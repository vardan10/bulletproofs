use crate::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use curve25519_dalek::scalar::Scalar;
use crate::r1cs::value::AllocatedQuantity;
use ::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use curve25519_dalek::ristretto::CompressedRistretto;
use r1cs::LinearCombination;


// Ensure `v` is a bit, hence 0 or 1
pub fn bit_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity
) -> Result<(), R1CSError> {
    let (a, b, o) = cs.allocate(|| {
        let bit: u64 = v.assignment.ok_or(R1CSError::MissingAssignment)?;
        Ok(((1 - bit).into(), bit.into(), Scalar::zero()))
    })?;

    // Variable b is same as v so b +
    let neg_v = LinearCombination {terms: vec![(v.variable, -Scalar::one())]};
    cs.constrain(b + neg_v);

    // Enforce a * b = 0, so one of (a,b) is zero
    cs.constrain(o.into());

    // Enforce that a = 1 - b, so they both are 1 or 0.
    cs.constrain(a + (b - 1u64));

    Ok(())
}

// Ensure sum of items of `vector` is `sum`
pub fn vector_sum_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    vector: &[AllocatedQuantity],
    sum: u64
) -> Result<(), R1CSError> {
    let mut vector_running_sum_vars: Vec<Variable> = vec![];
    let mut vector_running_sum_vals: Vec<u64> = vec![];

    for i in 0..vector.len() {
        let (a, b, o) = cs.allocate(|| {
            let bit: u64 = vector[i].assignment.ok_or(R1CSError::MissingAssignment)?;
            if i == 0 {
                vector_running_sum_vals.push(bit);
                Ok((bit.into(), Scalar::one(), bit.into()))
            } else {
                let r = vector_running_sum_vals[i-1] + bit;
                vector_running_sum_vals.push(r);
                Ok((r.into(), Scalar::one(), r.into()))
            }
        })?;

        vector_running_sum_vars.push(o);

        // Left wire should have appropriate value
        if i == 0 {
            cs.constrain(a - vector[i].variable);
        } else {
            cs.constrain(a - (vector_running_sum_vars[i-1] + vector[i].variable));
        }

        // output wire is same as left input wire
        cs.constrain(o - a);

        // right input wire is 1
        cs.constrain(b - Scalar::one());

        // last output wire should be equal to sum
        if i == (vector.len()-1) {
            let sum_var = LinearCombination {terms: vec![(Variable::One(), sum.into())]};
            cs.constrain(o - sum_var);
        }
    }
    Ok(())
}

// TODO: Find better name
pub fn vector_product_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    items: &[u64],
    vector: &[AllocatedQuantity],
    value: &AllocatedQuantity
) -> Result<(), R1CSError> {
    for i in 0..items.len() {

        let (a, b, o) = cs.allocate(|| {
            let bit: u64 = vector[i].assignment.ok_or(R1CSError::MissingAssignment)?;
            let val = value.assignment.ok_or(R1CSError::MissingAssignment)?;
            Ok((items[i].into(), bit.into(), (bit*val).into()))
        })?;

        let item_var = LinearCombination {terms: vec![(Variable::One(), items[i].into())]};
        cs.constrain(a - item_var);

        cs.constrain(o - (a+b));
    }

    Ok(())
}


#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;

    #[test]
    fn set_membership_check_gadget() {
        let set: Vec<u64> = vec![2, 3, 5, 6, 8, 20, 25];
        let value = 3u64;

        assert!(set_membership_check_helper(value, set).is_ok());
    }

    fn set_membership_check_helper(value: u64, set: Vec<u64>) -> Result<(), R1CSError> {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let set_length = set.len();

        let (proof, commitments) = {
            // Set all indices to 0 except the one where `value` is
            let bit_map: Vec<u64> = set.iter().map( | elem | {
                if *elem == value { 1 } else { 0 }
            }).collect();

            let mut comms = vec![];

            let mut prover_transcript = Transcript::new(b"SetMemebershipTest");
            let mut rng = rand::thread_rng();

            let mut prover = Prover::new(&bp_gens, &pc_gens, &mut prover_transcript);

            let mut bit_vars = vec![];
            for b in bit_map {
                let (com, var) = prover.commit(b.into(), Scalar::random(&mut rng));
                let quantity = AllocatedQuantity {
                    variable: var,
                    assignment: Some(b),
                };
                assert!(bit_gadget(&mut prover, quantity).is_ok());
                comms.push(com);
                bit_vars.push(quantity);
            }

            // The bit vector sum should be 1
            /*let (com_sum, var_sum) = prover.commit(Scalar::one(), Scalar::random(&mut rng));
            let quantity_sum = AllocatedQuantity {
                variable: var_sum,
                assignment: Some(1),
            };*/
            assert!(vector_sum_gadget(&mut prover, &bit_vars, 1).is_ok());
            //comms.push(com_sum);

            let (com_value, var_value) = prover.commit(value.into(), Scalar::random(&mut rng));
            let quantity_value = AllocatedQuantity {
                variable: var_value,
                assignment: Some(value),
            };
            assert!(vector_product_gadget(&mut prover, &set, &bit_vars, &quantity_value).is_ok());
            comms.push(com_value);

            println!("For set size {}, no of constraints is {}", &set_length, &prover.num_constraints());
//            println!("Prover commitments {:?}", &comms);
            let proof = prover.prove()?;

            (proof, comms)
        };

        let mut verifier_transcript = Transcript::new(b"SetMemebershipTest");
        let mut verifier = Verifier::new(&bp_gens, &pc_gens, &mut verifier_transcript);
        let mut bit_vars = vec![];

        for i in 0..set_length {
            let var = verifier.commit(commitments[i]);
            let quantity = AllocatedQuantity {
                variable: var,
                assignment: None,
            };
            assert!(bit_gadget(&mut verifier, quantity).is_ok());
            bit_vars.push(quantity);
        }

        /*let var_sum = verifier.commit(commitments[set_length]);
        let quantity_sum = AllocatedQuantity {
            variable: var_sum,
            assignment: None,
        };*/
        assert!(vector_sum_gadget(&mut verifier, &bit_vars, 1).is_ok());

        let var_val = verifier.commit(commitments[set_length]);
        let quantity_value = AllocatedQuantity {
            variable: var_val,
            assignment: None,
        };

        assert!(vector_product_gadget(&mut verifier, &set, &bit_vars, &quantity_value).is_ok());

        Ok(verifier.verify(&proof)?)
    }
}

