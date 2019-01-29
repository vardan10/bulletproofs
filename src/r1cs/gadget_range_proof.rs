use crate::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable};
use curve25519_dalek::scalar::Scalar;
use crate::r1cs::value::AllocatedQuantity;


struct PositiveNo(R1CSProof);

impl PositiveNo {
    fn gadget<CS: ConstraintSystem>(
        cs: &mut CS,
        v: AllocatedQuantity,
        n: usize,
    ) -> Result<(), R1CSError> {
        let mut constraint = vec![(v.variable, -Scalar::one())];
        let mut exp_2 = Scalar::one();
        for i in 0..n {
            // Create low-level variables and add them to constraints
            let (a, b, o) = cs.allocate(|| {
                let q: u64 = v.assignment.ok_or(R1CSError::MissingAssignment)?;
                //println!("q is {}", &q);
                let bit: u64 = (q >> i) & 1;
                Ok(((1 - bit).into(), bit.into(), Scalar::zero()))
            })?;

            // Enforce a * b = 0, so one of (a,b) is zero
            cs.constrain(o.into());

            // Enforce that a = 1 - b, so they both are 1 or 0.
            cs.constrain(a + (b - 1u64));

            constraint.push((b, exp_2)  );
            exp_2 = exp_2 + exp_2;
        }

        // Enforce that -v + Sum(b_i * 2^i, i = 0..n-1) = 0 => Sum(b_i * 2^i, i = 0..n-1) = v
        cs.constrain(constraint.iter().collect());

        Ok(())
    }
}

/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn fil_cs<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity,
    n: usize,
) -> Result<(), R1CSError> {
    let mut constraint = vec![(v.variable, -Scalar::one())];
    let mut exp_2 = Scalar::one();
    for i in 0..n {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs.allocate(|| {
            let q: u64 = v.assignment.ok_or(R1CSError::MissingAssignment)?;
            //println!("q is {}", &q);
            let bit: u64 = (q >> i) & 1;
            Ok(((1 - bit).into(), bit.into(), Scalar::zero()))
        })?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + (b - 1u64));

        constraint.push((b, exp_2)  );
        exp_2 = exp_2 + exp_2;
    }

    // Enforce that v = Sum(b_i * 2^i, i = 0..n-1)
    cs.constrain(constraint.iter().collect());

    Ok(())
}

// v and c should be equal
pub fn equality_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity,
    c: u64,
) -> Result<(), R1CSError> {
    let (a, b, o) = cs.allocate(|| {
        let x: u64 = v.assignment.ok_or(R1CSError::MissingAssignment)?;
        Ok(((x-c).into(), Scalar::one(), Scalar::zero()))
    })?;

    cs.constrain(o.into());
    cs.constrain(a.into());

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use r1cs::{Prover, Verifier};
    use ::{BulletproofGens, PedersenGens};
    use merlin::Transcript;


    #[test]
    fn bound_check_gadget() {
        use rand::rngs::OsRng;
        use rand::Rng;

        let mut rng = OsRng::new().unwrap();
        let min = 10;
        let max = 100;

        let v = rng.gen_range(min, max);
        println!("v is {}", &v);
        assert!(bound_check_helper(v, min, max).is_ok());
        println!("Bound check successful for value in bound");
        //assert!(bound_check_helper(max + 1, min, max).is_err());
    }

    fn bound_check_helper(v: u64, min: u64, max: u64) -> Result<(), R1CSError> {
        // Common
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        // TODO: Use correct bit size of the field
        let n = 32;

        let a = v - min;
        let b = max - v;
        println!("a, b are {} {}", &a, &b);

        // Prover's scope
        let (proof, commitments) = {
            let mut comms = vec![];

            // Prover makes a `ConstraintSystem` instance representing a range proof gadget
            let mut prover_transcript = Transcript::new(b"BoundsTest");
            let mut rng = rand::thread_rng();

            let mut prover = Prover::new(&bp_gens, &pc_gens, &mut prover_transcript);

            // Constrain a in [0, 2^n-1]
            let (com_a, var_a) = prover.commit(a.into(), Scalar::random(&mut rng));
            let quantity_a = AllocatedQuantity {
                variable: var_a,
                assignment: Some(a),
            };
            assert!(fil_cs(&mut prover, quantity_a, n).is_ok());
            comms.push(com_a);

            // Constrain b in [0, 2^n-1]
            let (com_b, var_b) = prover.commit(b.into(), Scalar::random(&mut rng));
            let quantity_b = AllocatedQuantity {
                variable: var_b,
                assignment: Some(b),
            };
            assert!(fil_cs(&mut prover, quantity_b, n).is_ok());
            comms.push(com_b);

            // Constrain a+b to be same as max-min. This ensures same v is used in both commitments (`com_a` and `com_b`)
            let (com_ab, var_ab) = prover.commit((a+b).into(), Scalar::random(&mut rng));
            let quantity_ab = AllocatedQuantity {
                variable: var_ab,
                assignment: Some(a+b),
            };
            assert!(equality_gadget(&mut prover, quantity_ab, max-min).is_ok());
            comms.push(com_ab);

            println!("For {} in ({}, {}), no of constraints is {}", v, min, max, &prover.num_constraints());
//            println!("Prover commitments {:?}", &comms);
            let proof = prover.prove()?;

            (proof, comms)
        };

        println!("Proving done");

        // Verifier makes a `ConstraintSystem` instance representing a merge gadget
        let mut verifier_transcript = Transcript::new(b"BoundsTest");
        let mut verifier = Verifier::new(&bp_gens, &pc_gens, &mut verifier_transcript);

//        println!("Verifier commitments {:?}", &commitments);

        let var_a = verifier.commit(commitments[0]);
        let quantity_a = AllocatedQuantity {
            variable: var_a,
            assignment: None,
        };
        assert!(fil_cs(&mut verifier, quantity_a, n).is_ok());

        let var_b = verifier.commit(commitments[1]);
        let quantity_b = AllocatedQuantity {
            variable: var_b,
            assignment: None,
        };
        assert!(fil_cs(&mut verifier, quantity_b, n).is_ok());

        let var_ab = verifier.commit(commitments[2]);
        let quantity_ab = AllocatedQuantity {
            variable: var_ab,
            assignment: None,
        };
        assert!(equality_gadget(&mut verifier, quantity_ab, max-min).is_ok());


        // Verifier verifies proof
        Ok(verifier.verify(&proof)?)
    }

    #[test]
    fn range_proof_gadget() {
        use rand::rngs::OsRng;
        use rand::Rng;

        let mut rng = OsRng::new().unwrap();
        let m = 3; // number of values to test per `n`

        for n in [2, 10, 32, 63].iter() {
            let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
            let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min, max)).collect();
            for v in values {
                assert!(range_proof_helper(v, *n).is_ok());
            }
            assert!(range_proof_helper(max + 1, *n).is_err());
        }
    }

    fn range_proof_helper(v_val: u64, n: usize) -> Result<(), R1CSError> {
        // Common
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        // Prover's scope
        let (proof, commitment) = {
            // Prover makes a `ConstraintSystem` instance representing a range proof gadget
            let mut prover_transcript = Transcript::new(b"RangeProofTest");
            let mut rng = rand::thread_rng();

            let mut prover = Prover::new(&bp_gens, &pc_gens, &mut prover_transcript);

            let (com, var) = prover.commit(v_val.into(), Scalar::random(&mut rng));
            let quantity = AllocatedQuantity {
                variable: var,
                assignment: Some(v_val),
            };
            assert!(fil_cs(&mut prover, quantity, n).is_ok());

            println!("For {}, no of constraints is {}", v_val, &prover.num_constraints());
            let proof = prover.prove()?;

            (proof, com)
        };

        // Verifier makes a `ConstraintSystem` instance representing a merge gadget
        let mut verifier_transcript = Transcript::new(b"RangeProofTest");
        let mut verifier = Verifier::new(&bp_gens, &pc_gens, &mut verifier_transcript);

        let var = verifier.commit(commitment);
        let quantity = AllocatedQuantity {
            variable: var,
            assignment: None,
        };

        // Verifier adds constraints to the constraint system
        assert!(fil_cs(&mut verifier, quantity, n).is_ok());

        // Verifier verifies proof
        Ok(verifier.verify(&proof)?)
    }
}