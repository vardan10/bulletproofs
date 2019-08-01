extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Aggregator, AggrProver, AggrVerifier};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use bulletproofs::r1cs::LinearCombination;

mod utils;
use utils::AllocatedScalar;

pub fn set_membership_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: Variable,
    diff_vars: Vec<Variable>,
    set: &[u64]
) -> Result<(), R1CSError> {
    let set_length = set.len();
    // Accumulates product of elements in `diff_vars`
    let mut product: LinearCombination = Variable::One().into();

    for i in 0..set_length {
        // Take difference of value and each set element, `v - set[i]`
        let elem_lc: LinearCombination = vec![(Variable::One(), Scalar::from(set[i]))].iter().collect();
        let v_minus_elem = v - elem_lc;

        // Since `diff_vars[i]` is `set[i] - v`, `v - set[i]` + `diff_vars[i]` should be 0
        cs.constrain(diff_vars[i] + v_minus_elem);

        let (_, _, o) = cs.multiply(product.clone(), diff_vars[i].into());
        product = o.into();
    }

    // Ensure product of elements if `diff_vars` is 0
    cs.constrain(product);

    Ok(())
}

pub fn is_nonzero_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    x: Variable,
    x_inv: Variable,
) -> Result<(), R1CSError> {
    let x_lc = LinearCombination::from(x);
    let y_lc = LinearCombination::from(Scalar::one());
    let one_minus_y_lc = LinearCombination::from(Variable::One()) - y_lc.clone();

    // x * (1-y) = 0
    let (_, _, o1) = cs.multiply(x_lc.clone(), one_minus_y_lc);
    cs.constrain(o1.into());

    // x * x_inv = y
    let inv_lc: LinearCombination = vec![(x_inv, Scalar::one())].iter().collect();
    let (_, _, o2) = cs.multiply(x_lc.clone(), inv_lc.clone());
    // Output wire should have value `y`
    cs.constrain(o2 - y_lc);

    Ok(())
}

pub fn set_non_membership_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: Variable,
    diff_vars: Vec<Variable>,
    diff_inv_vars: Vec<Variable>,
    set: &[u64]
) -> Result<(), R1CSError> {
    let set_length = set.len();

    for i in 0..set_length {
        // Take difference of value and each set element, `v - set[i]`
        let elem_lc: LinearCombination = vec![(Variable::One(), Scalar::from(set[i]))].iter().collect();
        let v_minus_elem = v - elem_lc;

        // Since `diff_vars[i]` is `set[i] - v`, `v - set[i]` + `diff_vars[i]` should be 0
        cs.constrain(diff_vars[i] + v_minus_elem);

        // Ensure `set[i] - v` is non-zero
        is_nonzero_gadget(cs, diff_vars[i], diff_inv_vars[i])?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;

    use std::time::{Duration, Instant};

    fn aggregate_set_membership_non_membership_helper(set1: Vec<u64>, set2: Vec<u64>, present_value: u64, absent_value: u64) -> Result<(), R1CSError> {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 3);
        let label = b"aggregating set membership and non membership";
        let mut aggregator = Aggregator::new(&bp_gens, &pc_gens, label);

        let mut prover_1 = AggrProver::new(&pc_gens);
        let mut prover_2 = AggrProver::new(&pc_gens);
        let mut rng = rand::thread_rng();

        let mut comms: Vec<CompressedRistretto> = vec![];

        let start = Instant::now();
        {
            let mut diff_vars = vec![];
            let value = Scalar::from(present_value);
            let (com_value, var_value) = prover_1.commit(value, Scalar::random(&mut rng));
            comms.push(com_value);

            for i in 0..set1.len() {
                let elem = Scalar::from(set1[i]);
                let diff = elem - value;

                // Take difference of set element and value, `set[i] - value`
                let (com_diff, var_diff) = prover_1.commit(diff, Scalar::random(&mut rng));

                diff_vars.push(var_diff);
                comms.push(com_diff);
            }

            assert!(set_membership_gadget(&mut prover_1, var_value, diff_vars, &set1).is_ok());
        }

        {
            let mut diff_vars = vec![];
            let mut diff_inv_vars = vec![];
            let value= Scalar::from(absent_value);
            let (com_value, var_value) = prover_2.commit(value.clone(), Scalar::random(&mut rng));
            comms.push(com_value);

            for i in 0..set2.len() {
                let elem = Scalar::from(set2[i]);
                let diff = elem - value;
                let diff_inv = diff.invert();

                // Take difference of set element and value, `set[i] - value`
                let (com_diff, var_diff) = prover_2.commit(diff.clone(), Scalar::random(&mut rng));
                diff_vars.push(var_diff);
                comms.push(com_diff);

                // Inverse needed to prove that difference `set[i] - value` is non-zero
                let (com_diff_inv, var_diff_inv) = prover_2.commit(diff_inv.clone(), Scalar::random(&mut rng));
                diff_inv_vars.push(var_diff_inv);
                comms.push(com_diff_inv);
            }

            assert!(set_non_membership_gadget(&mut prover_2, var_value, diff_vars, diff_inv_vars, &set2).is_ok());
        }

        let com_ll_1 = prover_1.commit_low_level_vars(&bp_gens.share(0));
        let com_ll_2  = prover_2.commit_low_level_vars(&bp_gens.share(1));
        let I = vec![
            com_ll_1.0,
            com_ll_2.0,
        ];
        let O = vec![
            com_ll_1.1,
            com_ll_2.1,
        ];
        let S = vec![
            com_ll_1.2,
            com_ll_2.2,
        ];

        let (y, z) = aggregator.process_var_commitments(comms.iter().map(|c| c).collect::<Vec<&CompressedRistretto>>(),
                                                        I,
                                                        O,
                                                        S);

        let t1 = prover_1.commit_to_polynomial(&y, &z);
        let t2 = prover_2.commit_to_polynomial(&y, &z);

        let (u, x) = aggregator.process_poly_commitment(vec![
            t1,
            t2,
        ]);

        let ps1 = prover_1.compute_poly(&x, &u, &y);
        let ps2 = prover_2.compute_poly(&x, &u, &y);

        let proof = aggregator.assemble_shares(vec![
            &ps1,
            &ps2,
        ]).unwrap();

        println!("Proving time for aggregated proof of set membership (set length {}) and non membership (set length {}) is {:?}", &set1.len(), &set2.len(), start.elapsed());
        println!("Proof size is {}", proof.to_bytes().len());

        let start = Instant::now();
        let mut verifier_transcript = Transcript::new(label);
        let mut verifier = AggrVerifier::new(2, &mut verifier_transcript);

        {
            let mut diff_vars = vec![];

            let var_val = verifier.commit(comms[0]);
            for i in 1..set1.len()+1 {
                let var_diff = verifier.commit(comms[i]);
                diff_vars.push(var_diff);
            }

            assert!(set_membership_gadget(&mut verifier, var_val, diff_vars, &set1).is_ok());

            verifier.processed_sub_proof();
        }

        {
            let mut diff_vars = vec![];
            let mut diff_inv_vars = vec![];

            let var_val = verifier.commit(comms[set1.len()+1]);

            for i in 1..set2.len()+1 {
                let offset = set1.len() + 1;
                let var_diff = verifier.commit(comms[offset + 2*i-1]);
                diff_vars.push(var_diff);

                let var_diff_inv = verifier.commit(comms[offset + 2*i]);
                diff_inv_vars.push(var_diff_inv);
            }

            assert!(set_non_membership_gadget(&mut verifier, var_val, diff_vars, diff_inv_vars, &set2).is_ok());

            verifier.processed_sub_proof();
        }

        let r = Ok(verifier.verify(&proof, &pc_gens, &bp_gens)?);
        println!("Verification time for aggregated proof of set membership (set length {}) and non membership (set length {}) is {:?}", &set1.len(), &set2.len(), start.elapsed());
        r
    }

    #[test]
    fn aggregate_set_membership_non_membership() {
        let set1: Vec<u64> = vec![2, 3, 5, 6, 8, 20, 25, 35, 60];
        let set2: Vec<u64> = vec![5, 9, 32, 1, 85, 2, 7, 11, 14, 26];
        let present_value = 20u64;
        let absent_value = 19u64;

        assert!(aggregate_set_membership_non_membership_helper(set1, set2, present_value, absent_value).is_ok());
    }

}