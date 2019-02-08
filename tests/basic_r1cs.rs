extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::r1cs::value::AllocatedQuantity;
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use curve25519_dalek::ristretto::CompressedRistretto;
use bulletproofs::r1cs::LinearCombination;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_factor_r1cs() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let (p, q, r) = (17u64, 19u64, 323u64);

        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"Factors");
            let mut prover = Prover::new(&bp_gens, &pc_gens, &mut prover_transcript);

            let mut rng = rand::thread_rng();

            let (com_p, var_p) = prover.commit(p.into(), Scalar::random(&mut rng));
            let (com_q, var_q) = prover.commit(q.into(), Scalar::random(&mut rng));

            let (a, b, o) = prover.allocate(|| {
                Ok((p.into(), q.into(), r.into()))
            }).unwrap();
            prover.constrain(var_p - a);
            prover.constrain(var_q - b);

            let proof = prover.prove().unwrap();

            (proof, (com_p, com_q))
        };

        let mut verifier_transcript = Transcript::new(b"Factors");
        let mut verifier = Verifier::new(&bp_gens, &pc_gens, &mut verifier_transcript);
        let var_p = verifier.commit(commitments.0);
        let var_q = verifier.commit(commitments.1);

        let (a, b, o) = verifier.allocate(|| {
            Err(R1CSError::MissingAssignment)
        }).unwrap();

        verifier.constrain(var_p - a);
        verifier.constrain(var_q - b);

        assert!(verifier.verify(&proof).is_ok());
    }
}