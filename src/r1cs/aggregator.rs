use merlin::Transcript;
use ::{BulletproofGens, PedersenGens};
use r1cs::{R1CSError, R1CSProof};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::traits::Identity;
use transcript::TranscriptProtocol;
use curve25519_dalek::scalar::Scalar;
use r1cs::aggr_prover::ProofShare;

use std::iter;
use util;
use inner_product_proof::InnerProductProof;
use std::ops::AddAssign;
use std::process::exit;
use util::scalar_exp_vartime;


/*
let pc_gens = PedersenGens::default();
// one extra set of generators is used by aggregator in case of padding
let bp_gens = BulletproofGens::new(...., <num of provers> + 1);

let mut aggregator = Aggregator::new(&bp_gens, &pc_gens, b"some aggregation");

// Create all provers. Each prover can be made to run over a separate constraint system
let mut prover_1 = AggrProver::new(&pc_gens);
let mut prover_2 = AggrProver::new(&pc_gens);
....
let mut prover_n = AggrProver::new(&pc_gens);

// First prover commits to his high level variables and specifies all its constraints
let (com1, var) = prover_1.commit(hidden_value, Scalar::random(&mut rng));
    .......      prover_1.commit(.........
    ..............
prover_1.constrain(............)
prover_1.constrain(..........)

// Commits to low level variables
let com_ll_1 = prover_1.commit_low_level_vars(&bp_gens.share(0));

// Now second prover commits to his high level variables, specifies all its constraints and commits to its low level variables like 1st prover
let (com2, var) = prover_2.commit(hidden_value, Scalar::random(&mut rng));
............
prover_2.constrain(.......)
let com_ll_2 = prover_2.commit_low_level_vars(&bp_gens.share(0));

// Similarly all provers follow the above procedure

// Combine all provers' commitments to high level and low level variables
let V = vec![com1, com2, .......];  // high level vars

let I = vec![
    com_ll_1.0,
    com_ll_2.0,
    ......
];
let O = vec![
    com_ll_1.1,
    com_ll_2.1,
    .....
];
let S = vec![
    com_ll_1.2,
    com_ll_2.2,
    ......
];

// Send these commitments to the aggregator to get the challenges
let (y, z) = aggregator.process_var_commitments(V, I, O, S);

// Each prover now commits to the polynomial. Since each prover uses different powers of y and z, they need to be told what is the offset
let mut y_offset = 0;
let mut z_offset = 1;

prover_1.commit_to_polynomial(&y, y_offset, &z, z_offset);
y_offset += prover_1.num_multipliers();
z_offset += prover_1.num_constraints();

prover_2.commit_to_polynomial(&y, y_offset, &z, z_offset);
y_offset += prover_2.num_multipliers();
z_offset += prover_2.num_constraints();

...........
.....

prover_n.commit_to_polynomial(.........)

// The aggregator now processes the polynomial commitments to return another tuple of challenges, u and x

let (u, x) = aggregator.process_poly_commitment(vec![
        &prover_1.T,
        &prover_2.T,
        .....
]);

// Each prover now evaluates the polynomial and outputs its contribution in the proof
let ps1 = prover_1.compute_poly(&x, &u, &y);
let ps2 = prover_2.compute_poly(&x, &u, &y);
.......
let psn = prover_n.compute_poly(&x, &u, &y);

// Aggregator combines these contributions to create a proof
let proof = aggregator.assemble_shares(vec![
    &ps1,
    &ps2,
    &ps3,
    &ps4,
]).unwrap();


// Verifier now processes each provers commitments in the same sequence as they were originally created. Also the constraints are created in the same order
let mut verifier_transcript = Transcript::new(b"basic aggregation");
let mut verifier = AggrVerifier::new(4, &mut verifier_transcript);

// Process first prover's commitments
let var_p1 = verifier.commit(com1);
.....
// Specify first prover's constraints
verifier.constrain(.....);
verifier.constrain(.....);
.........

// Mark ending of processing for first prover
verifier.processed_sub_proof();

// Process second prover's commitments and create its constrain
let var_p2 = verifier.commit(com2);
.....
verifier.constrain(.....);
verifier.constrain(.....);
.........

// Mark ending of processing for second prover
verifier.processed_sub_proof();

// Process for all provers
.....

// Verify proof
assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
*/

pub struct Aggregator<'a> {
    bp_gens: &'a BulletproofGens,
    pc_gens: &'a PedersenGens,
    pub transcript: Transcript,
    pub A_I1: CompressedRistretto,
    pub A_O1: CompressedRistretto,
    pub S1: CompressedRistretto,
    pub T_1: CompressedRistretto,
    pub T_3: CompressedRistretto,
    pub T_4: CompressedRistretto,
    pub T_5: CompressedRistretto,
    pub T_6: CompressedRistretto,
    pub x: Scalar,
    pub y: Scalar,
    pub z: Scalar,
    pub u: Scalar,
}

impl<'a> Aggregator<'a> {
    pub fn new(
        bp_gens: &'a BulletproofGens,
        pc_gens: &'a PedersenGens,
        label: &'static [u8]
    ) -> Self {
        // better to inject transcript to make it composable
        let transcript = Transcript::new(label);
        Self {
            transcript,
            bp_gens,
            pc_gens,
            A_I1: CompressedRistretto::identity(),
            A_O1: CompressedRistretto::identity(),
            S1: CompressedRistretto::identity(),
            T_1: CompressedRistretto::identity(),
            T_3: CompressedRistretto::identity(),
            T_4: CompressedRistretto::identity(),
            T_5: CompressedRistretto::identity(),
            T_6: CompressedRistretto::identity(),
            x: Scalar::zero(),
            y: Scalar::zero(),
            z: Scalar::zero(),
            u: Scalar::zero(),
        }
    }


    pub fn process_var_commitments(&mut self, v: Vec<&CompressedRistretto>,
                                   A_I1: Vec<&RistrettoPoint>,
                                   A_O1: Vec<&RistrettoPoint>,
                                   S1: Vec<&RistrettoPoint>) -> (Scalar, Scalar) {
        for comm in v {
            self.transcript.commit_point(b"V", comm);
        }

        let A_I1: RistrettoPoint = A_I1.into_iter().map(|c| c).sum();
        let A_O1: RistrettoPoint = A_O1.into_iter().map(|c| c).sum();
        let S1: RistrettoPoint = S1.into_iter().map(|c| c).sum();

        self.A_I1 = A_I1.compress();
        self.A_O1 = A_O1.compress();
        self.S1 = S1.compress();
        self.transcript.commit_point(b"A_I1", &self.A_I1);
        self.transcript.commit_point(b"A_O1", &self.A_O1);
        self.transcript.commit_point(b"S1", &self.S1);

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        self.y = y;
        self.z = z;
        (y, z)
    }

    pub fn process_poly_commitment(&mut self, coeffs: Vec<&[RistrettoPoint]>) -> (Scalar, Scalar) {
        let mut T1 = RistrettoPoint::identity();
        let mut T3 = RistrettoPoint::identity();
        let mut T4 = RistrettoPoint::identity();
        let mut T5 = RistrettoPoint::identity();
        let mut T6 = RistrettoPoint::identity();

        for c in coeffs {
            T1.add_assign(&c[0]);
            T3.add_assign(&c[1]);
            T4.add_assign(&c[2]);
            T5.add_assign(&c[3]);
            T6.add_assign(&c[4]);
        }

        self.T_1 = T1.compress();
        self.T_3 = T3.compress();
        self.T_4 = T4.compress();
        self.T_5 = T5.compress();
        self.T_6 = T6.compress();

        self.transcript.commit_point(b"T_1", &self.T_1);
        self.transcript.commit_point(b"T_3", &self.T_3);
        self.transcript.commit_point(b"T_4", &self.T_4);
        self.transcript.commit_point(b"T_5", &self.T_5);
        self.transcript.commit_point(b"T_6", &self.T_6);

        let u = self.transcript.challenge_scalar(b"u");
        let x = self.transcript.challenge_scalar(b"x");

        self.u = u;
        self.x = x;

        (u, x)
    }

    pub fn assemble_shares(&mut self, proof_shares: Vec<&ProofShare>) -> Result<R1CSProof, R1CSError> {

        let t_x: Scalar = proof_shares.iter().map(|ps| ps.t_x).sum();
        let t_x_blinding: Scalar = proof_shares.iter().map(|ps| ps.t_x_blinding).sum();
        let e_blinding: Scalar = proof_shares.iter().map(|ps| ps.e_blinding).sum();

        self.transcript.commit_scalar(b"t_x", &t_x);
        self.transcript
            .commit_scalar(b"t_x_blinding", &t_x_blinding);
        self.transcript.commit_scalar(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar(b"w");
        let Q = w * self.pc_gens.B;

        let mut l_vec: Vec<Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.l_vec.clone().into_iter())
            .collect();
        let mut r_vec: Vec<Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.r_vec.clone().into_iter())
            .collect();

        let n = l_vec.len();
        let padded_n = n.next_power_of_two();
        let pad = padded_n - n;

        l_vec.append(&mut vec![Scalar::zero(); pad]);
        let mut exp_y = scalar_exp_vartime(&self.y, n.clone() as u64);
        for i in n..padded_n {
            r_vec.push(-exp_y);
            exp_y = exp_y * self.y; // y^i -> y^(i+1)
        }

        let exp_y_inv = util::exp_iter(self.y.invert()).take(padded_n).collect::<Vec<_>>();

        // Create G_factors, H_factors, G_vec, H_vec
        let mut G_factors = Vec::<Scalar>::new();
        let mut H_factors = Vec::<Scalar>::new();
        let mut G_vec = Vec::<RistrettoPoint>::new();
        let mut H_vec = Vec::<RistrettoPoint>::new();

        let mut num_processed_vars = 0;

        for (i, share) in proof_shares.iter().enumerate() {
            let mut g = Vec::<Scalar>::new();
            g.append(&mut vec![Scalar::one(); share.n1]);
            g.append(&mut vec![self.u; share.n2]);
            let mut h = exp_y_inv.iter().skip(num_processed_vars).take(g.len())
                .zip(g.iter())
                .map(|(y, u_or_1)| y * u_or_1)
                .collect::<Vec<_>>();
            G_factors.append(&mut g);
            H_factors.append(&mut h);
            let gens = self.bp_gens.share(i);
            let mut gv: Vec<RistrettoPoint> = gens.G(share.n1 + share.n2).cloned().collect();
            let mut hv: Vec<RistrettoPoint> = gens.H(share.n1 + share.n2).cloned().collect();
            G_vec.append(&mut gv);
            H_vec.append(&mut hv);

            num_processed_vars += share.n1 + share.n2;
        }

        assert_eq!(n, num_processed_vars);

        G_factors.append(&mut vec![self.u; pad]);
        H_factors.append(&mut exp_y_inv.iter().skip(n).take(pad)
            .zip(G_factors.iter().skip(n).take(pad))
            .map(|(y, u_or_1)| y * u_or_1)
            .collect::<Vec<_>>()
        );

        let gens = self.bp_gens.share(proof_shares.len());
        G_vec.append(&mut gens.G(pad).cloned().collect());
        H_vec.append(&mut gens.H(pad).cloned().collect());
        let ipp_proof = InnerProductProof::create(
            &mut self.transcript,
            &Q,
            &G_factors,
            &H_factors,
            G_vec,
            H_vec,
            l_vec,
            r_vec,
        );

        Ok(R1CSProof {
            A_I1: self.A_I1,
            A_O1: self.A_O1,
            S1: self.S1,
            A_I2: CompressedRistretto::identity(),
            A_O2: CompressedRistretto::identity(),
            S2: CompressedRistretto::identity(),
            T_1: self.T_1,
            T_3: self.T_3,
            T_4: self.T_4,
            T_5: self.T_5,
            T_6: self.T_6,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1cs::aggr_prover::AggrProver;
    use crate::r1cs::ConstraintSystem;
    use r1cs::{LinearCombination, Variable};
    use r1cs::aggr_verifier::AggrVerifier;

    #[test]
    fn test_basic_aggr() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 5);

        let mut aggregator = Aggregator::new(&bp_gens, &pc_gens, b"basic aggregation");

        let (p1, q1, r1) = (3u64, 5u64, 15u64);
        let (p2, q2, r2) = (7u64, 11u64, 77u64);
        let (p3, q3, r3) = (2u64, 13u64, 26u64);
        let (p4, q4, r4) = (19u64, 2u64, 38u64);

        let mut prover_1 = AggrProver::new(&pc_gens);
        let mut prover_2 = AggrProver::new(&pc_gens);
        let mut prover_3 = AggrProver::new(&pc_gens);
        let mut prover_4 = AggrProver::new(&pc_gens);

        let mut rng = rand::thread_rng();

        let (com_p1, var_p1) = prover_1.commit(p1.into(), Scalar::random(&mut rng));
        let (com_q1, var_q1) = prover_1.commit(q1.into(), Scalar::random(&mut rng));
        let (_, _, o1) =  prover_1.multiply(var_p1.into(), var_q1.into());
        let lc1: LinearCombination = vec![(Variable::One(), r1.into())].iter().collect();
        prover_1.constrain(o1 -  lc1);
        let com_ll_1 = prover_1.commit_low_level_vars(&bp_gens.share(0));

        let (com_p2, var_p2) = prover_2.commit(p2.into(), Scalar::random(&mut rng));
        let (com_q2, var_q2) = prover_2.commit(q2.into(), Scalar::random(&mut rng));
        let (_, _, o2) =  prover_2.multiply(var_p2.into(), var_q2.into());
        let lc2: LinearCombination = vec![(Variable::One(), r2.into())].iter().collect();
        prover_2.constrain(o2 -  lc2);
        let com_ll_2  = prover_2.commit_low_level_vars(&bp_gens.share(1));

        let (com_p3, var_p3) = prover_3.commit(p3.into(), Scalar::random(&mut rng));
        let (com_q3, var_q3) = prover_3.commit(q3.into(), Scalar::random(&mut rng));
        let (_, _, o3) =  prover_3.multiply(var_p3.into(), var_q3.into());
        let lc3: LinearCombination = vec![(Variable::One(), r3.into())].iter().collect();
        prover_3.constrain(o3 -  lc3);
        let com_ll_3 = prover_3.commit_low_level_vars(&bp_gens.share(2));

        let (com_p4, var_p4) = prover_4.commit(p4.into(), Scalar::random(&mut rng));
        let (com_q4, var_q4) = prover_4.commit(q4.into(), Scalar::random(&mut rng));
        let (_, _, o4) =  prover_4.multiply(var_p4.into(), var_q4.into());
        let lc4: LinearCombination = vec![(Variable::One(), r4.into())].iter().collect();
        prover_4.constrain(o4 -  lc4);
        let com_ll_4 = prover_4.commit_low_level_vars(&bp_gens.share(3));

        let V = vec![&com_p1, &com_q1,
                     &com_p2, &com_q2,
                     &com_p3, &com_q3,
                     &com_p4, &com_q4,
        ];
        let I = vec![
            com_ll_1.0,
            com_ll_2.0,
            com_ll_3.0,
            com_ll_4.0,
        ];
        let O = vec![
            com_ll_1.1,
            com_ll_2.1,
            com_ll_3.1,
            com_ll_4.1,
        ];
        let S = vec![
            com_ll_1.2,
            com_ll_2.2,
            com_ll_3.2,
            com_ll_4.2,
        ];
        let (y, z) = aggregator.process_var_commitments(V,
                                                        I,
                                                        O,
                                                        S);

        let mut y_offset = 0;
        let mut z_offset = 1;

        prover_1.commit_to_polynomial(&y, y_offset, &z, z_offset);
        y_offset += prover_1.num_multipliers();
        z_offset += prover_1.num_constraints();

        prover_2.commit_to_polynomial(&y, y_offset, &z, z_offset);
        y_offset += prover_2.num_multipliers();
        z_offset += prover_2.num_constraints();

        prover_3.commit_to_polynomial(&y, y_offset, &z, z_offset);
        y_offset += prover_3.num_multipliers();
        z_offset += prover_3.num_constraints();

        prover_4.commit_to_polynomial(&y, y_offset, &z, z_offset);

        let (u, x) = aggregator.process_poly_commitment(vec![
            &prover_1.T,
            &prover_2.T,
            &prover_3.T,
            &prover_4.T,
        ]);

        let ps1 = prover_1.compute_poly(&x, &u, &y);
        let ps2 = prover_2.compute_poly(&x, &u, &y);
        let ps3 = prover_3.compute_poly(&x, &u, &y);
        let ps4 = prover_4.compute_poly(&x, &u, &y);

        let proof = aggregator.assemble_shares(vec![
            &ps1,
            &ps2,
            &ps3,
            &ps4,
        ]).unwrap();

        let mut verifier_transcript = Transcript::new(b"basic aggregation");
        let mut verifier = AggrVerifier::new(4, &mut verifier_transcript);

        let var_p1 = verifier.commit(com_p1);
        let var_q1 = verifier.commit(com_q1);
        let (_, _, o1) =  verifier.multiply(var_p1.into(), var_q1.into());
        let lc1: LinearCombination = vec![(Variable::One(), r1.into())].iter().collect();
        verifier.constrain(o1 -  lc1);

        verifier.processed_sub_proof();

        let var_p2 = verifier.commit(com_p2);
        let var_q2 = verifier.commit(com_q2);
        let (_, _, o2) =  verifier.multiply(var_p2.into(), var_q2.into());
        let lc2: LinearCombination = vec![(Variable::One(), r2.into())].iter().collect();
        verifier.constrain(o2 -  lc2);

        verifier.processed_sub_proof();

        let var_p3 = verifier.commit(com_p3);
        let var_q3 = verifier.commit(com_q3);
        let (_, _, o3) =  verifier.multiply(var_p3.into(), var_q3.into());
        let lc3: LinearCombination = vec![(Variable::One(), r3.into())].iter().collect();
        verifier.constrain(o3 -  lc3);

        verifier.processed_sub_proof();

        let var_p4 = verifier.commit(com_p4);
        let var_q4 = verifier.commit(com_q4);
        let (_, _, o4) =  verifier.multiply(var_p4.into(), var_q4.into());
        let lc4: LinearCombination = vec![(Variable::One(), r4.into())].iter().collect();
        verifier.constrain(o4 -  lc4);

        verifier.processed_sub_proof();

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_basic_aggr_with_padding() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 4);

        let mut aggregator = Aggregator::new(&bp_gens, &pc_gens, b"basic aggregation");

        let (p1, q1, r1) = (3u64, 5u64, 15u64);
        let (p2, q2, r2) = (7u64, 11u64, 77u64);
        let (p3, q3, r3) = (2u64, 13u64, 26u64);

        let mut prover_1 = AggrProver::new(&pc_gens);
        let mut prover_2 = AggrProver::new(&pc_gens);
        let mut prover_3 = AggrProver::new(&pc_gens);

        let mut rng = rand::thread_rng();

        let (com_p1, var_p1) = prover_1.commit(p1.into(), Scalar::random(&mut rng));
        let (com_q1, var_q1) = prover_1.commit(q1.into(), Scalar::random(&mut rng));
        let (_, _, o1) =  prover_1.multiply(var_p1.into(), var_q1.into());
        let lc1: LinearCombination = vec![(Variable::One(), r1.into())].iter().collect();
        prover_1.constrain(o1 -  lc1);
        let com_ll_1 = prover_1.commit_low_level_vars(&bp_gens.share(0));

        let (com_p2, var_p2) = prover_2.commit(p2.into(), Scalar::random(&mut rng));
        let (com_q2, var_q2) = prover_2.commit(q2.into(), Scalar::random(&mut rng));
        let (_, _, o2) =  prover_2.multiply(var_p2.into(), var_q2.into());
        let lc2: LinearCombination = vec![(Variable::One(), r2.into())].iter().collect();
        prover_2.constrain(o2 -  lc2);
        let com_ll_2  = prover_2.commit_low_level_vars(&bp_gens.share(1));

        let (com_p3, var_p3) = prover_3.commit(p3.into(), Scalar::random(&mut rng));
        let (com_q3, var_q3) = prover_3.commit(q3.into(), Scalar::random(&mut rng));
        let (_, _, o3) =  prover_3.multiply(var_p3.into(), var_q3.into());
        let lc3: LinearCombination = vec![(Variable::One(), r3.into())].iter().collect();
        prover_3.constrain(o3 -  lc3);
        let com_ll_3 = prover_3.commit_low_level_vars(&bp_gens.share(2));

        let V = vec![&com_p1, &com_q1,
                     &com_p2, &com_q2,
                     &com_p3, &com_q3,
        ];
        let I = vec![
            com_ll_1.0,
            com_ll_2.0,
            com_ll_3.0,
        ];
        let O = vec![
            com_ll_1.1,
            com_ll_2.1,
            com_ll_3.1,
        ];
        let S = vec![
            com_ll_1.2,
            com_ll_2.2,
            com_ll_3.2,
        ];
        let (y, z) = aggregator.process_var_commitments(V,
                                                        I,
                                                        O,
                                                        S);

        let mut y_offset = 0;
        let mut z_offset = 1;

        prover_1.commit_to_polynomial(&y, y_offset, &z, z_offset);
        y_offset += prover_1.num_multipliers();
        z_offset += prover_1.num_constraints();

        prover_2.commit_to_polynomial(&y, y_offset, &z, z_offset);
        y_offset += prover_2.num_multipliers();
        z_offset += prover_2.num_constraints();

        prover_3.commit_to_polynomial(&y, y_offset, &z, z_offset);

        let (u, x) = aggregator.process_poly_commitment(vec![
            &prover_1.T,
            &prover_2.T,
            &prover_3.T,
        ]);

        let ps1 = prover_1.compute_poly(&x, &u, &y);
        let ps2 = prover_2.compute_poly(&x, &u, &y);
        let ps3 = prover_3.compute_poly(&x, &u, &y);

        let proof = aggregator.assemble_shares(vec![
            &ps1,
            &ps2,
            &ps3,
        ]).unwrap();

        let mut verifier_transcript = Transcript::new(b"basic aggregation");
        let mut verifier = AggrVerifier::new(3, &mut verifier_transcript);

        let var_p1 = verifier.commit(com_p1);
        let var_q1 = verifier.commit(com_q1);
        let (_, _, o1) =  verifier.multiply(var_p1.into(), var_q1.into());
        let lc1: LinearCombination = vec![(Variable::One(), r1.into())].iter().collect();
        verifier.constrain(o1 -  lc1);

        verifier.processed_sub_proof();

        let var_p2 = verifier.commit(com_p2);
        let var_q2 = verifier.commit(com_q2);
        let (_, _, o2) =  verifier.multiply(var_p2.into(), var_q2.into());
        let lc2: LinearCombination = vec![(Variable::One(), r2.into())].iter().collect();
        verifier.constrain(o2 -  lc2);

        verifier.processed_sub_proof();

        let var_p3 = verifier.commit(com_p3);
        let var_q3 = verifier.commit(com_q3);
        let (_, _, o3) =  verifier.multiply(var_p3.into(), var_q3.into());
        let lc3: LinearCombination = vec![(Variable::One(), r3.into())].iter().collect();
        verifier.constrain(o3 -  lc3);

        verifier.processed_sub_proof();

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_basic_aggr_1() {
        let (p1, q1, r1, s1) = (5u64, 7u64, 3u64, 105u64);
        let (p2, q2, r2, s2) = (2u64, 5u64, 3u64, 30u64);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 3);

        let mut aggregator = Aggregator::new(&bp_gens, &pc_gens, b"basic aggregation 1");

        let mut prover_1 = AggrProver::new(&pc_gens);
        let mut prover_2 = AggrProver::new(&pc_gens);

        let mut rng = rand::thread_rng();

        let (com_p1, var_p1) = prover_1.commit(p1.into(), Scalar::random(&mut rng));
        let (com_q1, var_q1) = prover_1.commit(q1.into(), Scalar::random(&mut rng));
        let (com_r1, var_r1) = prover_1.commit(r1.into(), Scalar::random(&mut rng));

        let (_, _, o1) =  prover_1.multiply(var_p1.into(), var_q1.into());
        let (_, _, o2) =  prover_1.multiply(o1.into(), var_r1.into());
        let lc1: LinearCombination = vec![(Variable::One(), s1.into())].iter().collect();
        prover_1.constrain(o2 -  lc1);
        let com_ll_1 = prover_1.commit_low_level_vars(&bp_gens.share(0));

        let (com_p2, var_p2) = prover_2.commit(p2.into(), Scalar::random(&mut rng));
        let (com_q2, var_q2) = prover_2.commit(q2.into(), Scalar::random(&mut rng));
        let (com_r2, var_r2) = prover_2.commit(r2.into(), Scalar::random(&mut rng));

        let (_, _, o3) =  prover_2.multiply(var_p2.into(), var_q2.into());
        let (_, _, o4) =  prover_2.multiply(o3.into(), var_r2.into());
        let lc2: LinearCombination = vec![(Variable::One(), s2.into())].iter().collect();
        prover_2.constrain(o4 -  lc2);
        let com_ll_2  = prover_2.commit_low_level_vars(&bp_gens.share(1));

        let V = vec![&com_p1, &com_q1, &com_r1,
                    &com_p2, &com_q2, &com_r2,
        ];
        let I = vec![com_ll_1.0,
                     com_ll_2.0,
        ];
        let O = vec![com_ll_1.1,
                     com_ll_2.1,
        ];
        let S = vec![com_ll_1.2,
                     com_ll_2.2,
        ];
        let (y, z) = aggregator.process_var_commitments(V,
                                                        I,
                                                        O,
                                                        S);

        let mut y_offset = 0;
        let mut z_offset = 1;

        prover_1.commit_to_polynomial(&y, y_offset, &z, z_offset);
        y_offset += prover_1.num_multipliers();
        z_offset += prover_1.num_constraints();

        prover_2.commit_to_polynomial(&y, y_offset, &z, z_offset);

        let (u, x) = aggregator.process_poly_commitment(vec![&prover_1.T,
                                                             &prover_2.T]);

        let ps1 = prover_1.compute_poly(&x, &u, &y);
        let ps2 = prover_2.compute_poly(&x, &u, &y);

        let proof = aggregator.assemble_shares(vec![&ps1, &ps2]).unwrap();

        let mut verifier_transcript = Transcript::new(b"basic aggregation 1");
        let mut verifier = AggrVerifier::new(2, &mut verifier_transcript);

        let var_p1 = verifier.commit(com_p1);
        let var_q1 = verifier.commit(com_q1);
        let var_r1 = verifier.commit(com_r1);
        let (_, _, o1) =  verifier.multiply(var_p1.into(), var_q1.into());
        let (_, _, o2) =  verifier.multiply(o1.into(), var_r1.into());
        let lc1: LinearCombination = vec![(Variable::One(), s1.into())].iter().collect();
        verifier.constrain(o2 -  lc1);

        verifier.processed_sub_proof();

        let var_p2 = verifier.commit(com_p2);
        let var_q2 = verifier.commit(com_q2);
        let var_r2 = verifier.commit(com_r2);
        let (_, _, o3) =  verifier.multiply(var_p2.into(), var_q2.into());
        let (_, _, o4) =  verifier.multiply(o3.into(), var_r2.into());
        let lc2: LinearCombination = vec![(Variable::One(), s2.into())].iter().collect();
        verifier.constrain(o4 -  lc2);

        verifier.processed_sub_proof();

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_basic_aggr_1_with_padding() {
        let (p1, q1, r1, s1) = (5u64, 7u64, 3u64, 105u64);
        let (p2, q2, r2, s2) = (2u64, 5u64, 3u64, 30u64);
        let (p3, q3, r3, s3) = (7u64, 11u64, 13u64, 1001u64);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 4);

        let mut aggregator = Aggregator::new(&bp_gens, &pc_gens, b"basic aggregation 1");

        let mut prover_1 = AggrProver::new(&pc_gens);
        let mut prover_2 = AggrProver::new(&pc_gens);
        let mut prover_3 = AggrProver::new(&pc_gens);

        let mut rng = rand::thread_rng();

        let (com_p1, var_p1) = prover_1.commit(p1.into(), Scalar::random(&mut rng));
        let (com_q1, var_q1) = prover_1.commit(q1.into(), Scalar::random(&mut rng));
        let (com_r1, var_r1) = prover_1.commit(r1.into(), Scalar::random(&mut rng));

        let (_, _, o1) =  prover_1.multiply(var_p1.into(), var_q1.into());
        let (_, _, o2) =  prover_1.multiply(o1.into(), var_r1.into());
        let lc1: LinearCombination = vec![(Variable::One(), s1.into())].iter().collect();
        prover_1.constrain(o2 -  lc1);
        let com_ll_1 = prover_1.commit_low_level_vars(&bp_gens.share(0));

        let (com_p2, var_p2) = prover_2.commit(p2.into(), Scalar::random(&mut rng));
        let (com_q2, var_q2) = prover_2.commit(q2.into(), Scalar::random(&mut rng));
        let (com_r2, var_r2) = prover_2.commit(r2.into(), Scalar::random(&mut rng));

        let (_, _, o3) =  prover_2.multiply(var_p2.into(), var_q2.into());
        let (_, _, o4) =  prover_2.multiply(o3.into(), var_r2.into());
        let lc2: LinearCombination = vec![(Variable::One(), s2.into())].iter().collect();
        prover_2.constrain(o4 -  lc2);
        let com_ll_2  = prover_2.commit_low_level_vars(&bp_gens.share(1));

        let (com_p3, var_p3) = prover_3.commit(p3.into(), Scalar::random(&mut rng));
        let (com_q3, var_q3) = prover_3.commit(q3.into(), Scalar::random(&mut rng));
        let (com_r3, var_r3) = prover_3.commit(r3.into(), Scalar::random(&mut rng));

        let (_, _, o5) =  prover_3.multiply(var_p3.into(), var_q3.into());
        let (_, _, o6) =  prover_3.multiply(o5.into(), var_r3.into());
        let lc3: LinearCombination = vec![(Variable::One(), s3.into())].iter().collect();
        prover_3.constrain(o6 -  lc3);
        let com_ll_3  = prover_3.commit_low_level_vars(&bp_gens.share(2));

        let V = vec![
            &com_p1, &com_q1, &com_r1,
            &com_p2, &com_q2, &com_r2,
            &com_p3, &com_q3, &com_r3,
        ];
        let I = vec![
            com_ll_1.0,
            com_ll_2.0,
            com_ll_3.0,
        ];
        let O = vec![
            com_ll_1.1,
            com_ll_2.1,
            com_ll_3.1,
        ];
        let S = vec![
            com_ll_1.2,
            com_ll_2.2,
            com_ll_3.2,
        ];
        let (y, z) = aggregator.process_var_commitments(V,
                                                        I,
                                                        O,
                                                        S);

        let mut y_offset = 0;
        let mut z_offset = 1;

        prover_1.commit_to_polynomial(&y, y_offset, &z, z_offset);
        y_offset += prover_1.num_multipliers();
        z_offset += prover_1.num_constraints();

        prover_2.commit_to_polynomial(&y, y_offset, &z, z_offset);
        y_offset += prover_2.num_multipliers();
        z_offset += prover_2.num_constraints();

        prover_3.commit_to_polynomial(&y, y_offset, &z, z_offset);

        let (u, x) = aggregator.process_poly_commitment(vec![&prover_1.T, &prover_2.T, &prover_3.T]);

        let ps1 = prover_1.compute_poly(&x, &u, &y);
        let ps2 = prover_2.compute_poly(&x, &u, &y);
        let ps3 = prover_3.compute_poly(&x, &u, &y);

        let proof = aggregator.assemble_shares(vec![&ps1, &ps2, &ps3]).unwrap();

        let mut verifier_transcript = Transcript::new(b"basic aggregation 1");
        let mut verifier = AggrVerifier::new(3, &mut verifier_transcript);

        let var_p1 = verifier.commit(com_p1);
        let var_q1 = verifier.commit(com_q1);
        let var_r1 = verifier.commit(com_r1);
        let (_, _, o1) =  verifier.multiply(var_p1.into(), var_q1.into());
        let (_, _, o2) =  verifier.multiply(o1.into(), var_r1.into());
        let lc1: LinearCombination = vec![(Variable::One(), s1.into())].iter().collect();
        verifier.constrain(o2 -  lc1);

        verifier.processed_sub_proof();

        let var_p2 = verifier.commit(com_p2);
        let var_q2 = verifier.commit(com_q2);
        let var_r2 = verifier.commit(com_r2);
        let (_, _, o3) =  verifier.multiply(var_p2.into(), var_q2.into());
        let (_, _, o4) =  verifier.multiply(o3.into(), var_r2.into());
        let lc2: LinearCombination = vec![(Variable::One(), s2.into())].iter().collect();
        verifier.constrain(o4 -  lc2);

        verifier.processed_sub_proof();

        let var_p3 = verifier.commit(com_p3);
        let var_q3 = verifier.commit(com_q3);
        let var_r3 = verifier.commit(com_r3);
        let (_, _, o5) =  verifier.multiply(var_p3.into(), var_q3.into());
        let (_, _, o6) =  verifier.multiply(o3.into(), var_r3.into());
        let lc3: LinearCombination = vec![(Variable::One(), s3.into())].iter().collect();
        verifier.constrain(o6 -  lc3);

        verifier.processed_sub_proof();

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}