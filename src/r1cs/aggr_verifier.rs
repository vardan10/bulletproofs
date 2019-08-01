#![allow(non_snake_case)]

use core::mem;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use super::{ConstraintSystem, LinearCombination, R1CSProof, RandomizedConstraintSystem, Variable};

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use transcript::TranscriptProtocol;
use util;
use std::iter;
use inner_product_proof::inner_product;

struct SubProof<'t> {
    constraints: Vec<LinearCombination>,
    num_vars: usize,
    V: Vec<CompressedRistretto>,
    deferred_constraints: Vec<Box<Fn(&mut RandomizingAggrVerifier<'t>) -> Result<(), R1CSError>>>,
    pending_multiplier: Option<usize>
}

pub struct AggrVerifier<'t> {
    transcript: &'t mut Transcript,
    sub_proofs: Vec<SubProof<'t>>,
    cur_proof_idx: usize
}

pub struct RandomizingAggrVerifier<'t> {
    verifier: AggrVerifier<'t>,
}

impl<'t> ConstraintSystem for AggrVerifier<'t> {
    type RandomizedCS = RandomizingAggrVerifier<'t>;

    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        let sub_proof = &mut self.sub_proofs[self.cur_proof_idx];
        let var = sub_proof.num_vars;
        sub_proof.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        // Constrain l,r,o:
        left.terms.push((l_var, -Scalar::one()));
        right.terms.push((r_var, -Scalar::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate(&mut self, _: Option<Scalar>) -> Result<Variable, R1CSError> {
        let sub_proof = &mut self.sub_proofs[self.cur_proof_idx];
        match sub_proof.pending_multiplier {
            None => {
                let i = sub_proof.num_vars;
                sub_proof.num_vars += 1;
                sub_proof.pending_multiplier = Some(i);
                Ok(Variable::MultiplierLeft(i))
            }
            Some(i) => {
                sub_proof.pending_multiplier = None;
                Ok(Variable::MultiplierRight(i))
            }
        }
    }

    fn allocate_multiplier(
        &mut self,
        _: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        let sub_proof = &mut self.sub_proofs[self.cur_proof_idx];
        let var = sub_proof.num_vars;
        sub_proof.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        Ok((l_var, r_var, o_var))
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination
        // evals to 0 for prover, etc).
        let sub_proof = &mut self.sub_proofs[self.cur_proof_idx];
        sub_proof.constraints.push(lc);
    }

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
        where
            F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        let sub_proof = &mut self.sub_proofs[self.cur_proof_idx];
        sub_proof.deferred_constraints.push(Box::new(callback));
        Ok(())
    }

    fn evaluate_lc(&self, _: &LinearCombination) -> Option<Scalar> {
        None
    }

    fn allocate_single(&mut self, _: Option<Scalar>) -> Result<(Variable, Option<Variable>), R1CSError> {
        let var = self.allocate(None)?;
        match var {
            Variable::MultiplierLeft(i) => Ok((Variable::MultiplierLeft(i), None)),
            Variable::MultiplierRight(i) => Ok((Variable::MultiplierRight(i), Some(Variable::MultiplierOutput(i)))),
            _ => Err(R1CSError::FormatError)
        }
    }
}

impl<'t> ConstraintSystem for RandomizingAggrVerifier<'t> {
    type RandomizedCS = Self;

    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        self.verifier.multiply(left, right)
    }

    fn allocate(&mut self, assignment: Option<Scalar>) -> Result<Variable, R1CSError> {
        self.verifier.allocate(assignment)
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        self.verifier.allocate_multiplier(input_assignments)
    }

    fn constrain(&mut self, lc: LinearCombination) {
        self.verifier.constrain(lc)
    }

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
        where
            F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        callback(self)
    }

    fn evaluate_lc(&self, _: &LinearCombination) -> Option<Scalar> {
        None
    }

    fn allocate_single(&mut self, _: Option<Scalar>) -> Result<(Variable, Option<Variable>), R1CSError> {
        self.verifier.allocate_single(None)
    }
}

impl<'t> RandomizedConstraintSystem for RandomizingAggrVerifier<'t> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.verifier.transcript.challenge_scalar(label)
    }
}

impl<'t> AggrVerifier<'t> {
    pub fn new(num_sub_proofs: usize, transcript: &'t mut Transcript) -> Self {
        //transcript.r1cs_domain_sep();

        let mut sub_proofs: Vec<SubProof> = vec![];
        for _ in 0..num_sub_proofs {
            sub_proofs.push( SubProof {
                constraints: Vec::<LinearCombination>::new(),
                num_vars: 0,
                V: Vec::<CompressedRistretto>::new(),
                deferred_constraints: Vec::<Box<Fn(&mut RandomizingAggrVerifier<'t>) -> Result<(), R1CSError>>>::new(),
                pending_multiplier: None
            });
        }

        AggrVerifier {
            transcript,
            sub_proofs,
            cur_proof_idx: 0
        }
    }

    pub fn processed_sub_proof(&mut self) {
        self.cur_proof_idx += 1;
    }

    pub fn commit(&mut self, commitment: CompressedRistretto) -> Variable {
        let sub_proof = &mut self.sub_proofs[self.cur_proof_idx];

        let i = sub_proof.V.len();
        // Add the commitment to the transcript.
        self.transcript.commit_point(b"V", &commitment);

        sub_proof.V.push(commitment);

        Variable::Committed(i)
    }

    fn flattened_constraints(
        &self,
        cur_proof_idx: usize,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar) {
        let sub_proof = &self.sub_proofs[cur_proof_idx];
        let n = sub_proof.num_vars;
        let m = sub_proof.V.len();

        let mut wL = vec![Scalar::zero(); n];
        let mut wR = vec![Scalar::zero(); n];
        let mut wO = vec![Scalar::zero(); n];
        let mut wV = vec![Scalar::zero(); m];
        let mut wc = Scalar::zero();

        let mut exp_z = *z;
        for lc in sub_proof.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[*i] -= exp_z * coeff;
                    }
                    Variable::One() => {
                        wc -= exp_z * coeff;
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV, wc)
    }

    /// Calls all remembered callbacks with an API that
    /// allows generating challenge scalars.
    fn create_randomized_constraints(mut self) -> Result<Self, R1CSError> {
        // Clear the pending multiplier (if any) because it was committed into A_L/A_R/S.
        let sub_proof = &mut self.sub_proofs[self.cur_proof_idx];
        sub_proof.pending_multiplier = None;

        if sub_proof.deferred_constraints.len() == 0 {
            self.transcript.r1cs_1phase_domain_sep();
            Ok(self)
        } else {
            self.transcript.r1cs_2phase_domain_sep();
            // Note: the wrapper could've used &mut instead of ownership,
            // but specifying lifetimes for boxed closures is not going to be nice,
            // so we move the self into wrapper and then move it back out afterwards.
            let mut callbacks = mem::replace(&mut sub_proof.deferred_constraints, Vec::new());
            let mut wrapped_self = RandomizingAggrVerifier { verifier: self };
            for callback in callbacks.drain(..) {
                callback(&mut wrapped_self)?;
            }
            Ok(wrapped_self.verifier)
        }
    }

    pub fn verify(
        mut self,
        proof: &R1CSProof,
        pc_gens: &PedersenGens,
        bp_gens: &BulletproofGens,
    ) -> Result<(), R1CSError> {
        self.transcript.commit_point(b"A_I1", &proof.A_I1);
        self.transcript.commit_point(b"A_O1", &proof.A_O1);
        self.transcript.commit_point(b"S1", &proof.S1);

        /*self.transcript.commit_point(b"A_I2", &proof.A_I2);
        self.transcript.commit_point(b"A_O2", &proof.A_O2);
        self.transcript.commit_point(b"S2", &proof.S2);*/

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        self.transcript.commit_point(b"T_1", &proof.T_1);
        self.transcript.commit_point(b"T_3", &proof.T_3);
        self.transcript.commit_point(b"T_4", &proof.T_4);
        self.transcript.commit_point(b"T_5", &proof.T_5);
        self.transcript.commit_point(b"T_6", &proof.T_6);

        let u = self.transcript.challenge_scalar(b"u");
        let x = self.transcript.challenge_scalar(b"x");

        self.transcript.commit_scalar(b"t_x", &proof.t_x);
        self.transcript
            .commit_scalar(b"t_x_blinding", &proof.t_x_blinding);
        self.transcript
            .commit_scalar(b"e_blinding", &proof.e_blinding);

        let w = self.transcript.challenge_scalar(b"w");

        let n = self.sub_proofs.iter().fold(0, |sum, sp| sum + sp.num_vars);
        let padded_n = n.next_power_of_two();
        let pad = padded_n - n;

        // Get IPP variables
        let (u_sq, u_inv_sq, s) = proof
            .ipp_proof
            .verification_scalars(padded_n, self.transcript)
            .map_err(|_| R1CSError::VerificationError)?;

        let a = proof.ipp_proof.a;
        let b = proof.ipp_proof.b;

        let y_inv = y.invert();
        let y_inv_vec = util::exp_iter(y_inv).take(padded_n).collect::<Vec<Scalar>>();

        // combined delta + wc from each sub proof
        let mut delta_wc = Scalar::zero();

        // combined V from each sub proof
        let mut V = vec![];

        // combined wV from each sub proof
        let mut weightsV = vec![];

        let mut g_scalars = vec![];
        let mut h_scalars = vec![];
        let mut G_vec = Vec::<RistrettoPoint>::new();
        let mut H_vec = Vec::<RistrettoPoint>::new();

        let mut num_processed_vars = 0;

        for (i, sub_proof) in self.sub_proofs.iter().enumerate() {
            let num_vars = sub_proof.num_vars;

            let (wL, wR, wO, mut wV, wc) = self.flattened_constraints(i, &z);

            let yneg_wR = wR
                .into_iter()
                .zip(y_inv_vec.iter())
                .map(|(wRi, exp_y_inv)| wRi * exp_y_inv)
                .collect::<Vec<Scalar>>();
            let delta = inner_product(&yneg_wR, &wL);
            delta_wc = delta_wc + (delta + wc);
            V.append(&mut sub_proof.V.iter().map(|V_i| V_i.decompress()).collect::<Vec<Option<RistrettoPoint>>>());
            weightsV.append(&mut wV);


            // XXX: Avoid recomputation
            let u_for_g = iter::repeat(Scalar::one()).take(num_vars);
            let u_for_h = u_for_g.clone();

            let mut g = yneg_wR
                .iter()
                .zip(u_for_g)
                .zip(s.iter().skip(num_processed_vars).take(num_vars))
                .map(|((yneg_wRi, u_or_1), s_i)| u_or_1 * (x * yneg_wRi - a * s_i)).collect::<Vec<Scalar>>();

            let mut h = u_for_h
                .zip(y_inv_vec.iter())
                .zip(s.iter().rev().skip(num_processed_vars).take(num_vars))
                .zip(wL.into_iter())
                .zip(wO.into_iter())
                .map(|((((u_or_1, y_inv_i), s_i_inv), wLi), wOi)| {
                    u_or_1 * (y_inv_i * (x * wLi + wOi - b * s_i_inv) - Scalar::one())
                }).collect::<Vec<Scalar>>();

            g_scalars.append(&mut g);
            h_scalars.append(&mut h);

            let gens = bp_gens.share(i);
            let mut gv: Vec<RistrettoPoint> = gens.G(num_vars).cloned().collect();
            let mut hv: Vec<RistrettoPoint> = gens.H(num_vars).cloned().collect();
            G_vec.append(&mut gv);
            H_vec.append(&mut hv);

            num_processed_vars += num_vars;
        }

        assert_eq!(n, num_processed_vars);

        let u_for_g = iter::repeat(u).take(pad);
        let u_for_h = u_for_g.clone();

        g_scalars.append(&mut u_for_g
            .zip(s.iter().skip(n).take(pad))
            .map(|(u_or_1, s_i)| u_or_1 * (- a * s_i)).collect::<Vec<Scalar>>()
        );

        h_scalars.append(&mut u_for_h
            .zip(y_inv_vec.iter().skip(n))
            .zip(s.iter().rev().skip(n).take(pad))
            .map(| ((u_or_1, y_inv_i), s_i_inv) | {
                u_or_1 * (y_inv_i * (- b * s_i_inv) - Scalar::one())
            }).collect::<Vec<Scalar>>());

        let gens = bp_gens.share(self.sub_proofs.len());
        G_vec.append(&mut gens.G(pad).cloned().collect());
        H_vec.append(&mut gens.H(pad).cloned().collect());

        let mut rng = rand::thread_rng();
        let r = Scalar::random(&mut rng);

        let xx = x * x;
        let rxx = r * xx;
        let xxx = x * xx;

        // group the T_scalars and T_points together
        let r_xxx = r * xxx;
        let r_xxxx = r_xxx * x;
        let r_xxxxx = r_xxxx * x;
        let r_xxxxxx = r_xxxxx * x;
        let T_scalars = [r * x, r_xxx, r_xxxx, r_xxxxx, r_xxxxxx];
        let T_points = [proof.T_1, proof.T_3, proof.T_4, proof.T_5, proof.T_6];

        use curve25519_dalek::traits::IsIdentity;

        /*let Ts = [x, xxx, xxx * x, xxx * xx, xxx * xxx];
        let t2_check = RistrettoPoint::optional_multiscalar_mul(
            weightsV.iter().map(|wVi| wVi * xx) // V
                .chain(Ts.iter().cloned())
                .chain(iter::once(
                    (xx * delta_wc - proof.t_x),
                )) // B
                .chain(iter::once(-proof.t_x_blinding)), // B_blinding
            V.iter().cloned()
                .chain(T_points.iter().map(|T_i| T_i.decompress()))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(iter::once(Some(pc_gens.B_blinding))),
        )
            .ok_or_else(|| R1CSError::VerificationError)?;

        if !t2_check.is_identity() {
            return Err(R1CSError::VerificationError);
        }

        println!("t2 is correct");*/

        let mega_check = RistrettoPoint::optional_multiscalar_mul(
            iter::once(x) // A_I1
                .chain(iter::once(xx)) // A_O1
                .chain(iter::once(xxx)) // S1
                .chain(iter::once(u * x)) // A_I2
                .chain(iter::once(u * xx)) // A_O2
                .chain(iter::once(u * xxx)) // S2
                .chain(weightsV.iter().map(|wVi| wVi * rxx)) // V
                .chain(T_scalars.iter().cloned()) // T_points
                .chain(iter::once(
                    w * (proof.t_x - a * b) + r * (xx * delta_wc - proof.t_x),
                )) // B
                .chain(iter::once(-proof.e_blinding - r * proof.t_x_blinding)) // B_blinding
                .chain(g_scalars) // G
                .chain(h_scalars) // H
                .chain(u_sq.iter().cloned()) // ipp_proof.L_vec
                .chain(u_inv_sq.iter().cloned()), // ipp_proof.R_vec
            iter::once(proof.A_I1.decompress())
                .chain(iter::once(proof.A_O1.decompress()))
                .chain(iter::once(proof.S1.decompress()))
                .chain(iter::once(proof.A_I2.decompress()))
                .chain(iter::once(proof.A_O2.decompress()))
                .chain(iter::once(proof.S2.decompress()))
                .chain(V)
                .chain(T_points.iter().map(|T_i| T_i.decompress()))
                .chain(iter::once(Some(pc_gens.B)))
                .chain(iter::once(Some(pc_gens.B_blinding)))
                .chain(G_vec.iter().map(|&G_i| Some(G_i)))
                .chain(H_vec.iter().map(|&H_i| Some(H_i)))
                .chain(proof.ipp_proof.L_vec.iter().map(|L_i| L_i.decompress()))
                .chain(proof.ipp_proof.R_vec.iter().map(|R_i| R_i.decompress())),
        )
            .ok_or_else(|| R1CSError::VerificationError)?;

        if !mega_check.is_identity() {
            return Err(R1CSError::VerificationError);
        }

        Ok(())
    }
}