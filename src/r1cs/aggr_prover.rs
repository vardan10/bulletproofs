#![allow(non_snake_case)]

use clear_on_drop::clear::Clear;
use core::mem;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{Identity, MultiscalarMul};
use merlin::Transcript;

use super::{ConstraintSystem, LinearCombination, R1CSProof, RandomizedConstraintSystem, Variable};

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use inner_product_proof::InnerProductProof;
use transcript::TranscriptProtocol;
use inner_product_proof::inner_product;
use BulletproofGensShare;

use std::iter;
use util;
use util::{Poly6, VecPoly3};

#[derive(Clone, Debug)]
pub struct ProofShare {
    pub t_x: Scalar,
    pub t_x_blinding: Scalar,
    pub e_blinding: Scalar,
    pub l_vec: Vec<Scalar>,
    pub r_vec: Vec<Scalar>,
    pub n1: usize,
    pub n2: usize
}

/// Aggregatable prover
pub struct AggrProver<'g> {
    pc_gens: &'g PedersenGens,
    /// The constraints accumulated so far.
    constraints: Vec<LinearCombination>,
    /// Stores assignments to the "left" of multiplication gates
    a_L: Vec<Scalar>,
    /// Stores assignments to the "right" of multiplication gates
    a_R: Vec<Scalar>,
    /// Stores assignments to the "output" of multiplication gates
    a_O: Vec<Scalar>,
    /// High-level witness data (value openings to V commitments)
    pub v: Vec<Scalar>,
    /// High-level witness data (blinding openings to V commitments)
    pub v_blinding: Vec<Scalar>,

    // Number of 1st phase gates
    pub n1: usize,
    // Number of 2nd phase gates
    pub n2: usize,

    // Make the 3 below 2-tuples when supporting Randomized CS
    i_blindings: Scalar,
    o_blindings: Scalar,
    s_blindings: Scalar,

    s_L1: Vec<Scalar>,
    s_R1: Vec<Scalar>,

    // Make the 3 below 2-tuples when supporting Randomized CS
    A: RistrettoPoint,
    O: RistrettoPoint,
    S: RistrettoPoint,

    // Commitment to coefficients
    T: Vec<RistrettoPoint>,
    l_poly: VecPoly3,
    r_poly: VecPoly3,
    t_poly: Poly6,
    // Polynomial over the blindings
    t_blinding_poly: Poly6,

    exp_y: Scalar,

    exp_y_inv: Vec<Scalar>,
    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    //deferred_constraints: Vec<Box<Fn(&mut RandomizingAggrProver<'g>) -> Result<(), R1CSError>>>,

    /// Index of a pending multiplier that's not fully assigned yet.
    pending_multiplier: Option<usize>,
}

pub struct RandomizingAggrProver<'g> {
    prover: AggrProver<'g>,
}

impl<'g> ConstraintSystem for AggrProver<'g> {
    type RandomizedCS = RandomizingAggrProver<'g>;

    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        // Synthesize the assignments for l,r,o
        let l = self.eval(&left);
        let r = self.eval(&right);
        let o = l * r;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        // ... and assign them
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        // Constrain l,r,o:
        left.terms.push((l_var, -Scalar::one()));
        right.terms.push((r_var, -Scalar::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate(&mut self, assignment: Option<Scalar>) -> Result<Variable, R1CSError> {
        let scalar = assignment.ok_or(R1CSError::MissingAssignment)?;

        match self.pending_multiplier {
            None => {
                let i = self.a_L.len();
                self.pending_multiplier = Some(i);
                self.a_L.push(scalar);
                self.a_R.push(Scalar::zero());
                self.a_O.push(Scalar::zero());
                Ok(Variable::MultiplierLeft(i))
            }
            Some(i) => {
                self.pending_multiplier = None;
                self.a_R[i] = scalar;
                self.a_O[i] = self.a_L[i] * self.a_R[i];
                Ok(Variable::MultiplierRight(i))
            }
        }
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        let (l, r) = input_assignments.ok_or(R1CSError::MissingAssignment)?;
        let o = l * r;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        // ... and assign them
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        Ok((l_var, r_var, o_var))
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
        where
            F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        // TODO: Enable
        // self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }

    fn evaluate_lc(&self, lc: &LinearCombination) -> Option<Scalar> {
        Some(self.eval(lc))
    }

    fn allocate_single(&mut self, assignment: Option<Scalar>) -> Result<(Variable, Option<Variable>), R1CSError> {
        let var = self.allocate(assignment)?;
        match var {
            Variable::MultiplierLeft(i) => Ok((Variable::MultiplierLeft(i), None)),
            Variable::MultiplierRight(i) => Ok((Variable::MultiplierRight(i), Some(Variable::MultiplierOutput(i)))),
            _ => Err(R1CSError::FormatError)
        }
    }
}

impl<'g> ConstraintSystem for RandomizingAggrProver<'g> {
    type RandomizedCS = Self;

    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        self.prover.multiply(left, right)
    }

    fn allocate(&mut self, assignment: Option<Scalar>) -> Result<Variable, R1CSError> {
        self.prover.allocate(assignment)
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        self.prover.allocate_multiplier(input_assignments)
    }

    fn constrain(&mut self, lc: LinearCombination) {
        self.prover.constrain(lc)
    }

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
        where
            F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        callback(self)
    }

    fn evaluate_lc(&self, lc: &LinearCombination) -> Option<Scalar> {
        self.prover.evaluate_lc(lc)
    }

    fn allocate_single(&mut self, assignment: Option<Scalar>) -> Result<(Variable, Option<Variable>), R1CSError> {
        self.prover.allocate_single(assignment)
    }
}

/// This will not be used for now.
impl<'g> RandomizedConstraintSystem for RandomizingAggrProver<'g> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        //self.prover.transcript.challenge_scalar(label)
        unimplemented!()
    }
}

impl<'g> AggrProver<'g> {
    pub fn new(pc_gens: &'g PedersenGens) -> Self {
        Self {
            pc_gens,
            v: Vec::new(),
            v_blinding: Vec::new(),
            constraints: Vec::new(),
            a_L: Vec::new(),
            a_R: Vec::new(),
            a_O: Vec::new(),
            n1: 0,
            n2: 0,
            i_blindings: Scalar::zero(),
            o_blindings: Scalar::zero(),
            s_blindings: Scalar::zero(),
            s_L1: Vec::new(),
            s_R1: Vec::new(),
            A: RistrettoPoint::identity(),
            O: RistrettoPoint::identity(),
            S: RistrettoPoint::identity(),
            T: Vec::new(),
            l_poly: VecPoly3::zero(0),
            r_poly: VecPoly3::zero(0),
            t_poly: Poly6 {
                t1: Scalar::zero(),
                t2: Scalar::zero(),
                t3: Scalar::zero(),
                t4: Scalar::zero(),
                t5: Scalar::zero(),
                t6: Scalar::zero(),
            },
            t_blinding_poly: Poly6 {
                t1: Scalar::zero(),
                t2: Scalar::zero(),
                t3: Scalar::zero(),
                t4: Scalar::zero(),
                t5: Scalar::zero(),
                t6: Scalar::zero(),
            },
            exp_y: Scalar::zero(),
            exp_y_inv:  Vec::new(),
            pending_multiplier: None,
        }
    }

    pub fn commit(&mut self, v: Scalar, v_blinding: Scalar) -> (CompressedRistretto, Variable) {
        let i = self.v.len();
        self.v.push(v);
        self.v_blinding.push(v_blinding);
        let V = self.pc_gens.commit(v, v_blinding).compress();

        (V, Variable::Committed(i))
    }

    fn flattened_constraints(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
        let n = self.a_L.len();
        let m = self.v.len();

        let mut wL = vec![Scalar::zero(); n];
        let mut wR = vec![Scalar::zero(); n];
        let mut wO = vec![Scalar::zero(); n];
        let mut wV = vec![Scalar::zero(); m];

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
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
                        // The prover doesn't need to handle constant terms
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV)
    }

    fn eval(&self, lc: &LinearCombination) -> Scalar {
        lc.terms
            .iter()
            .map(|(var, coeff)| {
                coeff
                    * match var {
                    Variable::MultiplierLeft(i) => self.a_L[*i],
                    Variable::MultiplierRight(i) => self.a_R[*i],
                    Variable::MultiplierOutput(i) => self.a_O[*i],
                    Variable::Committed(i) => self.v[*i],
                    Variable::One() => Scalar::one(),
                }
            })
            .sum()
    }

    pub fn commit_low_level_vars(&mut self, gens: &BulletproofGensShare) -> (&RistrettoPoint, &RistrettoPoint, &RistrettoPoint) {
        // TODO: One way to commit_witness_bytes would be to pass hash of blindings to dealer.
        // A simpler but privacy breaking way is to pass all blindings to dealer
        let mut rng = rand::thread_rng();

        let n1 = self.a_L.len();
        let i_blinding1 = Scalar::random(&mut rng);
        let o_blinding1 = Scalar::random(&mut rng);
        let s_blinding1 = Scalar::random(&mut rng);

        let mut s_L1: Vec<Scalar> = (0..n1).map(|_| Scalar::random(&mut rng)).collect();
        let mut s_R1: Vec<Scalar> = (0..n1).map(|_| Scalar::random(&mut rng)).collect();

        // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        let A_I1 = RistrettoPoint::multiscalar_mul(
            iter::once(&i_blinding1)
                .chain(self.a_L.iter())
                .chain(self.a_R.iter()),
            iter::once(&self.pc_gens.B_blinding)
                .chain(gens.G(n1))
                .chain(gens.H(n1)),
        );

        // A_O = <a_O, G> + o_blinding * B_blinding
        let A_O1 = RistrettoPoint::multiscalar_mul(
            iter::once(&o_blinding1).chain(self.a_O.iter()),
            iter::once(&self.pc_gens.B_blinding).chain(gens.G(n1)),
        );

        // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        let S1 = RistrettoPoint::multiscalar_mul(
            iter::once(&s_blinding1)
                .chain(s_L1.iter())
                .chain(s_R1.iter()),
            iter::once(&self.pc_gens.B_blinding)
                .chain(gens.G(n1))
                .chain(gens.H(n1)),
        );

        self.n1 = n1;
        self.i_blindings = i_blinding1;
        self.o_blindings = o_blinding1;
        self.s_blindings = s_blinding1;
        self.s_L1 = s_L1;
        self.s_R1 = s_R1;
        self.A = A_I1;
        self.O = A_O1;
        self.S = S1;
        (&self.A, &self.O, &self.S)
    }

    pub fn commit_to_polynomial(&mut self, y: &Scalar, z: &Scalar) -> &[RistrettoPoint] {
        // TODO: Each prover should use different powers of y
        // TODO: A single rng should be used across all funcs
        let mut rng = rand::thread_rng();

        let n = self.a_L.len();

        let (wL, wR, wO, wV) = self.flattened_constraints(&z);

        let mut l_poly = VecPoly3::zero(n);
        let mut r_poly = VecPoly3::zero(n);

        let mut exp_y = Scalar::one(); // y^n starting at n=0
        let y_inv = y.invert();
        let exp_y_inv = util::exp_iter(y_inv).take(n).collect::<Vec<_>>();

        let sLsR = self.s_L1
            .iter()
            .zip(self.s_R1.iter());
        let mut yneg_wR = vec![];
        for (i, (sl, sr)) in sLsR.enumerate() {
            // l_poly.0 = 0
            // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
            yneg_wR.push(exp_y_inv[i] * wR[i]);
            l_poly.1[i] = self.a_L[i] + exp_y_inv[i] * wR[i];
            // l_poly.2 = a_O
            l_poly.2[i] = self.a_O[i];
            // l_poly.3 = s_L
            l_poly.3[i] = *sl;
            // r_poly.0 = (z * z^Q * W_O) - y^n
            r_poly.0[i] = wO[i] - exp_y;
            // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
            r_poly.1[i] = exp_y * self.a_R[i] + wL[i];
            // r_poly.2 = 0
            // r_poly.3 = y^n * s_R
            r_poly.3[i] = exp_y * sr;

            exp_y = exp_y * y; // y^i -> y^(i+1)
        }

        //println!("prover's wR={:?}", &wR);
        //println!("prover's yneg_wR={:?}", &yneg_wR);

        let t_poly = VecPoly3::special_inner_product(&l_poly, &r_poly);
        //println!("prover's t_poly.t2={:?}", &t_poly.t2);

        let t_1_blinding = Scalar::random(&mut rng);
        let t_3_blinding = Scalar::random(&mut rng);
        let t_4_blinding = Scalar::random(&mut rng);
        let t_5_blinding = Scalar::random(&mut rng);
        let t_6_blinding = Scalar::random(&mut rng);

        // t_2_blinding = <z*z^Q, W_V * v_blinding>
        // in the t_x_blinding calculations, line 76.
        let t_2_blinding = wV
            .iter()
            .zip(self.v_blinding.iter())
            .map(|(c, v_blinding)| c * v_blinding)
            .sum();

        let T_1 = self.pc_gens.commit(t_poly.t1, t_1_blinding);
        let T_3 = self.pc_gens.commit(t_poly.t3, t_3_blinding);
        let T_4 = self.pc_gens.commit(t_poly.t4, t_4_blinding);
        let T_5 = self.pc_gens.commit(t_poly.t5, t_5_blinding);
        let T_6 = self.pc_gens.commit(t_poly.t6, t_6_blinding);

        self.l_poly = l_poly;
        self.r_poly = r_poly;
        self.t_poly = t_poly;
        self.exp_y = exp_y;
        self.exp_y_inv = exp_y_inv;

        self.t_blinding_poly = Poly6 {
            t1: t_1_blinding,
            t2: t_2_blinding,
            t3: t_3_blinding,
            t4: t_4_blinding,
            t5: t_5_blinding,
            t6: t_6_blinding,
        };
        self.T.push(T_1);
        self.T.push(T_3);
        self.T.push(T_4);
        self.T.push(T_5);
        self.T.push(T_6);

       &self.T
    }

    pub fn compute_poly(&mut self, x: &Scalar, u: &Scalar, y: &Scalar) -> ProofShare {
        let x = x.clone();
        let u = u.clone();
        let y = y.clone();

        let n = self.a_L.len();

        let t_x = self.t_poly.eval(x);
        let t_x_blinding = self.t_blinding_poly.eval(x);

        let l_vec = self.l_poly.eval(x);
        let r_vec = self.r_poly.eval(x);

        let e_blinding = x * (self.i_blindings + x * (self.o_blindings + x * self.s_blindings));

        ProofShare {
            t_x,
            t_x_blinding,
            e_blinding,
            l_vec,
            r_vec,
            n1: self.n1,
            n2: self.n2,
        }
    }
}