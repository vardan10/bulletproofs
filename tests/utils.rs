extern crate bulletproofs;
extern crate curve25519_dalek;

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, Variable};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use bulletproofs::r1cs::LinearCombination;

/// Represents a variable for quantity, along with its assignment.
#[derive(Copy, Clone, Debug)]
pub struct AllocatedQuantity {
    pub variable: Variable,
    pub assignment: Option<u64>
}

#[derive(Copy, Clone, Debug)]
pub struct AllocatedScalar {
    pub variable: Variable,
    pub assignment: Option<Scalar>
}


/// if x == 0 then y = 0 else y = 1
/// if x != 0 then inv = x^-1 else inv = 0
/// x*(1-y) = 0
/// x*inv = y
/// The idea is described in the Pinocchio paper and i first saw it in https://github.com/HarryR/ethsnarks/blob/master/src/gadgets/isnonzero.cpp

/// Enforces that x is 0.
pub fn is_zero_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    x: AllocatedScalar
) -> Result<(), R1CSError> {
    let y: u32 = 0;
    let inv: u32 = 0;

    let x_lc: LinearCombination = vec![(x.variable, Scalar::one())].iter().collect();
    let one_minus_y_lc: LinearCombination = vec![(Variable::One(), Scalar::from(1-y))].iter().collect();
    let y_lc: LinearCombination = vec![(Variable::One(), Scalar::from(y))].iter().collect();
    let inv_lc: LinearCombination = vec![(Variable::One(), Scalar::from(inv))].iter().collect();

    // x * (1-y) = 0
    let (_, _, o1) = cs.multiply(x_lc.clone(), one_minus_y_lc);
    cs.constrain(o1.into());

    // x * inv = y
    let (_, _, o2) = cs.multiply(x_lc, inv_lc);
    // Output wire should have value `y`
    cs.constrain(o2 - y_lc);

    Ok(())
}

/// Enforces that x is 0.
pub fn is_nonzero_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    x: AllocatedScalar,
    x_inv: AllocatedScalar,
) -> Result<(), R1CSError> {
    let y: u32 = 1;

    let x_lc: LinearCombination = vec![(x.variable, Scalar::one())].iter().collect();
    let one_minus_y_lc: LinearCombination = vec![(Variable::One(), Scalar::from(1-y))].iter().collect();
    let y_lc: LinearCombination = vec![(Variable::One(), Scalar::from(y))].iter().collect();

    // x * (1-y) = 0
    let (_, _, o1) = cs.multiply(x_lc.clone(), one_minus_y_lc);
    cs.constrain(o1.into());

    // x * x_inv = y
    let inv_lc: LinearCombination = vec![(x_inv.variable, Scalar::one())].iter().collect();
    let (_, _, o2) = cs.multiply(x_lc.clone(), inv_lc.clone());
    // Output wire should have value `y`
    cs.constrain(o2 - y_lc);

    // Ensure x_inv is the really the inverse of x by ensuring x*x_inv = 1
    let (_, x_inv_var, o3) = cs.multiply(x_lc, inv_lc);
    // Output wire should be 1
    let one_lc: LinearCombination = vec![(Variable::One(), Scalar::one())].iter().collect();
    cs.constrain(o3 - one_lc);
    Ok(())
}