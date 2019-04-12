extern crate rand;
extern crate rand_chacha;
extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;

use rand::SeedableRng;
use rand_chacha::ChaChaRng;
use curve25519_dalek::scalar::Scalar;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs::r1cs::LinearCombination;

// For benchmarking
use std::time::{Duration, Instant};

//pub const MIMC_ROUNDS: usize = 322;
pub const MIMC_ROUNDS: usize = 10;


pub fn mimc(
    xl: &Scalar,
    xr: &Scalar,
    constants: &[Scalar]
) -> Scalar
{
    assert_eq!(constants.len(), MIMC_ROUNDS);

    let mut xl = xl.clone();
    let mut xr = xr.clone();

    for i in 0..MIMC_ROUNDS {
        let mut tmp1 = xl + constants[i];
        let mut tmp2 = (tmp1 * tmp1) * tmp1;
        tmp2 += xr;
        xr = xl;
        xl = tmp2;
    }

    xl
}

/*pub fn hash_2(cs: &mut ConstraintSystem,
              mut left_val: Option<Scalar>,
              mut left: Variable,
              mut right_val: Option<Scalar>,
              mut right: Variable,
              mimc_rounds: usize,
              mimc_constants: &[Scalar]) -> Result<(Option<Scalar>, Variable), R1CSError> {
    for j in 0..mimc_rounds {
        // xL, xR := xR + (xL + Ci)^3, xL
        //let cs = &mut cs.namespace(|| format!("mimc round {}", j));

        // tmp = (xL + Ci)^2
        let mut tmp_value = left_val.map(|mut e| {
            e.add_assign(&mimc_constants[j]);
            e.square();
            e
        });
        let mut tmp = cs.alloc(|| "tmp", || {
            tmp_value.ok_or(R1CSError::MissingAssignment)
        })?;

        cs.enforce(
            || "tmp = (xL + Ci)^2",
            |lc| lc + left + (mimc_constants[j], CS::one()),
            |lc| lc + left + (mimc_constants[j], CS::one()),
            |lc| lc + tmp
        );

        // new_xL = xR + (xL + Ci)^3
        // new_xL = xR + tmp * (xL + Ci)
        // new_xL - xR = tmp * (xL + Ci)
        let mut new_xl_value = left_val.map(|mut e| {
            e.add_assign(&mimc_constants[j]);
            e.mul_assign(&tmp_value.unwrap());
            e.add_assign(&right_val.unwrap());
            e
        });

        let mut new_xl = if j == (MIMC_ROUNDS-1) {
            // This is the last round, xL is our image and so
            // we allocate a public input.
            cs.alloc_input(|| "root", || {
                new_xl_value.ok_or(R1CSError::MissingAssignment)
            })?
        } else {
            cs.alloc(|| "new_xl", || {
                new_xl_value.ok_or(R1CSError::MissingAssignment)
            })?
        };

        cs.enforce(
            || "new_xL = xR + (xL + Ci)^3",
            |lc| lc + tmp,
            |lc| lc + left + (mimc_constants[j], CS::one()),
            |lc| lc + new_xl - right
        );

        // xR = xL
        right = left;
        right_val = left_val;

        // xL = new_xL
        left = new_xl;
        left_val = new_xl_value;
    }
    Ok((left_val, left))
}*/


#[test]
fn test_mimc() {
    let mut test_rng = ChaChaRng::from_seed([24u8; 32]);

    // Generate the MiMC round constants
    let constants = (0..MIMC_ROUNDS).map(|_| Scalar::random(&mut test_rng)).collect::<Vec<_>>();

    const SAMPLES: u32 = 50;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    for _ in 0..SAMPLES {
        // Generate a random preimage and compute the image
        let xl = Scalar::random(&mut test_rng);
        let xr = Scalar::random(&mut test_rng);
        let image = mimc(&xl, &xr, &constants);

    }
}