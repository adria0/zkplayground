#![allow(clippy::needless_range_loop)]

// https://eprint.iacr.org/2024/108.pdf
// https://eprint.iacr.org/2022/1355.pdf page 25
// https://xn--2-umb.com/24/sumcheck/

/*
We cannot use sumcheck protocol straighforward to prove that g(x) = 0, because sumcheck is for
  proving that the sum of all the images of g() is a value, and a prover can cheat by providing
  a polynomial that is not zero but has the same sum of images.

Remember that x is a boolean hypercube.

The intuition is that if we choose a random α, then g(α) = 0 with high probability, so we have sum
    {if x==α then 0 else 1}

- eq function: eq(a,b)=1 if a=b, 0 otherwise. In the boolean hypercube is implemented  as
  eq(a,b) = ∏(aₙ·bₙ+(1-aₙ)(1-bₙ))

- then ZEROCHECK(x) = Σ{x=[01]ⁿ} g(x)·eq(x,α) only will be zero if g(α) = 0

In the case of verifying, the trick here is to compute the eq function over alpha, that is not complicated, e.g.

let's supose that α = 2, this means that α = <1 0> in the boolean hypercube, so we need to compute
  eq(x,<1 0>) =   ( x₀ * 0 + ( 1 - x₀ )( 1 - 0 ) )
                * ( x₁ * 1 + ( 1 - x₁ )( 1 - 1 ) )
              = ( 1 - x₀ ) * x₁
              = x₁ - x₀*x₁

then
  SUMCHECK(x)= g(x) * (x₁ - x₀*x₁)    

*/

use core::num;

use ark_ff::{Field, Zero};
use ark_poly::multivariate::Term;
use ark_poly::multivariate::{SparsePolynomial, SparseTerm};
use ark_poly::{DenseMVPolynomial, Polynomial};

fn build_eq_poly<F: Field>(alpha: Vec<F>) -> SparsePolynomial<F, SparseTerm> {
    let degree = alpha.len();

    let mut eq_poly =
        SparsePolynomial::from_coefficients_vec(0, vec![(F::one(), SparseTerm::default())]);

    for i in 0..degree {
        let m = if alpha[i] == F::zero() {
            // if alpha[i] = 0 then eq_poly *= x_i * 0 + ( 1 - x_i )( 1 - 0 ) => eq_poly *= 1 - x_i
            let one = (F::one(), SparseTerm::default());
            let minus_x_i = (-F::one(), SparseTerm::new(vec![(i, 1)]));
            SparsePolynomial::from_coefficients_vec(degree, vec![one, minus_x_i])
        } else {
            // if alpha[i] = 1 then eq_poly *= x_i * 1 + ( 1 - x_i )( 1 - 1 ) => eq_poly *= x_i
            let x_i = (F::one(), SparseTerm::new(vec![(i, 1)]));
            SparsePolynomial::from_coefficients_vec(degree, vec![x_i])
        };

        eq_poly = naive_mul(&eq_poly, &m);
    }
    eq_poly
}

/// Perform a naive n^2 multiplication of `self` by `other`.
fn naive_mul<F: Field>(
    cur: &SparsePolynomial<F, SparseTerm>,
    other: &SparsePolynomial<F, SparseTerm>,
) -> SparsePolynomial<F, SparseTerm> {
    let num_vars = std::cmp::max(cur.num_vars, other.num_vars);
    if cur.is_zero() || other.is_zero() {
        SparsePolynomial::zero()
    } else {
        let mut result_terms = Vec::new();
        for (cur_coeff, cur_term) in cur.terms.iter() {
            for (other_coeff, other_term) in other.terms.iter() {
                let mut term : Vec<(usize, usize)>= (**cur_term).to_vec();
                term.extend((**other_term).to_vec());
                result_terms.push((*cur_coeff * *other_coeff, SparseTerm::new(term)));
            }
        }

        SparsePolynomial::from_coefficients_slice(num_vars, result_terms.as_slice())
    }
}

#[cfg(test)]
mod test {
    use crate::interactive_protocol::test_interactive_protocol;
    use crate::util::mvpoly;
    use ark_ff::One;
    use ark_ff::{Fp64, MontBackend, MontConfig};
    use super::super::util::PolyToString;
    use crate::sumcheck::*;

    use super::*;

    #[derive(MontConfig)]
    #[modulus = "17"]
    #[generator = "3"]
    pub struct FqConfig;
    pub type Fq = Fp64<MontBackend<FqConfig, 1>>;


    #[test]
    fn test_eq() {
      let alpha = vec![Fq::zero(), Fq::one()];
      let eq_poly = build_eq_poly(alpha);
      assert_eq!(eq_poly.to_string(), "-xy+y"); //  x₁ - x₀*x₁
    }

    #[test]
    fn test_zerocheck() {

        // g = x(1−x)+y(1−y)+z(1−z) evals to zero in all points
        let g =
          naive_mul(&mvpoly!("x"), &mvpoly!("1-x")) + 
          naive_mul(&mvpoly!("y"), &mvpoly!("1-y")) + 
          naive_mul(&mvpoly!("z"), &mvpoly!("1-z"));

        for x in [Fq::zero(), Fq::one()] {
          for y in [Fq::zero(), Fq::one()] {
            for z in [Fq::zero(), Fq::one()] {
              assert!(g.evaluate(&vec![x, y, z]).is_zero());
            }
          }
        }

        // select a random element alpha <0 1 0>
        // and build the multilinear eq polynomial xyz-xy-yz+y
        let alpha = vec![Fq::zero(), Fq::one(), Fq::zero()];
        let eq_poly = build_eq_poly(alpha);

        // build the zero check polynomial
        //   x^3yz-xy^3z-xyz^3+x^3y+2x^2yz+xy^3+xy^2z+2xyz^2+y^3z+yz^3
        //   -2x^2y-xy^2-2xyz-y^3-y^2z-2yz^2+xy+y^2+yz
        let zero_check = naive_mul(&g, &eq_poly);

        // run sumcheck over this polynomial
        let mut prover = SumcheckProver::<Fq>::new(zero_check);
        let mut verifier = SumcheckVerifier::new(prover.sumcheck.clone());
        test_interactive_protocol(&mut prover, &mut verifier).expect("should pass");
    }
}
