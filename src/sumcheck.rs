#![allow(non_snake_case)]

/*
SUMCHECK
-----------
Provide an argument to a verifier to
- check that the sum of all the images of g() is a value being g() a boolean-multivariate
  low-degree polinomial (so domain is a boolean hypercube)
- but without the verifier computing all the images of g, only log(#n) checks are needed
https://hackmd.io/@CPerezz/BJXq7U9Bn
https://zkproof.org/2020/03/16/sum-checkprotocol/
https://semiotic.ai/articles/sumcheck-tutorial/

*/

use crate::interactive_protocol::{InteractiveVerifier, VerifierResponse, InteractiveProver};
use crate::util::*;
use ark_ff::{Field, Zero};
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension;
use ark_poly::multivariate::{SparsePolynomial, SparseTerm};
use ark_poly::{DenseMVPolynomial, Polynomial};
use ark_poly::evaluations::multivariate::multilinear::{MultilinearExtension};

#[derive(Clone)]
pub struct SumCheck<F: Field> {
    pub f: SparsePolynomial<F, SparseTerm>,
    pub sum: F,
}

pub struct SumcheckVerifier<F: Field> {
    pub sumcheck: SumCheck<F>,
    pub challenges: Vec<F>,
    pub polys: Vec<SparsePolynomial<F, SparseTerm>>,
}

impl<F: Field> SumcheckVerifier<F> {
    pub fn new(sumcheck: SumCheck<F>) -> Self {
        Self {
            polys: vec![sumcheck.f.clone()],
            sumcheck,
            challenges: vec![],
        }
    }
}
impl<F: Field> InteractiveVerifier<SparsePolynomial<F, SparseTerm>, F> for SumcheckVerifier<F> {
    fn verify(&mut self, s: SparsePolynomial<F, SparseTerm>) -> VerifierResponse<F> {

        self.polys.push(s);

        let last_poly = &self.polys[self.polys.len() - 2];
        let this_poly = &self.polys[self.polys.len() - 1];

        let this_round_eval = this_poly.partial_eval(&[(self.challenges.len(), F::ZERO)])
            + this_poly.partial_eval(&[(self.challenges.len(), F::ONE)]);

        let last_round_eval = if self.challenges.is_empty() {
            SparsePolynomial::from_coefficients_vec(
                0,
                vec![(self.sumcheck.sum, SparseTerm::default())],
            )
        } else {
            last_poly
                .partial_eval(&[(self.challenges.len() - 1, self.challenges[self.challenges.len() - 1])])
        };
       
        if this_round_eval != last_round_eval {
            return VerifierResponse::Failed("this_round_eval != last_round_eval".into());
        }

        // Checks that the s0 polinomial has the same degree that the degree of the
        // uplifted variable in g

        if this_poly.degree() < last_poly.var_degree(self.challenges.len()) {
            return VerifierResponse::Failed("bad degree".into());
        }

        if self.challenges.len() == self.sumcheck.f.num_vars - 1 {
            VerifierResponse::Success
        } else {
            let mut rand = rand::thread_rng();
            let r = F::rand(&mut rand);
            self.challenges.push(r);
            VerifierResponse::Challenge(r)
        }
    }
}

pub struct SumcheckProver<F: Field> {
    pub sumcheck: SumCheck<F>,
    pub challenges: Vec<F>,
}

impl<F: Field> SumcheckProver<F> {
    pub fn new(f: SparsePolynomial<F, SparseTerm>) -> SumcheckProver<F> {
        let domain = gen_boolean_hypercube_domain::<F>(f.num_vars);
        let sum: F = domain.iter().map(|p| f.evaluate(p)).sum();
        let sumcheck = SumCheck { f, sum };
        Self {
            sumcheck,
            challenges: vec![],
        }
    }
    pub fn next_poly(&mut self, r: Option<F>) -> SparsePolynomial<F, SparseTerm> {
        if let Some(r) = r {
            self.challenges.push(r);
        }

        // polinomial coefficients are [r0, r1, r2, ...., VAR, ... , <domain> ]

        let r_vars = self.challenges.iter().cloned().enumerate().collect::<Vec<_>>();
        let subdomain =
            gen_boolean_hypercube_domain::<F>(self.sumcheck.f.num_vars - 1 - self.challenges.len());

        if subdomain.is_empty() {
            self.sumcheck.f.partial_eval(&r_vars)
        } else {
            let mut s = SparsePolynomial::zero();
            for p in subdomain {
                let mut evals: Vec<(usize, F)> = p
                    .into_iter()
                    .enumerate()
                    .map(|(var, value)| (var + self.challenges.len() + 1, value))
                    .collect();

                evals.append(&mut r_vars.clone());
                s = s + self.sumcheck.f.partial_eval(&evals)
            }

            s
        }
    }
}

impl<F: Field> InteractiveProver<SparsePolynomial<F, SparseTerm>, F> for SumcheckProver<F> {

    fn start(&mut self) -> SparsePolynomial<F, SparseTerm> {
        self.next_poly(None)
    }

    fn next(&mut self, r: F) -> SparsePolynomial<F, SparseTerm> {
        self.next_poly(Some(r))
   }
}

pub fn gen_boolean_hypercube_domain<F: Field>(pow: usize) -> Vec<Vec<F>> {
    if pow == 0 {
        return vec![vec![]];
    }
    let mut domain = vec![vec![F::ZERO], vec![F::ONE]];
    for _ in 1..pow {
        domain = domain
            .into_iter()
            .flat_map(|mut v| {
                let mut zero = v.clone();
                zero.push(F::ZERO);
                v.push(F::ONE);
                vec![zero, v]
            })
            .collect();
    }
    domain
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::util::*;
    type F = ark_bn254::fr::Fr;
    type P = SparsePolynomial<ark_bn254::fr::Fr, SparseTerm>;
    use crate::interactive_protocol::test_interactive_protocol;
    use ark_ff::{Field, Zero};
    use ark_poly::multivariate::{SparsePolynomial, SparseTerm};
    use ark_poly::{DenseMVPolynomial, Polynomial};

    #[test]
    fn sumcheck_small() {
        let mut prover = SumcheckProver::<F>::new(mvpoly!("2x^3+xz+yz"));
        let mut verifier = SumcheckVerifier::new(prover.sumcheck.clone());

        test_interactive_protocol(&mut prover, &mut verifier).expect("should pass");
    }

    #[test]
    fn sumcheck_larger() {
        let mut prover = SumcheckProver::<F>::new(mvpoly!("2x^3+xz+yz+8yw^8"));
        let mut verifier = SumcheckVerifier::new(prover.sumcheck.clone());

        test_interactive_protocol(&mut prover, &mut verifier).expect("should pass");
    }


    #[test]
    fn sumcheck_by_hand() {
        // this are the offsets of the variables in a multivariate polinomial

        const X: usize = 0;
        const Y: usize = 1;
        const Z: usize = 2;

        // the function that we want to prove the sum of the preimages
        let g: P = mvpoly!("2x^3+xz+yz");

        // --- Prover

        // Prover has full access to evaluation domain and computes all the sum of all the images
        // of the domain of g

        let domain = gen_boolean_hypercube_domain(g.num_vars);
        let H: F = domain.iter().map(|p| g.evaluate(p)).sum();
        assert_eq!(H, F::from(12));

        // Keeping variable x, generate all combinations that we need for y and z
        // this is (0,0) (0,1) (1,0) (1,1)

        let partial_evals: Vec<_> = gen_boolean_hypercube_domain(g.num_vars - 1);

        // Now create evaluations for y and z
        // this is s0(x) = g(x,0,0) + g(x,0,1) + g(x,1,0) + g(x,1,1) = 8x^3 + 2x + 1

        let mut s0 = P::zero();
        for p in partial_evals {
            let evals: Vec<(usize, F)> = p
                .into_iter()
                .enumerate()
                .map(|(var, value)| (var + 1, value))
                .collect();
            s0 = s0 + g.partial_eval(&evals)
        }

        // --- Verifier

        // Recieves H and s0 and checks that s0(0) + s0(1) == H

        assert_eq!(
            s0.partial_eval(&[(X, F::ZERO)]) + s0.partial_eval(&[(X, F::ONE)]),
            P::from_coefficients_vec(0, vec![(H, SparseTerm::default())])
        );

        // Checks that the s0 polinomial has the same degree that the degree of the
        // uplifted variable in g

        assert!(s0.degree() >= g.var_degree(X));

        // Now samples (random or fiat-shamir) an r0 ( = 2) and sends it to the prover

        let r0 = F::from(2);

        // --- Prover

        // Recieves r0, and generates
        // s1(y) = g(r0,y,0) + g(r0,y,1)= 34 + y
        // sends s1 to verifier

        let partial_evals: Vec<_> = gen_boolean_hypercube_domain(g.num_vars - 2);

        let mut s1 = P::zero();
        for p in partial_evals {
            let mut evals: Vec<(usize, F)> = p
                .into_iter()
                .enumerate()
                .map(|(var, value)| (var + 2, value))
                .collect();
            evals.push((X, r0));
            s1 = s1 + g.partial_eval(&evals)
        }

        // --- Verifier

        // checks that s1(0) + s1(1) == s0(r0)

        assert_eq!(
            s1.partial_eval(&[(Y, F::ZERO)]) + s1.partial_eval(&[(Y, F::ONE)]),
            s0.partial_eval(&[(X, r0)])
        );

        // Checks that the s1 polinomial has the same degree that the degree of the
        // uplifted variable in g

        assert!(s1.degree() >= g.var_degree(Y));

        // samples (random or fiat-shamir) an r1 ( = 7) and sends it to the prover

        let r1 = F::from(7);

        // --- Prover

        // Recieves r1, but.. there's no more possible divisions in the domain!
        // s2 = g(r0,r1,z) = 9z+16
        // sends s2 to verifier

        let s2 = g.partial_eval(&[(X, r0), (Y, r1)]);

        // --- Verifier

        // checks that s2(0) + s2(1) == s1(r1), that is the final check

        assert_eq!(
            s2.partial_eval(&[(Z, F::ZERO)]) + s2.partial_eval(&[(Z, F::ONE)]),
            s1.partial_eval(&[(Y, r1)])
        );

        // so the verifier only has to do log(n) checks to verify if the sum of all the images of g is ok
    }
}

