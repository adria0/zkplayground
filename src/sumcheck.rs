#![allow(non_snake_case)]

/*
SUMCHECK

Provide an argument to a verifier to check the sum of all the images of g()
without the verifier checking all the images of g, only log(#n) checks are needed

https://hackmd.io/@CPerezz/BJXq7U9Bn
https://zkproof.org/2020/03/16/sum-checkprotocol/
https://semiotic.ai/articles/sumcheck-tutorial/

*/

#[cfg(test)]
mod test {
    type F = ark_bn254::fr::Fr;
    type P = SparsePolynomial<ark_bn254::fr::Fr, SparseTerm>;
    use ark_ff::{Field, Zero};
    use ark_poly::multivariate::{SparsePolynomial, SparseTerm};
    use ark_poly::{DenseMVPolynomial, Polynomial};
    use crate::util::{mpoly, MultiPolyUtils};

    fn gen_hypercube_domain(pow: usize) -> Vec<Vec<F>> {
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

    #[test]
    fn test() {
        // this are the offsets of the variables in a multivariate polinomial

        const X: usize = 0;
        const Y: usize = 1;
        const Z: usize = 2;

        // the function that we want to prove the sum of the preimages
        let g: P = mpoly!("2x^3+xz+yz");

        // Prover has full access to evaluation domain and computes all the sum of all the images
        // of the domain of g

        let domain = gen_hypercube_domain(g.num_vars);
        let H: F = domain.iter().map(|p| g.evaluate(p)).sum();
        assert_eq!(H, F::from(12));

        // Keeping variable x, generate all combinations that we need for y and z
        // this is (0,0) (0,1) (1,0) (1,1)

        let partial_evals: Vec<_> = gen_hypercube_domain(g.num_vars - 1);

        // Now create evaluations for y and z
        // this is s0 = g(x,0,0) + g(x,0,1) + g(x,1,0) + g(x,1,1) = 8x^3 + 2x + 1

        let mut s0 = P::zero();
        for p in partial_evals {
            let evals: Vec<(usize, F)> = p
                .into_iter()
                .enumerate()
                .map(|(var, value)| (var + 1, value))
                .collect();
            s0 = s0 + g.partial_eval(&evals)
        }

        // Verifier: recieves s0 and checks that s0(0) + s0(1) == H

        assert_eq!(
            s0.partial_eval(&[(X, F::ZERO)]) + s0.partial_eval(&[(X, F::ONE)]),
            P::from_coefficients_vec(0, vec![(H, SparseTerm::default())])
        );

        // Verifier: now samples (random or fiat-shamir) an r0 ( = 2) and sends it to the prover

        let r0 = F::from(2);

        // Prover: recieves r0, and generates
        // s1 = g(r0,y,0) + g(r0,y,1)= 34 + y
        // sends s1 to verifier

        let partial_evals: Vec<_> = gen_hypercube_domain(g.num_vars - 2);

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

        // Verifier: checks that s1(0) + s1(1) == s0(r0)

        assert_eq!(
            s1.partial_eval(&[(Y, F::ZERO)]) + s1.partial_eval(&[(Y, F::ONE)]),
            s0.partial_eval(&[(X, r0)])
        );

        // Verifier: now samples (random or fiat-shamir) an r1 ( = 7) and sends it to the prover

        let r1 = F::from(7);

        // Prover: recieves r1, but.. there's no more possible divisions in the domain!
        // s2 = g(r0,r1,z) = 9z+16
        // sends s2 to verifier

        let s2 = g.partial_eval(&[(X, r0), (Y, r1)]);

        // Verifier: checks that s2(0) + s2(1) == s1(r1), that is the final check

        assert_eq!(
            s2.partial_eval(&[(Z, F::ZERO)]) + s2.partial_eval(&[(Z, F::ONE)]),
            s1.partial_eval(&[(Y, r1)])
        );

        // so the verifier only has to do log(n) checks to verify if the sum of all the images of g is ok
    }
}
