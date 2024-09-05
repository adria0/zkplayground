use ark_bls12_381::{Bls12_381, Config, Fr as Scalar, G1Projective as G1, G2Projective as G2};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_poly::{domain, univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial};
use std::ops::{Div, Rem, Sub};
use ark_ec::Group;
use ark_ff::{BigInt, CyclotomicMultSubgroup, Field, Zero};
use super::util::*;
use ark_ff::BigInteger;
use super::srs::SRS;

/*
Check the following protocol:

Z(x) , c(x) are public
a(x) , b(x) are private

provide an argument to convince the verifier that a(x)·b(x) = c(x)

Prover                              Verifier
---------------------------------   ------------------------------
1. Gen random s
   | Compute [a(s)]₁
   | Compute [b(s)]₁
   | Compute [c(s)]₁
   | > Send to verifier
                                    2. | Gen random z
                                       | Schwartz-Zippel Lemma 
                                       | < Send to prover
3. Compute
    qa(x) <- a(x)-a(z) / (x-z)
    qb(x) <- b(x)-b(z) / (x-z)
    qc(x) <- c(x)-c(z) / (x-z)
    | a(z), b(z), c(z)
    | π = ([qa(s)]₁, [qb(s)]₁, [qc(s)]₁]
    | > send to verifier

                                    4. Checks
                                       // The polynomial is zero at a random point
                                       // => the polnomial is zero everywhere
                                       a(z)b(z)-c(z) = Z(z)d(z)
                                       // I know the evaluations of qa(s), qb(s) and qc(s) polynomials
                                       // by Schwartz-Zippel Lemma ?
                                       ê([qa(s)]₁, [s-z]₂)  = ê([a(s)-a(z)]₁, [1]₂)
                                       ê([qb(s)]₁, [s-z]₂)  = ê([b(s)-b(z)]₁, [1]₂)
                                       ê([qc(s)]₁, [s-z]₂)  = ê([c(s)-c(z)]₁, [1]₂)
                                       
note that:

ê([qa(s)]₁, [s-z]₂)
    = ê([a(s)-a(z) / (s-z)]₁, [s-z]₂)
    = ê([a(s)-a(z) * 1/(s-z)]₁, [s-z]₂) 
    = ê([a(s)-a(z)]₁, [(s-z) * (1/(s-z))]₂) 
    = ê([a(s)-a(z)]₁, [1]₂)

a(z)b(z)-c(z) = Z(z)d(z)
    ≡ a(z)b(z)-c(z) divides at Z(z)

*/

fn g1(s: Scalar) -> G1 {
    G1::generator() * s
}
fn g2(s: Scalar) -> G2 {
    G2::generator() * s
}

#[test]
fn test_multiplication_argument() {

    let srs = SRS::new(Scalar::from(22), 3); 

    fn poly(v: &[Scalar]) -> DensePolynomial<Scalar> {
        DensePolynomial::from_coefficients_vec(v.to_vec())
    }

    let domain = GeneralEvaluationDomain::<Scalar>::new(3).unwrap();
    let Z_x : DensePolynomial<_> = domain.vanishing_polynomial().into();
    
    // domain[0] = 1
    // domain[1] = ω = 3465144826073652318776269530687742778270252468765361963008
    // domain[2] = ω² = 52435875175126190479447740508185965837690552500527637822603658699938581184512

    // evaluation domain here has 3 elements:       1,  ω, ω²
    let a = Evaluations::from_vec_and_domain([1,  2, 3].map(Scalar::from).into(), domain).interpolate();
    let b = Evaluations::from_vec_and_domain([4,  5, 6].map(Scalar::from).into(), domain).interpolate();    
    let c = Evaluations::from_vec_and_domain([4, 10,18].map(Scalar::from).into(), domain).interpolate();
    
    // p(x) = a(x) * b(x) - c(x) == 0
    let p = &a.naive_mul(&b) -  &c;

    // d(x) = p(x) / Z(x)
    // note that this division never fails since p() is over the domain
    let d = &p / &Z_x;

    // 1
    let a_s = srs.evaluate_at_tau_g1(&a);
    let b_s = srs.evaluate_at_tau_g1(&b);
    let c_s = srs.evaluate_at_tau_g1(&c);

    let p_s = srs.evaluate_at_tau_g1(&p);
    let d_s = srs.evaluate_at_tau_g1(&d);

    // 2 
    let z = Scalar::from(2);

    // 3
    let x_minus_z = poly(&[-z, Scalar::from(1)]);
    let qa = &(&a - &poly(&[a.evaluate(&z)])) / &x_minus_z; 
    let qb = &(&b - &poly(&[b.evaluate(&z)])) / &x_minus_z; 
    let qc = &(&c - &poly(&[c.evaluate(&z)])) / &x_minus_z;

    let q_a_s = srs.evaluate_at_tau_g1(&qa);
    let q_b_s = srs.evaluate_at_tau_g1(&qb);
    let q_c_s = srs.evaluate_at_tau_g1(&qc);

    // 4
    
    // check that p(x) is zero at the domain points
    // with the help of d(x)
    // 
    //   ê(d(s)         , Z(s)) == ê(p(s), 1)
    //   ê(p(s) · 1/Z(s), Z(s)) == ê(p(s), 1)
    //   ê(p(s)         , 1   ) == ê(p(s), 1)

    assert_eq!(
        Bls12_381::pairing(d_s, srs.evaluate_at_tau_g2(&Z_x)),
        Bls12_381::pairing(p_s, G2::generator())
    );
    
    assert_eq!(
        Bls12_381::pairing(q_a_s, srs.g2s[1] - g2(z)),
        Bls12_381::pairing(a_s - g1(a.evaluate(&z)), G2::generator())
    );
    assert_eq!(
        Bls12_381::pairing(q_b_s, srs.g2s[1] - g2(z)),
        Bls12_381::pairing(b_s - g1(b.evaluate(&z)), G2::generator())
    );
    assert_eq!(
        Bls12_381::pairing(q_c_s, srs.g2s[1] - g2(z)),
        Bls12_381::pairing(c_s - g1(c.evaluate(&z)), G2::generator())
    );
    
}

#[test]
fn test_pairings() {
    let g1 = G1::generator();
    let g2 = G2::generator();
    let n3 = Scalar::from(3u64);
    let n4 = Scalar::from(4u64);
    let n5 = Scalar::from(5u64);
    let n12 = Scalar::from(12u64);

    // check ê(3,4) = ê(12,1)= sum e(1,1) 12 times = 12 * e(1,1)

    let gt_1 = Bls12_381::pairing(
        g1 * n3,
        g2 * n4,
    );
    let gt_2 = Bls12_381::pairing(g1 * n12, g2);

    let gt_3 = (0..11).fold(
        Bls12_381::pairing(g1, g2),
        |acc, _| acc + Bls12_381::pairing(g1, g2),
    );

    assert_eq!(gt_1, gt_2);
    assert_eq!(gt_1, gt_3);

    let gt_4 = Bls12_381::pairing(g1, g2).mul_bigint(&[12u64]);
    assert_eq!(gt_1, gt_4);

    // check paring multiplication 
    // ê(2,3) · ê(4,5) == ê(1,1)^(2*3 + 4*5)

}
