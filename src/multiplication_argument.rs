use ark_bls12_381::{Bls12_381, Fr as Scalar, G1Projective as G1, G2Projective as G2};
use ark_ec::pairing::Pairing;
use ark_poly::{domain, univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial};
use std::ops::{Div, Rem, Sub};
use ark_ec::Group;
use ark_ff::{BigInt, Field, Zero};
use super::util::{UniPolyUtils, PolyToString};
use ark_ff::BigInteger;

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
                                    2. |Gen random z
                                       |  to avoid prover cheating 
                                       |< Send to prover
3. Compute
    qa(x) <- a(x)-a(z) / (x-z)
    qb(x) <- b(x)-b(z) / (x-z)
    qc(x) <- c(x)-c(z) / (x-z)
    | a(z), b(z), c(z)
    | π = ([qa(s)]₁, [qb(s)]₁, [qc(s)]₁]
    | > send to verifier

                                    4. Checks
                                       // check that qa(s) == 0 without revealing s ?
                                       ê([qa(s)]₁, [s-z]₂)  = ê([a(s)-a(z)]₁, [1]₂)
                                       ê([qb(s)]₁, [s-z]₂)  = ê([b(s)-b(z)]₁, [1]₂)
                                       ê([qc(s)]₁, [s-z]₂)  = ê([c(s)-c(z)]₁, [1]₂)
                                       a(z)b(z)-c(z) = Z(z)d(z)
                                       
note that:

ê([qa(s)]₁, [s-z]₂)
    = ê([a(s)-a(z) / (s-z)]₁, [s-z]₂)
    = ê([a(s)-a(z) * 1/(s-z)]₁, [s-z]₂) 
    = ê([a(s)-a(z)]₁, [(s-z) * (1/(s-z))]₂) 
    = ê([a(s)-a(z)]₁, [1]₂)

a(z)b(z)-c(z) = Z(z)d(z)
    ≡ a(z)b(z)-c(z) divides at Z(z))

comments:
    S -> V: must send [s-z]₂ ??
*/

#[test]
fn test_multiplication_argument() {

    let g1 = G1::generator();
    let g2 = G2::generator();

    fn poly(v: &[Scalar]) -> DensePolynomial<Scalar> {
        DensePolynomial::from_coefficients_vec(v.to_vec())
    }

    let domain = GeneralEvaluationDomain::<Scalar>::new(3).unwrap();
    let Z_x = domain.vanishing_polynomial();
    
    // domain[0] = 1
    // domain[1] = ω = 3465144826073652318776269530687742778270252468765361963008
    // domain[2] = ω² = 52435875175126190479447740508185965837690552500527637822603658699938581184512

    // evaluation domain here has 3 elements:       1,  ω, ω²
    let a = Evaluations::from_vec_and_domain([1,  2, 3].map(Scalar::from).into(), domain).interpolate();
    let b = Evaluations::from_vec_and_domain([4,  5, 6].map(Scalar::from).into(), domain).interpolate();    
    let c = Evaluations::from_vec_and_domain([4, 10,18].map(Scalar::from).into(), domain).interpolate();
    
    // check that a(x) * b(x) - c(x) == 0 for all x in domain
    let p = &a.naive_mul(&b) -  &c;    
    let (d,r) = p.divide_by_vanishing_poly(domain).unwrap();
    assert!(r.is_zero());

    // 1
    let s = Scalar::from(9);
    let a_s = g1 * a.evaluate(&s);
    let b_s = g1 * b.evaluate(&s);
    let c_s = g1 * c.evaluate(&s);

    let p_s = g1 * p.evaluate(&s);
    let d_s = g1 * d.evaluate(&s);

    // 2 
    let z = Scalar::from(2);

    // 3
    let x_minus_z = poly(&[-z, Scalar::from(1)]);
    let qa = &(&a - &poly(&[a.evaluate(&z)])) / &x_minus_z; 
    let qb = &(&b - &poly(&[b.evaluate(&z)])) / &x_minus_z; 
    let qc = &(&c - &poly(&[c.evaluate(&z)])) / &x_minus_z;

    let q_a_s = g1 * qa.evaluate(&s);
    let q_b_s = g1 * qb.evaluate(&s);
    let q_c_s = g1 * qc.evaluate(&s);

    // 4
    assert_eq!(
        Bls12_381::pairing(d_s, g2 * domain.vanishing_polynomial().evaluate(&s) ),
        Bls12_381::pairing(p_s, g2)
    );
    
    assert_eq!(
        Bls12_381::pairing(q_a_s, g2 * (s-z)),
        Bls12_381::pairing(a_s - g1*a.evaluate(&z), g2)
    );
    assert_eq!(
        Bls12_381::pairing(q_b_s, g2 * (s-z)),
        Bls12_381::pairing(b_s - g1*b.evaluate(&z), g2)
    );
    assert_eq!(
        Bls12_381::pairing(q_c_s, g2 * (s-z)),
        Bls12_381::pairing(c_s - g1*c.evaluate(&z), g2)
    );
    
}

#[test]
fn test_pairing() {
    let g1 = G1::generator();
    let g2 = G2::generator();

    let gt_1 = Bls12_381::pairing(
        g1 * Scalar::from(3u64),
        g2 * Scalar::from(4u64),
    );
    let gt_2 = Bls12_381::pairing(g1 * Scalar::from(12u64), g2);

    let gt_3 = (0..11).fold(
        Bls12_381::pairing(g1, g2),
        |acc, _| acc + Bls12_381::pairing(g1, g2),
    );

    assert_eq!(gt_1, gt_2);
    assert_eq!(gt_1, gt_3);
}
