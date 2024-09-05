use crate::util::*;

use ark_bls12_381::{g2, Bls12_381, Fr as Scalar, G1Projective as G1, G2Projective as G2};
use ark_ec::pairing::Pairing;
use ark_ec::Group;
use ark_ff::BigInteger;
use ark_ff::{BigInt, Field, Zero};
use ark_poly::{
    domain, univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations,
    GeneralEvaluationDomain, Polynomial,
};

use std::ops::{Deref, Div, Mul, Neg, Rem, Sub};

// https://arnaucube.com/blog/powersoftau.html

pub fn g1(s: Scalar) -> G1 {
    G1::generator() * s
}
pub fn g2(s: Scalar) -> G2 {
    G2::generator() * s
}

pub struct SRS {
    pub g1s: Vec<G1>,
    pub g2s: Vec<G2>,
}

impl SRS {
    pub fn new(tau: Scalar, k: u32) -> Self {
        let n = 2usize.pow(k);
        let mut g1s = Vec::with_capacity(n);
        let mut g2s = Vec::with_capacity(n);
        for i in 0..n {
            let tau_pow = tau.pow(&[i as u64]);
            g1s.push(g1(tau_pow));
            g2s.push(g2(tau_pow));
        }
        Self { g1s, g2s }
    }
    pub fn evaluate_at_tau_g1(&self, p: &DensePolynomial<Scalar>) -> G1 {
        p.coeffs
            .iter()
            .zip(self.g1s.iter())
            .map(|(c, s)| s.mul_bigint(Into::<BigInt<4>>::into(*c)))
            .sum()
    }
    pub fn evaluate_at_tau_g2(&self, p: &DensePolynomial<Scalar>) -> G2 {
        p.coeffs
            .iter()
            .zip(self.g2s.iter())
            .map(|(c, s)| s.mul_bigint(Into::<BigInt<4>>::into(*c)))
            .sum()
    }

    // create a new contribution based on current SRS
    pub fn new_contribution(&self, new_tau: Scalar) -> (SRS, G1) {
        // mainly multiplies previous srs by newτ⁰..newτⁿ
        // g1s: [τ*newτ]₁, [τ²*newτ²]₁, [τ³*newτ³]₁ , ...
        // g2s: [τ*newτ]₂, [τ²*newτ²]₂, [τ³*newτ³]₂ , ...
        // also returns [newτ]₂ to check the contribution

        let mut g1s = Vec::with_capacity(self.g1s.len());
        let mut g2s = Vec::with_capacity(self.g2s.len());
        for i in 0..self.g1s.len() {
            let tau_pow = new_tau.pow(&[i as u64]);
            g1s.push(self.g1s[i] * tau_pow);
            g2s.push(self.g2s[i] * tau_pow);
        }

        (Self { g1s, g2s }, g1(new_tau))
    }    

    // append a contributin to the current SRS
    pub fn append_contribution(&mut self, contrib: (SRS, G1)) -> bool {
        let (new_srs, new_tau_g2) = contrib;

        assert_eq!(self.g1s.len(), new_srs.g2s.len());

        // Check that does not contains any zero.
        for g1e in &new_srs.g1s {
            if g1e.is_zero() {
                return false;
            }
        }
        for g2e in &new_srs.g2s {
            if g2e.is_zero() {
                return false;
            }
        }

        // Check that the new SRS is correctly related to the previous one.
        // We know that current SRS.g1s[1] contains [τ]₁ and new SRS.g1s contains [τ*newτ]₁
        // So ê([τ*newτ)]₁,[1]₂)=ê([newτ]₁,[τ]₂).

        let correctlly_related = Bls12_381::pairing(new_srs.g1s[1], g2(Scalar::from(1)))
            == Bls12_381::pairing(new_tau_g2, self.g2s[1]);

        if !correctlly_related {
            return false;
        }

        // Check that G1 and G2 sequence is ok.
        //   [τ*newτ]₁, [(τ*newτ)²]₁, [(τ*newτ)³]₁ , ...
        //   ê([τ*newτ]₁,[τ*newτ]₂) == ê([(τ*newτ)²]₁,[1]₂) == ê([1]₁,[(τ*newτ)²]₂)

        for i in 0..self.g1s.len() - 1 {
            let curr = Bls12_381::pairing(new_srs.g1s[i], new_srs.g2s[1]);
            let next_g1 = Bls12_381::pairing(new_srs.g1s[i + 1], g2(Scalar::from(1)));
            let next_g2 = Bls12_381::pairing(g1(Scalar::from(1)), new_srs.g2s[i + 1]);

            if curr != next_g1 || curr != next_g2 {
                return false;
            }
        }

        *self = new_srs;

        true
    }
}

#[test]
fn kzg_test() {
    let k: u32 = 3;

    // create a new SRS with tau = 32
    let mut srs = SRS::new(Scalar::from(32), k);

    // add a contribution to SRS with tau = 56
    let contrib = srs.new_contribution(Scalar::from(56));

    // accept contribution
    assert!(srs.append_contribution(contrib));
}
