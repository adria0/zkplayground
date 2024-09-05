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
use super::srs::{SRS, g1, g2};

// Notes:
// https://arnaucube.com/blog/kzg-commitments.html
// https://arnaucube.com/blog/powersoftau.html
// https://arnaucube.com/blog/kzg-batch-proof.html
// https://eprint.iacr.org/2019/953.pdf

#[derive(Clone, Debug)]
struct Commitment(G1);
impl Deref for Commitment {
    type Target = G1;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug)]
struct Proof<T>(T);
impl<T> Deref for Proof<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug)]
struct VerifyOpenings {
    // where to open
    z: Scalar,
    // commitments to polys
    commitments: Vec<Commitment>,
    // openings
    y: Vec<Scalar>, 
    // Proof
    proof: Proof<G1>, 
}

trait KZG {

    // commit a polynomial 
    fn commit(&self, p: &DensePolynomial<Scalar>) -> Commitment;
    
    // generate a proof that p(z) == y
    fn prove(&self, p: &DensePolynomial<Scalar>, z: Scalar) -> Proof<G1>;

    // verify p(z) == y
    fn verify(
        &self,
        proof: &Proof<G1>,
        commitment: &Commitment,
        point: (Scalar, Scalar),
    ) -> bool;

    // prove a set of points
    fn prove_point(&self, p: &DensePolynomial<Scalar>, zetas: &[Scalar]) -> Proof<G1>;

    // verify a set of points
    fn verify_points(
        &self,
        proof: &Proof<G1>,
        commitment: &Commitment,
        points: &[(Scalar, Scalar)],
    ) -> bool;

    fn prove_openings(
        &self,
        polys: &[DensePolynomial<Scalar>],
        gamma: &Scalar,
        z: &Scalar,
    ) -> Proof<G1>;

    // verify that fₙ(z)=sₙ
    fn verify_openings(
        &self,
        vo : VerifyOpenings,
        gamma: &Scalar,
    ) -> bool;

        // See https://eprint.iacr.org/2019/953.pdf
    fn verify_openings_batched (
        &self,
        vos: &[VerifyOpenings],
        gamma: &Scalar,
        r: &Scalar
    ) -> bool;

}

impl KZG for SRS {
    fn commit(&self, p: &DensePolynomial<Scalar>) -> Commitment {
        Commitment(self.evaluate_at_tau_g1(&p))
    }

    // generate a proof that p(z) == y
    fn prove(&self, p: &DensePolynomial<Scalar>, z: Scalar) -> Proof<G1> {
        let y = p.evaluate(&z);
        let q = &(p - &DensePolynomial::from_coefficients_vec(vec![y]))
            / &DensePolynomial::from_coefficients_vec(vec![-z, Scalar::ONE]);
        Proof(self.evaluate_at_tau_g1(&q))
    }

    // verify p(z) == y
    fn verify(
        &self,
        proof: &Proof<G1>,
        commitment: &Commitment,
        point: (Scalar, Scalar),
    ) -> bool {
        // ê(π,[τ]₂-[z]₂) = ê(c-[y]₁,[0]₂)
        // ê([q(τ)]₁,[τ-z]₂) = ê([p(τ)]₁-[y]₁,[0]₂)
        // ê([p(τ)-y * 1/(τ-z)]₁,[τ-z]₂) = ê([p(τ)-y]₁,[0]₂)
        // ê([p(τ)-y]₁ ,[0]₂) = ê([p(τ)-y]₁,[0]₂)

        let (z, y) = point;
        Bls12_381::pairing(**proof, self.g2s[1] - g2(z))
            == Bls12_381::pairing(**commitment - g1(y), self.g2s[0])
    }

    // prove a set of points
    fn prove_point(&self, p: &DensePolynomial<Scalar>, zetas: &[Scalar]) -> Proof<G1> {
        let ys = zetas.iter().map(|z| p.evaluate(&z)).collect::<Vec<_>>();
        let points = zetas
            .to_vec()
            .into_iter()
            .zip(ys.into_iter())
            .collect::<Vec<_>>();

        let lagrange = DensePolynomial::lagrange(&points);
        let vanishing = DensePolynomial::vanishing(points.iter().map(|(z, _)| *z));

        let q = &(p - &lagrange) / &vanishing; // panics if remanider is not zero
        Proof(self.evaluate_at_tau_g1(&q))
    }

    // check a set of points
    fn verify_points(
        &self,
        proof: &Proof<G1>,
        commitment: &Commitment,
        points: &[(Scalar, Scalar)],
    ) -> bool {
        let vanishing = DensePolynomial::vanishing(points.iter().map(|(z, _)| *z));
        let lagrange = DensePolynomial::lagrange(points);

        let lagrange_at_tau = self.evaluate_at_tau_g1(&lagrange);
        let vanishing_at_tau = self.evaluate_at_tau_g2(&vanishing);

        Bls12_381::pairing(**proof, vanishing_at_tau)
            == Bls12_381::pairing(**commitment - lagrange_at_tau, self.g2s[0])
    }

    // prove that fₙ(z)=sₙ
    // taken from PLONK paper
    // notes:
    //     x in paper is τ here
    //     s in paper is y here
    //     W in paper if proof here
    fn prove_openings(
        &self,
        polys: &[DensePolynomial<Scalar>],
        gamma: &Scalar,
        z: &Scalar,
    ) -> Proof<G1> {
        // return
        let mut sum = DensePolynomial::zero();

        for (n, poly) in polys.iter().enumerate() {
            //  𝚺 γⁱ⁻¹ * ( pᵢ(x) - pᵢ(z) ) ( x - z )
            let eval: DensePolynomial<_> = (&(poly
                - &DensePolynomial::from_coefficients_vec(vec![poly.evaluate(&z)]))
                / &DensePolynomial::from_coefficients_vec(vec![-*z, Scalar::ONE]));

            sum = sum + &eval * gamma.pow(&[n as u64]);
        }
        Proof(self.evaluate_at_tau_g1(&sum))
    }

    // verify that fₙ(z)=sₙ
    fn verify_openings(
        &self,
        vo : VerifyOpenings,
        gamma: &Scalar,
    ) -> bool {

        let VerifyOpenings { proof, commitments, z, y } = vo;

        // F = 𝚺 γⁱ⁻¹ * cmₙ
        // v = [ 𝚺 γⁱ⁻¹ * sᵢ ]₁

        let blinded_commitments: G1 = commitments
            .iter()
            .enumerate()
            .map(|(n, c)| **c * gamma.pow(&[n as u64]))
            .sum();


        let blinded_ys = y
            .iter()
            .enumerate()
            .map(|(n, y)| y * &gamma.pow(&[n as u64]))
            .sum();

            let f_minus_v = blinded_commitments - g1(blinded_ys);

        Bls12_381::pairing(*proof, self.g2s[1] - g2(z))
            == Bls12_381::pairing(blinded_commitments - g1(blinded_ys), self.g2s[0])
    }

    // See https://eprint.iacr.org/2019/953.pdf
    fn verify_openings_batched (
        &self,
        vos: &[VerifyOpenings],
        gamma: &Scalar,
        r: &Scalar
    ) -> bool {

        let mut F = G1::zero();
        let mut left = G1::zero();
        let mut right = G1::zero();

        for (n,vo) in vos.iter().enumerate() {

            let VerifyOpenings { proof, commitments, z, y } = vo;

            let blinded_commitments: G1 = commitments
                .iter()
                .enumerate()
                .map(|(i, c)| **c * gamma.pow(&[i as u64]))
                .sum();
    
            let blinded_ys : Scalar = y
                .iter()
                .enumerate()
                .map(|(i, y)| y * &gamma.pow(&[i as u64]))
                .sum();

            let r_pow_n = r.pow(&[n as u64]); 
    
            F = F + (blinded_commitments - g1(blinded_ys)) * r_pow_n;

            left = left + ( **proof * r_pow_n * z );
            right = right + (**proof * r_pow_n); 
       }

        Bls12_381::pairing(F + left, g2(Scalar::from(1)))
            == Bls12_381::pairing(right, self.g2s[1])

    }

}

#[test]
fn kzg_test() {
    let k: u32 = 3;

    // create a new SRS with tau = 32
    let mut srs = SRS::new(Scalar::from(32), k);

    // polynomial to commit
    let p: DensePolynomial<Scalar> = poly!("5x^2+3x");
    // generate commit
    let p_commitment = srs.commit(&p);
    let z = Scalar::from(2u32);
    let y = p.evaluate(&z);

    {
        // verify proof
        let proof = srs.prove(&p, z);
        assert!(srs.verify(&proof, &p_commitment, (z, y)));

        // check bad proof
        assert!(!srs.verify(&proof, &p_commitment, (z, y + Scalar::from(1))));
    }
    {
        let z2 = Scalar::from(3u32);
        let y2 = p.evaluate(&z2);

        let proof = srs.prove_point(&p, &[z, z2]);

        // verify batched proof
        assert!(srs.verify_points(&proof, &p_commitment, &[(z, y), (z2, y2)]));
    }
    {
        let p2: DensePolynomial<Scalar> = poly!("15x^3+9x");
        let p2_commitment = srs.commit(&p2);

        let gamma = Scalar::from(77);
        let proof = srs.prove_openings(&[p.clone(), p2.clone()], &gamma, &z);

        // verify ok
        assert!(srs.verify_openings(
            VerifyOpenings {
                proof,
                commitments: vec![p_commitment.clone(), p2_commitment],
                z,
                y: vec![p.evaluate(&z), p2.evaluate(&z)]
            },
            &gamma,
        ));
    }
    {
        let gamma = Scalar::from(77);
        let r = Scalar::from(66);

        let p2: DensePolynomial<Scalar> = poly!("15x^3+9x");
        let p2_commitment = srs.commit(&p2);
        let proof = srs.prove_openings(&[p.clone(), p2.clone()], &gamma, &z);

        let verify_openings = VerifyOpenings {
            proof,
            commitments: vec![p_commitment, p2_commitment],
            z,
            y: vec![p.evaluate(&z), p2.evaluate(&z)]
        };

        let p3: DensePolynomial<Scalar> = poly!("115x^3");
        let p3_commitment = srs.commit(&p3);
        let p4: DensePolynomial<Scalar> = poly!("115x^2");
        let p4_commitment = srs.commit(&p4);
        let p5: DensePolynomial<Scalar> = poly!("115x");
        let p5_commitment = srs.commit(&p5);
        let z2 = Scalar::from(177u32);

        let proof2 = srs.prove_openings(&[p3.clone(), p4.clone(), p5.clone()], &gamma, &z2);

        let verify_openings_2 = VerifyOpenings {
            proof: proof2,
            commitments: vec![p3_commitment, p4_commitment, p5_commitment],
            z: z2,
            y: vec![p3.evaluate(&z2), p4.evaluate(&z2), p5.evaluate(&z2)]
        };

        // verify ok
        assert!(srs.verify_openings_batched(
            &[verify_openings.clone()],
            &gamma,
            &r
        ));
        assert!(srs.verify_openings_batched(
            &[verify_openings_2.clone()],
            &gamma,
            &r
        ));
        assert!(srs.verify_openings_batched(
            &[verify_openings, verify_openings_2],
            &gamma,
            &r
        ));
    }

}
