use crate::util::poly;

use super::util::{PolyToString, UniPolyUtils};
use crate::util::poly_i32;
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

// Notes:
// https://arnaucube.com/blog/kzg-commitments.html
// https://arnaucube.com/blog/powersoftau.html
// https://arnaucube.com/blog/kzg-batch-proof.html
// https://eprint.iacr.org/2019/953.pdf

struct SRS {
    g1s: Vec<G1>,
    g2s: Vec<G2>,
}

fn g1(s: Scalar) -> G1 {
    G1::generator() * s
}
fn g2(s: Scalar) -> G2 {
    G2::generator() * s
}

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
    fn evaluate_at_tau_g1(&self, p: &DensePolynomial<Scalar>) -> G1 {
        p.coeffs
            .iter()
            .zip(self.g1s.iter())
            .map(|(c, s)| s.mul_bigint(Into::<BigInt<4>>::into(*c)))
            .sum()
    }
    fn evaluate_at_tau_g2(&self, p: &DensePolynomial<Scalar>) -> G2 {
        p.coeffs
            .iter()
            .zip(self.g2s.iter())
            .map(|(c, s)| s.mul_bigint(Into::<BigInt<4>>::into(*c)))
            .sum()
    }

    pub fn commit(&self, p: &DensePolynomial<Scalar>) -> Commitment {
        Commitment(self.evaluate_at_tau_g1(&p))
    }

    // generate a proof that p(z) == y
    pub fn prove(&self, p: &DensePolynomial<Scalar>, z: Scalar) -> Proof<G1> {
        let y = p.evaluate(&z);
        let q = &(p - &DensePolynomial::from_coefficients_vec(vec![y]))
            / &DensePolynomial::from_coefficients_vec(vec![-z, Scalar::ONE]);
        Proof(self.evaluate_at_tau_g1(&q))
    }

    // verify p(z) == y
    pub fn verify(
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

            // F = 𝚺 γⁱ⁻¹ * cmₙ
            // v = [ 𝚺 γⁱ⁻¹ * sᵢ ]₁
    
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
    
            F = F + (blinded_commitments - g1(blinded_ys)) * r.pow(&[n as u64]);

            left = left + ( **proof * r.pow(&[n as u64]) * z );
            right = right + (**proof * r.pow(&[n as u64])); 
       }

        Bls12_381::pairing(F + left, g2(Scalar::from(1)))
            == Bls12_381::pairing(right, self.g2s[1])

    }

    // create a new contribution based on current SRS
    fn new_contribution(&self, new_tau: Scalar) -> (SRS, G1) {
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
    fn append_contribution(&mut self, contrib: (SRS, G1)) -> bool {
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
