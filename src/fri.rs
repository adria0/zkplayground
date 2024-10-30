use crate::util::*;

use ark_ff::{Field, Fp64, MontBackend, MontConfig};

use ark_poly::{Polynomial, univariate::DensePolynomial};
use blake2::{Blake2b512, Blake2s256, Digest};
use rand::prelude::*;


type Scalar = ark_bn254::fr::Fr;

// FRI is a protocol that establishes that a committed polynomial has a bounded degree.

/* 
// split even and odd powers
// p(x) = g(x^2) + x h(x^2)
// meaning that both g and h are polynomials of half the degree of p
fn split_poly<F: Field>(p: &DensePolynomial<F>) -> (DensePolynomial<F>, DensePolynomial<F>) {
    let x = poly!("x");
    let x_pow_2 = poly!("x^2");

    let g_coeffs = p
        .coeffs
        .iter()
        .enumerate()
        .filter_map(|(i, n)| if i % 2 == 0 { Some(*n) } else { None });

    let h_coeffs = p
        .coeffs
        .iter()
        .enumerate()
        .filter_map(|(i, n)| if i % 2 == 1 { Some(*n) } else { None });

    let g = DensePolynomial {
        coeffs: g_coeffs.collect(),
    };
    let h = DensePolynomial {
        coeffs: h_coeffs.collect(),
    };

    // sanity check that H(x) = H_1(x^2) + x·H_2(x^2)
    assert_eq!(
        p.clone(),
        g.compose(&x_pow_2.clone()) + x.naive_mul(&h.compose(&x_pow_2.clone()))
    );

    (g, h)
}

struct FriCommitment<F: Field>{
    last : F,
    g_h_s : Vec<(DensePolynomial<F>, DensePolynomial<F>)>
}

impl<F: Field> FriCommitment<F> {
    fn commit(p: DensePolynomial<F>, betas: &[F]) -> Self {
        let mut g_h_s = vec![];
        let mut p = p;
        let mut betas = betas.iter();
    
        while p.coeffs.len() > 1 {
            let (g,h) = split_poly(&p);
    
            //      p(x)  = g(x^2) + x h(x^2) 
            // also p(-x) = g(x^2) - x h(x^2) 
    
            g_h_s.push((g.clone(),h.clone()));
    
            let b : F = *betas.next().unwrap();
    
            p = g + &h * b;
        }

        Self {
            last : p.coeffs[0],
            g_h_s
        }
    }


    fn print(&self) {
        for (i,(g,h)) in self.g_h_s.iter().enumerate() {
            println!("{}.g={}", i, g.to_string());
            println!("{}.h={}", i, h.to_string());
         }
         println!("last={}", self.last.to_string());
    } 

}
*/

#[derive(Debug)]
struct FriCommitment<F: Field>(Vec<(F, F)>);

impl<F: Field> FriCommitment<F> {
    fn commit<R: Rng>(mut poly: DensePolynomial<F>, domain: &[F], rng: &mut R) -> Self
    {
        let codewords : Vec<F> = domain.iter().map(|x| poly.evaluate(x)).collect();

        let query = rng.next_u64() as usize;

        let mut evals = Vec::new();
        let mut layer = 0usize;

        while poly.degree() > 0 {
            // index folding
            let x = domain[((query % (domain.len() >> layer)) << layer)];
            dbg!(x);
            evals.push((poly.evaluate(&x), poly.evaluate(&-x)));

            let mut g_x2 = vec![];
            let mut h_x2 = vec![];            

            for (i, coeff) in poly.coeffs.iter().enumerate() {
                if i % 2 == 0 {
                    g_x2.push(*coeff);
                } else {
                    h_x2.push(*coeff);
                }
            }

            let g_x2 = DensePolynomial { coeffs : g_x2 } ;
            
            let beta = F::rand(rng);
            h_x2.iter_mut().for_each(|coeff| *coeff *= beta);
            let h_x2 = DensePolynomial { coeffs : h_x2 };

            poly = g_x2 + h_x2;

            layer += 1;
        }

        // Write the "root" of the tree
        let x = domain[((query % (domain.len() >> layer)) << layer)];
        evals.push((poly.evaluate(&x), F::zero()));

        Self ( evals )
    }

    // Verify that a commitment is low degree
    fn verify<R: Rng>(&self, domain: &[F], rng: &mut R) -> bool
    {
        let two = F::ONE + F::ONE;
        let query = rng.next_u64() as usize;

        for layer in 0..self.0.len() - 1 {
            let x = domain[((query % (domain.len() >> layer)) << layer)];
            dbg!(x);

            let beta = F::rand(rng);
            let check = ((beta + x) / (x * two)) * self.0[layer].0
                + ((beta - x) / (-x * two)) * self.0[layer].1;

            println!("check={}", check);
            println!("layer={}", self.0[layer + 1].0);
            
            if self.0[layer + 1].0 != check {
                return false;
            }
        }

        true
    }
}



#[cfg(test)]
mod test {

    #[derive(MontConfig)]
    #[modulus = "17"]
    #[generator = "3"]
    pub struct FqConfig;
    pub type Fq = Fp64<MontBackend<FqConfig, 1>>;
   
    use super::*;
    use ark_ff::{fields::{Field, Fp64, MontBackend, MontConfig}, Fp256};
    use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain};
    use rand::prelude::*;
    
    #[test]
    fn fri() {
        let new_rng = || rand_xorshift::XorShiftRng::seed_from_u64(0x12345);

        let domain = GeneralEvaluationDomain::<Fq>::new(8).unwrap();
        let domain_elements = domain.elements().collect::<Vec<_>>();
        let mut rng = new_rng();
        
        let poly = DensePolynomial::<Fq>::rand(6, &mut rng);
        
        let mut rng = new_rng();
        let commitment = FriCommitment::commit(poly, &domain_elements, &mut rng);
        
        let mut rng = new_rng();
        assert!(commitment.verify(&domain_elements, &mut rng));
    }
/* 
    #[test]
    fn test_fri() {
        use crate::util::*;
        use ark_poly::{DenseMVPolynomial, Polynomial};

        type F = ark_bn254::fr::Fr;

        let p: DensePolynomial<F> = poly!("5x^5+3x^4+7x^3+2x^2+x+3");

        let commitment = FriCommitment::commit(p, &[F::from(3), F::from(5), F::from(7)]);
        commitment.print();
    }
    */
}