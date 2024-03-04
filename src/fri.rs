use crate::util::{poly, UniPolyUtils, PolyToString};
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;

type Scalar = ark_bn254::fr::Fr;

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


#[test]
fn test_fri() {
    use crate::util::{poly, UniPolyUtils, *};
    use ark_poly::{DenseMVPolynomial, Polynomial};

    type F = ark_bn254::fr::Fr;

    let p: DensePolynomial<F> = poly!("5x^5+3x^4+7x^3+2x^2+x+3");

    let commitment = FriCommitment::commit(p, &[F::from(3), F::from(5), F::from(7)]);
    commitment.print();


}
