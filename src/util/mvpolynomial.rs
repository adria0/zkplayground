use ark_ff::{Field, Zero};
use ark_poly::multivariate::Term;
use ark_poly::DenseMVPolynomial;
use ark_poly::{
    multivariate::{SparsePolynomial, SparseTerm},
    univariate::DensePolynomial,
    DenseUVPolynomial, Polynomial,
};
use ark_std::One;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Display;
use std::ops::Mul;
use std::str::Chars;

use super::PolyToString;
use super::common::*;

const MPOLY_VARS: &str = "xyzwutsrqabcdefg";
const EXTVAR: char = 'v';

pub trait MVPolyUtils<F> {
    fn partial_eval(&self, evals: &[(usize, F)]) -> Self;
    fn var_degree(&self, var: usize) -> usize;
}


impl<F: Field + Display> PolyToString for SparsePolynomial<F, SparseTerm> {
    fn to_string(&self) -> String {
        multipoly_to_str(self)
    }
}

fn multipoly_to_str<F: Field + Display>(p: &SparsePolynomial<F, SparseTerm>) -> String {
    let mut s = String::new();
    for (f, term) in p.terms().iter().rev() {
        let pv = format!("{}", f);
        let nv = format!("{}", -*f);
        let (v, sign) = if pv.len() < nv.len() {
            (pv, '+')
        } else {
            (nv, '-')
        };
        if !s.is_empty() || sign == '-' {
            s.push(sign);
        }
        if v != "1" || term.is_empty() {
            s.push_str(&v);
        }
        for (var, power) in term.iter() {
            if let Some(ch) = MPOLY_VARS.chars().nth(*var) {
                s.push(ch);
            } else {
                s.push_str(&format!("{}{}", EXTVAR, var));
            }
            if *power > 1 {
                s.push('^');
                s.push_str(&format!("{}", power));
            }
        }
    }
    if s.is_empty() {
        "0".to_string()
    } else {
        s
    }
}



pub fn str_to_multipoly<F: Field + Display + One>(
    s: &str,
) -> Result<SparsePolynomial<F, SparseTerm>, &'static str> {
    let mut coeffs = vec![];

    let mut it = s.chars();
    let mut ch = it.next();

    let mut vars = HashSet::<usize>::new();
    let is_var = |ch: &char| MPOLY_VARS.contains(*ch) || ch == &EXTVAR;

    while ch.is_some() {
        let sign = match ch {
            Some('+') => {
                ch = it.next();
                F::ONE
            }
            Some('-') => {
                ch = it.next();
                -F::ONE
            }
            Some('0'..='9') => F::ONE,
            Some(ch) if is_var(&ch) => F::ONE,
            _ => unreachable!(),
        };

        let value = match ch {
            Some(ch) if is_var(&ch) => F::ONE,
            Some('0'..='9') => read_f(&mut it, &mut ch),
            _ => return Err("unable to parse value"),
        };

        let mut term = Vec::new();
        loop {
            let var = match ch {
                Some(c) if MPOLY_VARS.contains(c) => {
                    ch = it.next();
                    MPOLY_VARS.find(c).unwrap()
                }
                Some(c) if c == EXTVAR => {
                    ch = it.next();
                    read_usize(&mut it, &mut ch)
                }
                _ => break,
            };

            let exp = match ch {
                Some('^') => {
                    ch = it.next();
                    let exp = read_usize(&mut it, &mut ch);
                    if exp == 0 {
                        return Err("unable to parse coeff(1)");
                    }
                    exp
                }
                _ => 1,
            };
            vars.insert(var);
            term.push((var, exp));
        }

        coeffs.push((value * sign, SparseTerm::new(term)));
    }

    let num_vars = 1 + *vars.iter().max().unwrap_or(&0);

    Ok(SparsePolynomial::from_coefficients_vec(num_vars, coeffs))
}


impl<F: Field> MVPolyUtils<F> for SparsePolynomial<F, SparseTerm> {
    fn partial_eval(&self, evals: &[(usize, F)]) -> Self {
        let evals: HashMap<usize, F> = evals.iter().cloned().collect();

        // substitute
        let terms: Vec<(F, Vec<(usize, usize)>)> = self
            .terms
            .iter()
            .map(|(factor, vars)| {
                let mut factor = *factor;
                let mut new_vars = vec![];
                for (var, pow) in vars.iter() {
                    if let Some(value) = evals.get(var) {
                        factor *= value.pow([*pow as u64]);
                    } else {
                        new_vars.push((*var, *pow));
                    }
                }
                new_vars.sort_by(|a, b| format!("{}{}", a.0, a.1).cmp(&format!("{}{}", b.0, b.1)));
                (factor, new_vars)
            })
            .collect();

        let mut compact = BTreeMap::new();
        for (f, term) in terms {
            let entry = compact
                .entry(format!("{:?}", term))
                .or_insert((F::ZERO, SparseTerm::new(term)));
            entry.0 += f;
        }

        SparsePolynomial::from_coefficients_vec(self.num_vars, compact.into_values().collect())
    }
    fn var_degree(&self, var: usize) -> usize {
        self.terms
            .iter()
            .map(|(_, term)| {
                if let Some(var_pos) = term.vars().iter().position(|v| *v == var) {
                    term.powers()[var_pos]
                } else {
                    0
                }
            })
            .max()
            .unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::*;

    use ark_bn254::fr::Fr;
    use ark_poly::{multivariate::Term, univariate::DensePolynomial};
    use std::str::FromStr;

    fn n(s: &str) -> Fr {
        if let Some(s) = s.strip_prefix('-') {
            -Fr::from_str(s).unwrap()
        } else {
            Fr::from_str(s).unwrap()
        }
    }
    fn dp(coeffs: &[&str]) -> DensePolynomial<Fr> {
        let coeffs = coeffs.iter().map(|c| n(c)).collect::<Vec<_>>();
        DenseUVPolynomial::from_coefficients_vec(coeffs)
    }

    #[test]
    fn test_mpoly_to_str() {
        let poly = SparsePolynomial::from_coefficients_vec(
            3,
            vec![
                (Fr::from(2), SparseTerm::new(vec![(0, 3)])),
                (Fr::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
                (Fr::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
                (Fr::from(5), SparseTerm::new(vec![])),
            ],
        );
        assert_eq!("2x^3+xz+yz+5", poly.to_string());
    }

    #[test]
    fn test_str_to_mpoly() {
        let eq = |s: &str| assert_eq!(s, &str_to_multipoly::<Fr>(s).unwrap().to_string());
        eq("0");
        eq("1");
        eq("x");
        eq("xy");
        eq("v17");
        eq("xy+x-y");
        eq("yv18+x-y");
        eq("x^8y-y^2+x");
        eq("x^8y-y^2+x");
        eq("x^8yv16^11-y^2+x");
    }

    #[test]
    fn test_partial_eval() {
        let g: SparsePolynomial<Fr, SparseTerm> = mvpoly!("8x^3+xz+yz");

        let s0 = g.partial_eval(&[(0, Fr::from(2))]);
        assert_eq!(s0.to_string(), "yz+2z+64");

        let s1 = s0.partial_eval(&[(2, Fr::from(100))]);
        assert_eq!(s1.to_string(), "100y+264");

        let s2 = s1.partial_eval(&[(1, Fr::from(8))]);
        assert_eq!(s2.to_string(), "1064");
    }

}
