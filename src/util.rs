#![allow(unused)]

use ark_ff::Field;
use ark_poly::multivariate::Term;
use ark_poly::DenseMVPolynomial;
use ark_poly::{
    multivariate::{SparsePolynomial, SparseTerm},
    univariate::DensePolynomial,
    DenseUVPolynomial,
};
use ark_std::One;
use std::collections::{HashSet, HashMap, BTreeMap};
use std::fmt::Display;
use std::str::Chars;

const MPOLY_VARS: &str = "xyzwutsrqabcdefg";
const EXTVAR: char = 'v';

pub trait PolyToString {
    fn to_string(&self) -> String;
}

impl<F: Field + Display> PolyToString for DensePolynomial<F> {
    fn to_string(&self) -> String {
        unipoly_to_str(self)
    }
}

impl<F: Field + Display> PolyToString for SparsePolynomial<F, SparseTerm> {
    fn to_string(&self) -> String {
        multipoly_to_str(self)
    }
}

macro_rules! poly {
    ($s:expr) => {
        crate::util::str_to_unipoly($s).expect("unable to parse poly")
    };
}
macro_rules! mpoly {
    ($s:expr) => {
        crate::util::str_to_multipoly($s).expect("unable to parse multipoly")
    };
}

pub(crate) use mpoly;
pub(crate) use poly;

fn unipoly_to_str<F: Field + Display>(p: &DensePolynomial<F>) -> String {
    let mut s = String::new();
    for (n, coeff) in p.coeffs().iter().enumerate().rev() {
        if coeff.is_zero() {
            continue;
        }
        let pv = format!("{}", coeff);
        let nv = format!("{}", -*coeff);
        let (v, sign) = if pv.len() < nv.len() {
            (pv, '+')
        } else {
            (nv, '-')
        };
        if !s.is_empty() || sign == '-' {
            s.push(sign);
        }
        if v != "1" || n == 0 {
            s.push_str(&v);
        }
        if n >= 1 {
            s.push('x');
        }
        if n >= 2 {
            s.push_str(&format!("^{}", n));
        }
    }
    if s.is_empty() {
        "0".to_string()
    } else {
        s
    }
}

fn read_f<F: Field>(it: &mut Chars, ch: &mut Option<char>) -> F {
    let digits: Vec<_> = std::iter::successors(Some(F::ZERO), |v| Some(*v + F::ONE))
        .take(10)
        .collect();

    let ten = digits[9] + F::ONE;

    let mut value = F::ZERO;
    while matches!(*ch, Some('0'..='9')) {
        value = ten * value + digits[(ch.unwrap() as usize) - ('0' as usize)];
        *ch = it.next();
    }
    value
}

fn read_usize(it: &mut Chars, ch: &mut Option<char>) -> usize {
    let mut value = 0;
    while matches!(*ch, Some('0'..='9')) {
        value = 10 * value + (ch.unwrap() as usize) - ('0' as usize);
        *ch = it.next();
    }
    value
}

pub fn str_to_unipoly<F: Field + Display>(s: &str) -> Result<DensePolynomial<F>, &'static str> {
    let mut coeffs = vec![];

    let mut it = s.chars();
    let mut ch = it.next();

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
            Some('x') => F::ONE,
            _ => unreachable!(),
        };
        let value = match ch {
            Some('x') => F::ONE,
            Some('0'..='9') => read_f(&mut it, &mut ch),
            _ => return Err("unable to parse value"),
        };
        let coeff = match ch {
            None => 0,
            Some('x') => {
                ch = it.next();
                if Some('^') == ch {
                    ch = it.next();
                    let exp = read_usize(&mut it, &mut ch);
                    if exp == 0 {
                        return Err("unable to parse coeff(1)");
                    }
                    exp
                } else {
                    1
                }
            }
            _ => return Err("Unable to parse coeff(2)"),
        };
        if coeffs.len() < coeff + 1 {
            coeffs.extend(std::iter::repeat(F::ZERO).take(coeff - coeffs.len() + 1));
        }
        coeffs[coeff] += sign * value;
    }

    Ok(DensePolynomial::from_coefficients_vec(coeffs))
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

// this function partially evaluates a polinomial
pub fn partial_poly_eval<F: Field>(mpoly: &SparsePolynomial<F, SparseTerm>, evals: &[(usize, F)]) -> SparsePolynomial<F, SparseTerm> {

    let evals : HashMap<usize,F> = evals.iter().cloned().collect();

    // substitute
    let terms: Vec<(F, Vec<(usize, usize)>)> = mpoly
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

    SparsePolynomial::from_coefficients_vec(mpoly.num_vars, compact.into_values().collect())
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn test_poly_to_str() {
        let eq = |s: &str, coeffs: &[&str]| assert_eq!(s, dp(coeffs).to_string());
        eq("0", &["0"]);
        eq("1", &["1"]);
        eq("-1", &["-1"]);
        eq("-x", &["0", "-1"]);
        eq("-x^2", &["0", "0", "-1"]);
        eq("-x^2-1", &["-1", "0", "-1"]);
        eq("-x^2+2x-1", &["-1", "2", "-1"]);
    }

    #[test]
    fn test_str_to_poly() {
        let eq = |s: &str| assert_eq!(s, &str_to_unipoly::<Fr>(s).unwrap().to_string());
        eq("0");
        eq("1");
        eq("-1");
        eq("-x");
        eq("x-2");
        eq("2x");
        eq("200x");
        eq("200x^200");
        eq("-200x");
        eq("-200x^2");
        eq("-x^2+2x+1");
        eq("-x^2+2x-1");
        eq("x^25-8x^2+1552x-1");
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
        let g: SparsePolynomial<Fr, SparseTerm> = mpoly!("8x^3+xz+yz");

        let s0 = partial_poly_eval(&g, &[(0, Fr::from(2))]);
        assert_eq!(s0.to_string(), "yz+2z+64");

        let s1 = partial_poly_eval(&s0, &[(2, Fr::from(100))]);
        assert_eq!(s1.to_string(), "100y+264");

        let s2 = partial_poly_eval(&s1, &[(1, Fr::from(8))]);
        assert_eq!(s2.to_string(), "1064");
    }

}
