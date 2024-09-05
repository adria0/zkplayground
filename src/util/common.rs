#![allow(unused)]

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

pub fn read_f<F: Field>(it: &mut Chars, ch: &mut Option<char>) -> F {
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

pub fn read_usize(it: &mut Chars, ch: &mut Option<char>) -> usize {
    let mut value = 0;
    while matches!(*ch, Some('0'..='9')) {
        value = 10 * value + (ch.unwrap() as usize) - ('0' as usize);
        *ch = it.next();
    }
    value
}
