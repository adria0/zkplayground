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

mod common;
pub mod polynomial;
pub mod mvpolynomial;

pub trait PolyToString {
    fn to_string(&self) -> String;
}

macro_rules! poly {
    ($s:expr) => {
        crate::util::polynomial::str_to_unipoly($s).expect("unable to parse poly")
    };
}

macro_rules! mvpoly {
    ($s:expr) => {
        crate::util::mvpolynomial::str_to_multipoly($s).expect("unable to parse multipoly")
    };
}
pub(crate) use poly;
pub(crate) use mvpoly;

pub use polynomial::{PolyUtils, PolyUtilsI32};
pub use mvpolynomial::MVPolyUtils;
