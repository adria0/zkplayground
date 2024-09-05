use std::{fmt::Debug, mem::MaybeUninit};

// https://www.youtube.com/watch?v=Bl5mQA7UL2I
//

trait Field : Sized + Clone + Debug{
    const SIZE : usize;
    fn add(&self, other: &Self) -> Self;
    fn add_assign(&mut self, other: &Self);
    fn mul(&self, other: &Self) -> Self;
    fn mul_assign(&mut self, other: &Self);
    fn divmod(&self, other: u64) -> (Self, Self);
    fn is_zero(&self) -> bool;
    fn from_u64(n: u64) -> Self;
    fn as_u64(&self) -> u64;
    fn zero() -> Self;
    fn one() -> Self;
    fn two() -> Self;
}

impl Field for u64 {  
    const SIZE : usize = 64;  
    fn add(&self, other: &Self) -> Self {
        self + other
    }
    fn add_assign(&mut self, other: &Self) {
        *self += other;
    }
    fn mul(&self, other: &Self) -> Self {
       self * other
    }
    fn mul_assign(&mut self, other: &Self) {
        *self *= other;
    }
    fn divmod(&self, other: u64) -> (Self, Self) {
        (self / other, self % other) 
    }
    fn as_u64(&self) -> u64 {
        *self
    }
    fn from_u64(n: u64) -> Self {
        n
    }

    fn zero() -> Self {
        0
    }

    fn one() -> Self {
        1
    }

    fn two() -> Self {
        2
    }
    fn is_zero(&self) -> bool {
        *self == 0
    }
}


fn double_and_add<F: Field>(mut s: F, g: F) -> F {
    let mut r = F::zero();
    let mut temp = g;
    while !s.is_zero() {
        let (s_div, s_mod) = s.divmod(2);
        if !s_mod.is_zero() {
            r.add_assign(&temp);
        }
        temp.mul_assign(&F::two());
        s = s_div;
    }
    r
}

fn msm_double_and_add<F: Field>(n: &[F], g: &[F]) -> F {
    n.iter()
        .zip(g.iter())
        .map(|(s, g)| double_and_add(s.clone(), g.clone()))
        .fold(F::zero(), |acc, x| acc.add(&x))
}

fn msm_bucket_reduced<F: Field>(n: &[F], g: &[F], buckets: usize) -> F {
    let mut buckets = vec![F::zero(); buckets];

    // Append into buckets
    for i in 0..g.len() {
        buckets[n[i].as_u64() as usize].add_assign(&g[i]);
    }

    // Sum buckets
    let mut sum = F::zero();
    let mut acc = F::zero();
    for s in buckets.iter().skip(1).rev() {
        acc.add_assign(s);
        sum.add_assign(&acc);
    }

    sum
}

fn scalar_limbs<const LIMBS: usize, F: Field>(mut s: F) -> [F; LIMBS]{
    let size = 2u64.pow((F::SIZE / LIMBS) as u32);
    let mut ret = [();LIMBS].map(|_| F::zero());

    for bucket in 0..LIMBS {
        let (s_div, s_mod) = s.divmod(size);
        ret[bucket] = s_mod;
        s = s_div;
    }
    ret
}

fn msm_bucket<F: Field>(n: &[F], g: &[F]) -> F {
    assert_eq!(F::SIZE, 64, "Only works for 64 bit fields");
    
    const FIELD_BITS : usize = 64;
    const BITS_PER_LIMB : usize = 16;
    const NUM_LIMBS : usize = FIELD_BITS / BITS_PER_LIMB;

    // partition scalars
    let n_limbs : Vec<[_;NUM_LIMBS]> = n.iter().map(|n| scalar_limbs::<NUM_LIMBS, _>(n.clone())).collect();

    // compute the MSM for each the limbs
    let mut msm_per_limb = [();NUM_LIMBS].map(|_| F::zero());

    for limb in 0..NUM_LIMBS {
        let scalars_limb : Vec<_> = n_limbs.iter().map(|c| c[limb].clone()).collect();
        let num_buckets = 2usize.pow(BITS_PER_LIMB as u32);
        msm_per_limb[limb] = msm_bucket_reduced::<F>(&scalars_limb, &g, num_buckets );
    }

    // combine MSM
    let mut t = msm_per_limb[NUM_LIMBS - 1].clone();
    for j in 1..NUM_LIMBS {
        // double c times
        for _ in 0..BITS_PER_LIMB {
            t.add_assign(&t.clone());
        }   
        t.add_assign(&msm_per_limb[NUM_LIMBS - j -1])
    }

    t

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_msm_double_and_add() {
        // 1 1 0
        //

        assert_eq!(double_and_add(6, 2), 6 * 2);
        assert_eq!(msm_double_and_add(&[6, 7], &[8, 9]), 6 * 8 + 7 * 9);
        //biits(1368, 4);
    }


    #[test]
    fn test_bucket_reduced() {
        let g: [u64; 14] = [7, 8, 9, 11, 6, 5, 4, 2, 6, 5, 4, 1, 9, 1];
        let n: [u64; 14] = [6, 2, 6, 1, 7, 2, 3, 5, 1, 4, 6, 7, 3, 1];

        assert_eq!(msm_bucket_reduced::<_>(&n, &g, 8), msm_double_and_add(&n, &g));
        assert_eq!(msm_bucket::<_>(&n, &g), msm_double_and_add(&n, &g));

    }

    #[test]
    fn test_partition_scalar() {
        let partition = scalar_limbs::<16,_>(0x176Au64);
        assert_eq!(partition, [0xa, 6, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn test_bucket() {
        let g: [u64; 3] = [7, 8, 4];
        let n: [u64; 3] = [0x1FFFF, 0x176Au64, 0x1763ffaaf9391u64];

        assert_eq!(msm_bucket::<_>(&n, &g), msm_double_and_add(&n, &g));
    }

}
