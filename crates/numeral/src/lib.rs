//! Arbitrary-precision natural numerals (`docs/wide-numerals-design.md`).
//!
//! One type shared by the lexer, the AST, the elaborator and the kernel, so
//! that a numeral is the number it spells at every stage. It is in the
//! kernel's trusted base (`Term::NatLit` carries it), and what the kernel
//! relies on is small: [`Numeral::is_zero`], [`Numeral::pred`] of a nonzero
//! value, and [`Numeral::limbs`]. There is deliberately no arithmetic beyond
//! what reading and presenting a literal needs: computing is the kernel's
//! business, on its own values.

use std::cmp::Ordering;
use std::fmt;
use std::sync::Arc;

/// A natural number of any size.
///
/// Invariant: `Big` exactly when the value exceeds `u64::MAX`, with at least
/// two little-endian limbs and a nonzero top limb. Every constructor goes
/// through [`Numeral::from_limbs`], so equality, hashing and order may be
/// structural.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Numeral(Repr);

#[derive(Clone, PartialEq, Eq, Hash)]
enum Repr {
    Small(u64),
    Big(Arc<[u64]>),
}

impl Numeral {
    pub const ZERO: Numeral = Numeral(Repr::Small(0));

    pub const fn from_u64(n: u64) -> Numeral {
        Numeral(Repr::Small(n))
    }

    pub fn from_u128(n: u128) -> Numeral {
        Numeral::from_limbs(vec![n as u64, (n >> 64) as u64])
    }

    /// From little-endian limbs, normalized.
    pub fn from_limbs(mut limbs: Vec<u64>) -> Numeral {
        while limbs.len() > 1 && limbs.last() == Some(&0) {
            limbs.pop();
        }
        match limbs.len() {
            0 => Numeral::ZERO,
            1 => Numeral(Repr::Small(limbs[0])),
            _ => Numeral(Repr::Big(limbs.into())),
        }
    }

    /// The value, when it fits a `u64`.
    pub fn as_u64(&self) -> Option<u64> {
        match &self.0 {
            Repr::Small(n) => Some(*n),
            Repr::Big(_) => None,
        }
    }

    /// The value, when it fits a `u128`.
    pub fn as_u128(&self) -> Option<u128> {
        match self.limbs() {
            [lo] => Some(u128::from(*lo)),
            [lo, hi] => Some(u128::from(*lo) | (u128::from(*hi) << 64)),
            _ => None,
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.0, Repr::Small(0))
    }

    /// Little-endian limbs: one for a value that fits a `u64` (`[0]` for
    /// zero), otherwise as many as the value needs, the top one nonzero.
    pub fn limbs(&self) -> &[u64] {
        match &self.0 {
            Repr::Small(n) => std::slice::from_ref(n),
            Repr::Big(limbs) => limbs,
        }
    }

    /// `self - 1`, or `None` at zero.
    pub fn pred(&self) -> Option<Numeral> {
        match &self.0 {
            Repr::Small(0) => None,
            Repr::Small(n) => Some(Numeral(Repr::Small(n - 1))),
            Repr::Big(limbs) => {
                let mut out = limbs.to_vec();
                for limb in out.iter_mut() {
                    let (next, borrow) = limb.overflowing_sub(1);
                    *limb = next;
                    if !borrow {
                        break;
                    }
                }
                Some(Numeral::from_limbs(out))
            }
        }
    }

    /// `self + 1`.
    pub fn succ(&self) -> Numeral {
        self.mul_add(1, 1)
    }

    /// `self * m + a`, the step of reading digits.
    pub fn mul_add(&self, m: u64, a: u64) -> Numeral {
        let mut out = Vec::with_capacity(self.limbs().len() + 1);
        let mut carry = u128::from(a);
        for &limb in self.limbs() {
            let wide = u128::from(limb) * u128::from(m) + carry;
            out.push(wide as u64);
            carry = wide >> 64;
        }
        out.push(carry as u64);
        Numeral::from_limbs(out)
    }

    /// `(self / d, self % d)` for a nonzero `d`, the step of printing.
    fn div_rem(&self, d: u64) -> (Numeral, u64) {
        debug_assert!(d != 0);
        let mut out = vec![0u64; self.limbs().len()];
        let mut rem = 0u128;
        for (i, &limb) in self.limbs().iter().enumerate().rev() {
            let wide = (rem << 64) | u128::from(limb);
            out[i] = (wide / u128::from(d)) as u64;
            rem = wide % u128::from(d);
        }
        (Numeral::from_limbs(out), rem as u64)
    }

    /// The number of significant bits (0 for zero).
    pub fn bits(&self) -> u64 {
        let limbs = self.limbs();
        let top = limbs[limbs.len() - 1];
        64 * (limbs.len() as u64 - 1) + u64::from(64 - top.leading_zeros())
    }

    /// Bit `i`, least significant first.
    pub fn bit(&self, i: u64) -> bool {
        let limb = (i / 64) as usize;
        self.limbs().get(limb).is_some_and(|l| (l >> (i % 64)) & 1 == 1)
    }

    /// Digits in `radix` (2–36), most significant first, `_` separators
    /// allowed between digits. `None` on an empty string, a stray
    /// separator or a digit outside the radix.
    pub fn parse(digits: &str, radix: u32) -> Option<Numeral> {
        if !(2..=36).contains(&radix) || digits.is_empty() || digits.starts_with('_') || digits.ends_with('_') {
            return None;
        }
        let mut value = Numeral::ZERO;
        for c in digits.chars() {
            if c == '_' {
                continue;
            }
            let d = c.to_digit(radix)?;
            value = value.mul_add(u64::from(radix), u64::from(d));
        }
        Some(value)
    }
}

impl From<u64> for Numeral {
    fn from(n: u64) -> Numeral {
        Numeral::from_u64(n)
    }
}

impl Ord for Numeral {
    fn cmp(&self, other: &Numeral) -> Ordering {
        let (a, b) = (self.limbs(), other.limbs());
        a.len().cmp(&b.len()).then_with(|| a.iter().rev().cmp(b.iter().rev()))
    }
}

impl PartialOrd for Numeral {
    fn partial_cmp(&self, other: &Numeral) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Numeral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Repr::Small(n) = self.0 {
            return write!(f, "{n}");
        }
        // Nineteen decimal digits at a time.
        const CHUNK: u64 = 10_000_000_000_000_000_000;
        let mut chunks = Vec::new();
        let mut rest = self.clone();
        while !rest.is_zero() {
            let (q, r) = rest.div_rem(CHUNK);
            chunks.push(r);
            rest = q;
        }
        let mut out = String::new();
        for (i, chunk) in chunks.iter().rev().enumerate() {
            if i == 0 {
                out.push_str(&chunk.to_string());
            } else {
                out.push_str(&format!("{chunk:019}"));
            }
        }
        f.write_str(&out)
    }
}

impl fmt::Debug for Numeral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big(s: &str) -> Numeral {
        Numeral::parse(s, 10).unwrap()
    }

    #[test]
    fn small_values_stay_inline_and_the_boundary_is_exact() {
        assert_eq!(big("18446744073709551615").as_u64(), Some(u64::MAX));
        let two64 = big("18446744073709551616");
        assert_eq!(two64.as_u64(), None);
        assert_eq!(two64.limbs(), &[0, 1]);
        assert_eq!(two64.pred().unwrap(), Numeral::from_u64(u64::MAX));
        assert_eq!(Numeral::from_u64(u64::MAX).succ(), two64);
        assert_eq!(two64.bits(), 65);
    }

    #[test]
    fn display_round_trips_in_every_radix() {
        for s in ["0", "1", "18446744073709551616", "340282366920938463463374607431768211456",
                  "10000000000000000000", "99999999999999999999999999999999999999999"] {
            let n = big(s);
            assert_eq!(n.to_string(), s);
            for radix in [2u32, 8, 16] {
                let mut digits = String::new();
                let mut rest = n.clone();
                if rest.is_zero() { digits.push('0'); }
                while !rest.is_zero() {
                    let (q, r) = rest.div_rem(u64::from(radix));
                    digits.insert(0, std::char::from_digit(r as u32, radix).unwrap());
                    rest = q;
                }
                assert_eq!(Numeral::parse(&digits, radix).unwrap(), n, "{s} in radix {radix}");
            }
        }
    }

    #[test]
    fn order_is_numeric_and_pred_borrows_across_limbs() {
        let a = big("18446744073709551616");
        let b = big("36893488147419103232");
        assert!(Numeral::from_u64(u64::MAX) < a && a < b);
        assert_eq!(b.pred().unwrap().to_string(), "36893488147419103231");
        assert_eq!(Numeral::ZERO.pred(), None);
        assert_eq!(Numeral::from_u128(u128::MAX).as_u128(), Some(u128::MAX));
    }

    #[test]
    fn malformed_digits_are_refused() {
        for (s, r) in [("", 10), ("_1", 10), ("1_", 10), ("12a", 10), ("2", 2)] {
            assert!(Numeral::parse(s, r).is_none(), "{s:?}");
        }
        assert_eq!(Numeral::parse("1_000", 10), Some(Numeral::from_u64(1000)));
    }
}
