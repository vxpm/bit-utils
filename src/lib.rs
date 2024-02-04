#![cfg_attr(feature = "const_impl", feature(const_trait_impl))]
#![no_std]

//! Crate that provides a [`BitUtils`] trait which implements basic bit operations on integer
//! types. Allows getting/setting the value of a bit or a range of bits.
//!
//! # Features
//! - `assertions`: adds debug assertions that verify valid indices.
//! - `const_impl` (nightly only): makes [`BitUtils`] a const trait.

use core::ops::{BitAnd, Shr};

#[cfg_attr(feature = "const_impl", const_trait)]
pub trait BitUtils: Sized + Copy + Shr<usize, Output = Self> + BitAnd<Self, Output = Self> {
    /// Returns if the given bit is set.  Indices out of range always return false.
    fn bit(self, index: u8) -> bool;

    /// Sets the state of the given bit. Indices out of range return the value unmodified.
    #[must_use = "with_bit returns a new value instead of modifying the original"]
    fn with_bit(self, index: u8, value: bool) -> Self;

    /// Extracts the value between bits `start` (inclusive) and `end` (exclusive). Bits out of
    /// range are always zero and invalid ranges return zero.
    fn bits(self, start: u8, end: u8) -> Self;

    /// Sets the value between given bits. The value is masked, so a value with more bits than
    /// available will drop it's most significant bits. Bits out of range are left unmodified and
    /// invalid ranges return the value unmodified.
    #[must_use = "with_bits returns a new value instead of modifying the original"]
    fn with_bits(self, start: u8, end: u8, value: Self) -> Self;
}

macro_rules! impl_bit_utils {
    (inner; $($constness:ident)? => $t:ty) => {
        impl $($constness)? BitUtils for $t {
            #[inline]
            fn bit(self, index: u8) -> bool {
                #[cfg(feature = "assertions")]
                debug_assert!((index as u32) < Self::BITS);

                let shifted = match self.checked_shr(index as u32) {
                    Some(x) => x,
                    None => 0
                };

                (shifted & 1) > 0
            }

            #[inline]
            fn with_bit(self, index: u8, value: bool) -> Self {
                #[cfg(feature = "assertions")]
                debug_assert!((index as u32) < Self::BITS);

                const ONE: $t = 1;

                let shifted_one = match ONE.checked_shl(index as u32) {
                    Some(x) => x,
                    None => 0
                };

                let shifted_value = match (value as Self).checked_shl(index as u32) {
                    Some(x) => x,
                    None => 0
                };

                (self & !shifted_one) | shifted_value
            }

            #[inline]
            fn bits(self, start: u8, end: u8) -> $t {
                #[cfg(feature = "assertions")]
                {
                    debug_assert!(end >= start);
                    debug_assert!((end as u32) <= Self::BITS);
                }

                const ONE: $t = 1;

                let len = end.saturating_sub(start) as u32;
                let shifted_one = match ONE.checked_shl(len) {
                    Some(x) => x,
                    None => 0
                };

                let mask = shifted_one.wrapping_sub(ONE);

                let shifted_value = match self.checked_shr(start as u32) {
                    Some(x) => x,
                    None => 0,
                };

                shifted_value & mask
            }

            #[inline]
            fn with_bits(self, start: u8, end: u8, value: Self) -> Self {
                #[cfg(feature = "assertions")]
                {
                    debug_assert!(end >= start);
                    debug_assert!((end as u32) <= Self::BITS);
                }

                const ONE: $t = 1;

                let len = end.saturating_sub(start) as u32;
                let shifted_one = match ONE.checked_shl(len) {
                    Some(x) => x,
                    None => 0
                };

                let mask = shifted_one.wrapping_sub(ONE);
                let value = value & mask;

                let shifted_mask = match mask.checked_shl(start as u32) {
                    Some(x) => x,
                    None => 0,
                };

                let shifted_value = match value.checked_shl(start as u32) {
                    Some(x) => x,
                    None => 0,
                };

                (self & !shifted_mask) | shifted_value
            }
        }
    };
    ($($t:ty),*) => {
        $(
            impl_bit_utils!(inner; => $t);
        )*
    };
    (const => $($t:ty),*) => {
        $(
            impl_bit_utils!(inner; const => $t);
        )*
    };
}

#[cfg(not(feature = "const_impl"))]
impl_bit_utils!(u8, u16, u32, u64, i8, i16, i32, i64, i128);
#[cfg(feature = "const_impl")]
impl_bit_utils!(const => u8, u16, u32, u64, i8, i16, i32, i64, u128);

#[cfg(test)]
mod test {
    use super::BitUtils;

    const A: u8 = 0b0110_1010;
    const B: u16 = 0b1000_1100_1111_0001;

    #[test]
    fn test_bit() {
        assert!(!A.bit(0));
        assert!(A.bit(1));
        assert!(!A.bit(2));
        assert!(A.bit(3));

        assert!(!A.bit(4));
        assert!(A.bit(5));
        assert!(A.bit(6));
        assert!(!A.bit(7));

        #[cfg(not(feature = "assertions"))]
        for i in 8..255u8 {
            assert!(!A.bit(i));
        }
    }

    #[test]
    fn test_with_bit() {
        assert_eq!(B.with_bit(0, false), 0b1000_1100_1111_0000);
        assert_eq!(B.with_bit(3, true), 0b1000_1100_1111_1001);
        assert_eq!(B.with_bit(15, false), 0b0000_1100_1111_0001);

        #[cfg(not(feature = "assertions"))]
        for i in 16..255u8 {
            assert_eq!(B.with_bit(i, true), B);
        }
    }

    #[test]
    fn test_bits() {
        assert_eq!(A.bits(0, 4), 0b1010);
        assert_eq!(A.bits(0, 8), 0b0110_1010);
        assert_eq!(A.bits(4, 8), 0b0110);
        assert_eq!(A.bits(3, 7), 0b1101);

        #[cfg(not(feature = "assertions"))]
        assert_eq!(A.bits(5, 38), 0b11);

        #[cfg(not(feature = "assertions"))]
        for start in 8..255u8 {
            for end in start..255u8 {
                assert_eq!(A.bits(start, end), 0);
            }
        }
    }

    #[test]
    fn test_with_bits() {
        assert_eq!(A.with_bits(0, 3, 0b111), 0b0110_1111);
        assert_eq!(A.with_bits(2, 6, 0b0011), 0b0100_1110);
        assert_eq!(A.with_bits(2, 6, 0b1111_0011), 0b0100_1110);

        #[cfg(not(feature = "assertions"))]
        assert_eq!(A.with_bits(8, 10, 0b10101010), A);

        #[cfg(not(feature = "assertions"))]
        assert_eq!(A.with_bits(3, 1, 0b10101010), A);
    }
}
