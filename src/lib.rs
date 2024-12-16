#![cfg_attr(feature = "const_impl", feature(const_trait_impl))]
#![no_std]

//! Crate that provides a [`BitUtils`] trait which implements basic bit operations on integer
//! types. Allows getting/setting the value of a bit or a range of bits.
//!
//! # Features
//! - `const_impl` (nightly only): makes [`BitUtils`] a const trait.

/// Provides methods for querying and modifying the value of specific bits. Convention is LSB0.
#[cfg_attr(feature = "const_impl", const_trait)]
pub trait BitUtils: Sized + Copy {
    /// Returns whether the bit at `index` is set or not. Indices out of range always return false.
    fn bit(self, index: u8) -> bool;

    /// Returns whether the bit at `index` is set or not. If out of range, returns [`None`].
    fn try_bit(self, index: u8) -> Option<bool>;

    /// Sets the state of the bit at `index`. Indices out of range return the value unmodified.
    #[must_use = "with_bit returns a new value instead of modifying the original"]
    fn with_bit(self, index: u8, value: bool) -> Self;

    /// Sets the state of the bit at `index`. If out of range, returns [`None`].
    #[must_use = "with_bit returns a new value instead of modifying the original"]
    fn try_with_bit(self, index: u8, value: bool) -> Option<Self>;

    /// Extracts the value between bits `start` (inclusive) and `end` (exclusive). Bits out of
    /// range are always zero and invalid ranges return zero.
    fn bits(self, start: u8, end: u8) -> Self;

    /// Extracts the value between bits `start` (inclusive) and `end` (exclusive). If the range is
    /// invalid, returns [`None`].
    fn try_bits(self, start: u8, end: u8) -> Option<Self>;

    /// Sets the value between given bits. The value is masked, so a value with more bits than
    /// available will drop it's most significant bits. Bits out of range are left unmodified and
    /// invalid ranges return the value unmodified.
    #[must_use = "with_bits returns a new value instead of modifying the original"]
    fn with_bits(self, start: u8, end: u8, value: Self) -> Self;

    /// Sets the value between given bits. The value is masked, so a value with more bits than
    /// available will drop it's most significant bits. If the range is invalid, returns [`None`].
    #[must_use = "with_bits returns a new value instead of modifying the original"]
    fn try_with_bits(self, start: u8, end: u8, value: Self) -> Option<Self>;
}

macro_rules! impl_bit_utils {
    (inner; $($constness:ident)? => $t:ty) => {
        impl $($constness)? BitUtils for $t {
            #[inline(always)]
            fn bit(self, index: u8) -> bool {
                let shifted = match self.checked_shr(index as u32) {
                    Some(x) => x,
                    None => 0
                };

                (shifted & 1) > 0
            }

            #[inline(always)]
            fn try_bit(self, index: u8) -> Option<bool> {
                let shifted = self.checked_shr(index as u32);
                match shifted {
                    Some(x) => Some((x & 1) > 0),
                    None => None
                }
            }

            #[inline(always)]
            fn with_bit(self, index: u8, value: bool) -> Self {
                const ONE: $t = 1;

                if index >= Self::BITS as u8 {
                    return self;
                }

                let shifted_one = ONE << (index as usize);
                let shifted_value = (value as Self) << (index as usize);
                (self & !shifted_one) | shifted_value
            }

            #[inline(always)]
            fn try_with_bit(self, index: u8, value: bool) -> Option<Self> {
                const ONE: $t = 1;

                if index >= Self::BITS as u8 {
                    return None;
                }

                let shifted_one = ONE << (index as usize);
                let shifted_value = (value as Self) << (index as usize);
                Some((self & !shifted_one) | shifted_value)
            }

            #[inline(always)]
            fn bits(self, start: u8, end: u8) -> Self {
                const ONE: $t = 1;

                let len = end.saturating_sub(start) as u32;
                if start >= Self::BITS as u8 || len == 0 {
                    return 0;
                }

                let shifted_one = match ONE.checked_shl(len) {
                    Some(x) => x,
                    None => 0,
                };
                let mask = shifted_one.wrapping_sub(ONE);

                let shifted_value = self >> (start as usize);
                let result = shifted_value & mask;

                unsafe { core::hint::assert_unchecked(result <= mask) };
                result
            }

            #[inline(always)]
            fn try_bits(self, start: u8, end: u8) -> Option<Self> {
                const ONE: $t = 1;

                let len = end.saturating_sub(start);
                if start >= Self::BITS as u8 || end > Self::BITS as u8 || len == 0 {
                    return None;
                }

                let shifted_one = match ONE.checked_shl(len as u32) {
                    Some(x) => x,
                    None => 0,
                };
                let mask = shifted_one.wrapping_sub(ONE);

                let shifted_value = self >> (start as usize);
                let result = shifted_value & mask;

                unsafe { core::hint::assert_unchecked(result <= mask) };
                Some(result)
            }

            #[inline(always)]
            fn with_bits(self, start: u8, end: u8, value: Self) -> Self {
                const ONE: $t = 1;

                let len = end.saturating_sub(start) as u32;
                if start >= Self::BITS as u8 || len == 0 {
                    return self;
                }

                let shifted_one = match ONE.checked_shl(len) {
                    Some(x) => x,
                    None => 0,
                };
                let mask = shifted_one.wrapping_sub(ONE);
                let value = value & mask;

                let shifted_mask = mask << (start as usize);
                let shifted_value = value << (start as usize);

                (self & !shifted_mask) | shifted_value
            }

            #[inline(always)]
            fn try_with_bits(self, start: u8, end: u8, value: Self) -> Option<Self> {
                const ONE: $t = 1;

                let len = end.saturating_sub(start) as u32;
                if start >= Self::BITS as u8 || end > Self::BITS as u8 || len == 0 {
                    return None;
                }

                let shifted_one = match ONE.checked_shl(len) {
                    Some(x) => x,
                    None => 0,
                };
                let mask = shifted_one.wrapping_sub(ONE);
                let value = value & mask;

                let shifted_mask = mask << (start as usize);
                let shifted_value = value << (start as usize);

                Some((self & !shifted_mask) | shifted_value)
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

        for i in 8..255u8 {
            assert!(!A.bit(i));
        }
    }

    #[test]
    fn test_try_bit() {
        assert!(!A.try_bit(0).unwrap());
        assert!(A.try_bit(1).unwrap());
        assert!(!A.try_bit(2).unwrap());
        assert!(A.try_bit(3).unwrap());

        assert!(!A.try_bit(4).unwrap());
        assert!(A.try_bit(5).unwrap());
        assert!(A.try_bit(6).unwrap());
        assert!(!A.try_bit(7).unwrap());

        for i in 8..255u8 {
            assert!(A.try_bit(i).is_none());
        }
    }

    #[test]
    fn test_with_bit() {
        assert_eq!(B.with_bit(0, false), 0b1000_1100_1111_0000);
        assert_eq!(B.with_bit(3, true), 0b1000_1100_1111_1001);
        assert_eq!(B.with_bit(15, false), 0b0000_1100_1111_0001);

        for i in 16..255u8 {
            assert_eq!(B.with_bit(i, true), B);
        }
    }

    #[test]
    fn test_try_with_bit() {
        assert_eq!(B.try_with_bit(0, false).unwrap(), 0b1000_1100_1111_0000);
        assert_eq!(B.try_with_bit(3, true).unwrap(), 0b1000_1100_1111_1001);
        assert_eq!(B.try_with_bit(15, false).unwrap(), 0b0000_1100_1111_0001);

        for i in 16..255u8 {
            assert!(B.try_with_bit(i, true).is_none());
        }
    }

    #[test]
    fn test_bits() {
        assert_eq!(A.bits(0, 4), 0b1010);
        assert_eq!(A.bits(0, 8), 0b0110_1010);
        assert_eq!(A.bits(4, 8), 0b0110);
        assert_eq!(A.bits(3, 7), 0b1101);

        assert_eq!(A.bits(5, 38), 0b11);

        for start in 8..255u8 {
            for end in start..255u8 {
                assert_eq!(A.bits(start, end), 0);
            }
        }
    }

    #[test]
    fn test_try_bits() {
        assert_eq!(A.try_bits(0, 4).unwrap(), 0b1010);
        assert_eq!(A.try_bits(0, 8).unwrap(), 0b0110_1010);
        assert_eq!(A.try_bits(4, 8).unwrap(), 0b0110);
        assert_eq!(A.try_bits(3, 7).unwrap(), 0b1101);

        assert!(A.try_bits(8, 9).is_none());
        assert!(A.try_bits(5, 9).is_none());
        assert!(A.try_bits(5, 38).is_none());

        for start in 8..255u8 {
            for end in start..255u8 {
                assert!(A.try_bits(start, end).is_none());
            }
        }
    }

    #[test]
    fn test_with_bits() {
        assert_eq!(A.with_bits(0, 3, 0b111), 0b0110_1111);
        assert_eq!(A.with_bits(2, 6, 0b0011), 0b0100_1110);
        assert_eq!(A.with_bits(2, 6, 0b1111_0011), 0b0100_1110);

        assert_eq!(A.with_bits(8, 10, 0b10101010), A);
        assert_eq!(A.with_bits(3, 1, 0b10101010), A);
    }

    #[test]
    fn test_try_with_bits() {
        assert_eq!(A.try_with_bits(0, 3, 0b111).unwrap(), 0b0110_1111);
        assert_eq!(A.try_with_bits(2, 6, 0b0011).unwrap(), 0b0100_1110);
        assert_eq!(A.try_with_bits(2, 6, 0b1111_0011).unwrap(), 0b0100_1110);

        assert!(A.try_with_bits(2, 8, 0b1111_0011).is_some());
        assert!(A.try_with_bits(2, 9, 0b1111_0011).is_none());
        assert!(A.try_with_bits(8, 10, 0b10101010).is_none());
        assert!(A.try_with_bits(3, 1, 0b10101010).is_none());
    }
}
