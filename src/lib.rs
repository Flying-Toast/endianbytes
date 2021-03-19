//! A very simple generic wrapper around the standard library's endianness-related functions.
//!
//! Although the standard library has funtions such as [`{primative}::from_be_bytes()`](u64::from_be_bytes)
//! and [`{primative}::to_be_bytes()`](f32::to_be_bytes), they are implemented directly on the types without
//! using a generic trait. This makes it impossible to concisely write e.g. a serializer/deserializer that
//! works with primatives without duplicating code or using macros.
//! To solve that problem, this crate provides two generic types:
//! - [`EndianBytes`], for converting from byte arrays to primatives
//! - [`ToBytes`], for converting from primatives to byte arrays

#![no_std]

use core::convert::From;
use core::mem::size_of;

enum Endianness {
    Big,
    Little,
    Native,
}

/// A wrapper around a byte array (`[u8; N]`) that allows the array to be
/// converted into a primative (float, int, etc.) while specifying the
/// endianness of the bytes.
///
/// We cannot simply implement [`From<[u8; N]>`](core::convert::From)
/// on primative types, because it would not allow us to specify the
/// endianness of the array we are converting from. To solve this,
/// `EndianBytes` wraps the byte array and stores a marker alongside it
/// to denote the endianness of the array. This way, the `From<EndianBytes>`
/// implementation is able to properly react to different endians.
///
/// To create an `EndianBytes` from a byte array of a certain endianness, use
/// the corresponding `EndianBytes::from_*` function. Then, to convert the
/// `EndianBytes` to a primative, call `.into()` (from the `From<EndianBytes<N>>`
/// implementation).
///
/// This crate has implementations of `From<EndianBytes<N>>` for all
/// primative types.
///
/// # Examples
///
/// Parse primatives from a big endian byte array:
///
/// ```
/// # use endianbytes::EndianBytes;
/// # fn main() {
/// use std::convert::TryInto;
///
/// struct Parser<'a> {
///     data: &'a [u8],
/// }
///
/// impl<'a> Parser<'a> {
///     fn parse<T: From<EndianBytes<N>>, const N: usize>(&mut self) -> T {
///         let bytes = self.data[..N].try_into().unwrap();
///         // advance the slice past the N bytes we just parsed
///         self.data = &self.data[N..];
///
///         // the `from_be_bytes` specifies that the `From` implementation will
///         // convert from the big endian byte array `bytes`.
///         EndianBytes::from_be_bytes(bytes).into()
///     }
/// }
///
/// let bytes = [67, 216, 55, 10, 3, 75, 0, 32, 176, 134];
/// let mut parser = Parser { data: &bytes, };
///
/// let parsed1: f32 = parser.parse();
/// assert_eq!(parsed1, 432.43);
///
/// let parsed2: i16 = parser.parse();
/// assert_eq!(parsed2, 843);
///
/// let parsed3: i32 = parser.parse();
/// assert_eq!(parsed3, 2142342);
/// # }
/// ```
pub struct EndianBytes<const N: usize> {
    // NOTE: The reason this is implemented as a struct instead of a tuple enum
    // is because doing so would allow users to manually create instances of
    // the enum, which can lead to confusing situations. For example, a user
    // would be able to do something like this:
    // ```
    // let some_le_bytes = [210, 4];
    // let some_be_bytes = EndianBytes::BigEndian(some_le_bytes);
    // let bytes = some_be_bytes.0;
    // ```
    // In this case it could seem like `bytes` should be in big endian, but
    // really `bytes` is still the same `[210, 4]` little endian array we
    // started with. To avoid that confusion, it's better to just encapsulate
    // it all in this struct.
    endianness: Endianness,
    bytes: [u8; N],
}

impl<const N: usize> EndianBytes<N> {
    /// Creates an `EndianBytes` wrapper around the given big endian byte array
    pub const fn from_be_bytes(bytes: [u8; N]) -> Self {
        Self {
            endianness: Endianness::Big,
            bytes,
        }
    }

    /// Creates an `EndianBytes` wrapper around the given little endian byte array
    pub const fn from_le_bytes(bytes: [u8; N]) -> Self {
        Self {
            endianness: Endianness::Little,
            bytes,
        }
    }

    /// Creates an `EndianBytes` wrapper around the given native (platform) endian byte array
    ///
    /// Because this uses the endianness of the underlying architecture, portable
    /// code should prefer [`from_le_bytes`](Self::from_le_bytes) or [`from_be_byres`](Self::from_be_bytes).
    pub const fn from_ne_bytes(bytes: [u8; N]) -> Self {
        Self {
            endianness: Endianness::Native,
            bytes,
        }
    }
}

/// The `ToBytes` trait enables primative types to be converted to a byte array of a
/// specific endianness.
///
/// `ToBytes` is implemented on all the primative types (floats, ints, usize/isize),
/// which allows code to be generic over all types which have endianness and thus can
/// be converted to a byte array of another endianness.
///
/// This is the generic vertion of the standard library's [`{primative}::to_{be, le, ne}_bytes`](i32::to_be_bytes).
///
/// # Examples
///
/// Create a type that packs primatives into a `Vec` of bytes, in little endian byte order:
///
/// ```
/// # use endianbytes::ToBytes;
/// # fn main() {
/// struct BytePacker {
///     data: Vec<u8>,
/// }
///
/// impl BytePacker {
///     // this function can be generic thanks to the `ToBytes` trait
///     fn pack<T: ToBytes<N>, const N: usize>(&mut self, value: T) {
///         self.data.reserve(N);
///         // append the value to `data` as little endian bytes
///         self.data.extend_from_slice(&value.to_le_bytes());
///     }
/// }
///
/// let mut packer = BytePacker { data: Vec::new(), };
/// // pack() accepts any primative:
/// packer.pack(12u8);
/// packer.pack(0.5);
/// packer.pack(1337i16);
/// # }
/// ```
///
/// If we didn't have the `ToBytes` trait, the only way we would be able to do
/// this using the standard library would be:
///
/// ```
/// # struct BytePacker { data: Vec<u8>, }
/// impl BytePacker {
///     fn pack_u8(&mut self, value: u8) {
///         self.data.reserve(std::mem::size_of::<u8>());
///         self.data.extend_from_slice(&value.to_le_bytes());
///     }
///
///     fn pack_i8(&mut self, value: i8) {
///         self.data.reserve(std::mem::size_of::<i8>());
///         self.data.extend_from_slice(&value.to_le_bytes());
///     }
///
///     fn pack_f32(&mut self, value: f32) {
///         self.data.reserve(std::mem::size_of::<f32>());
///         self.data.extend_from_slice(&value.to_le_bytes());
///     }
///     // ... f64, u16, i16, etc.
/// }
/// ```
pub trait ToBytes<const N: usize> {
    /// Converts this value into its bytes in little endian order
    fn to_le_bytes(self) -> [u8; N];

    /// Converts this value into its bytes in big endian order
    fn to_be_bytes(self) -> [u8; N];

    /// Converts this value into its bytes in native (platform) endian order.
    ///
    /// Because this uses the endianness of the underlying architecture, portable
    /// code should prefer [`to_le_bytes`](Self::to_le_bytes) or [`to_be_bytes`](Self::to_be_bytes).
    fn to_ne_bytes(self) -> [u8; N];
}

macro_rules! impls {
    ($($prim:ty)*) => {
    $(
        impl From<EndianBytes<{size_of::<$prim>()}>> for $prim {
            fn from(ebytes: EndianBytes<{size_of::<$prim>()}>) -> Self {
                let EndianBytes { bytes, endianness } = ebytes;

                match endianness {
                    Endianness::Big    => Self::from_be_bytes(bytes),
                    Endianness::Little => Self::from_le_bytes(bytes),
                    Endianness::Native => Self::from_ne_bytes(bytes),
                }
            }
        }

        impl ToBytes<{size_of::<$prim>()}> for $prim {
            fn to_le_bytes(self) -> [u8; size_of::<$prim>()] {
                self.to_le_bytes()
            }

            fn to_be_bytes(self) -> [u8; size_of::<$prim>()] {
                self.to_be_bytes()
            }

            fn to_ne_bytes(self) -> [u8; size_of::<$prim>()] {
                self.to_ne_bytes()
            }
        }
    )*
    }
}

impls!(f32 f64 u8 i8 u16 i16 u32 i32 u64 i64 u128 i128 usize isize);
