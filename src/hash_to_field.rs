//! This module implements hash_to_field and related hashing primitives
//! for use with BLS signatures.

use digest::generic_array::{typenum::Unsigned, ArrayLength, GenericArray};
use digest::{BlockInput, Digest, ExtendableOutput, Update};
use std::marker::PhantomData;

/// Hash to field for they type `T` using ExpandMsg variant `X`.
pub fn hash_to_field<T, X>(msg: &[u8], dst: &[u8], count: usize) -> Vec<T>
where
    T: FromRO,
    X: ExpandMsg,
{
    let len_per_elm = <T as FromRO>::Length::to_usize();
    let len_in_bytes = count * len_per_elm;
    let pseudo_random_bytes = X::expand_message(msg, dst, len_in_bytes);

    let mut ret = Vec::<T>::with_capacity(count);
    for idx in 0..count {
        let bytes_to_convert = &pseudo_random_bytes[idx * len_per_elm..(idx + 1) * len_per_elm];
        let bytes_arr = GenericArray::<u8, <T as FromRO>::Length>::from_slice(bytes_to_convert);
        ret.push(T::from_ro(bytes_arr));
    }

    ret
}

/// Generate a field element from a random string of bytes.
pub trait FromRO {
    type Length: ArrayLength<u8>;

    fn from_ro(okm: &GenericArray<u8, <Self as FromRO>::Length>) -> Self;
}

/// BaseFromRO is a FromRO impl for a field with extension degree 1.
impl<T: BaseFromRO> FromRO for T {
    type Length = <T as BaseFromRO>::BaseLength;

    fn from_ro(okm: &GenericArray<u8, <Self as FromRO>::Length>) -> T {
        T::from_okm(okm)
    }
}

/// Generate an element of a base field for a random string of bytes
/// (used by FromRO for extension fields).
pub trait BaseFromRO {
    type BaseLength: ArrayLength<u8>;

    fn from_okm(okm: &GenericArray<u8, <Self as BaseFromRO>::BaseLength>) -> Self;
}

/// Trait for types implementing expand_message interface for hash_to_field
pub trait ExpandMsg {
    fn expand_message(msg: &[u8], dst: &[u8], len_in_bytes: usize) -> Vec<u8>;
}

/// Placeholder type for implementing expand_message_xof based on a hash function
#[derive(Debug)]
pub struct ExpandMsgXof<HashT> {
    phantom: PhantomData<HashT>,
}

/// ExpandMsgXof implements expand_message_xof for the ExpandMsg trait
impl<HashT> ExpandMsg for ExpandMsgXof<HashT>
where
    HashT: Default + ExtendableOutput + Update,
{
    fn expand_message(msg: &[u8], dst: &[u8], len_in_bytes: usize) -> Vec<u8> {
        assert!(
            dst.len() < 256,
            "dst of more than 255bytes is not supported"
        );
        HashT::default()
            .chain(msg)
            .chain([(len_in_bytes >> 8) as u8, len_in_bytes as u8])
            .chain(dst)
            .chain([dst.len() as u8])
            .finalize_boxed(len_in_bytes)
            .to_vec()
    }
}

/// Placeholder type for implementing `expand_message_xmd` based on a hash function.
#[derive(Debug)]
pub struct ExpandMsgXmd<HashT> {
    phantom: PhantomData<HashT>,
}

/// ExpandMsgXmd implements expand_message_xmd for the ExpandMsg trait
impl<HashT> ExpandMsg for ExpandMsgXmd<HashT>
where
    HashT: Digest + BlockInput,
{
    fn expand_message(msg: &[u8], dst: &[u8], len_in_bytes: usize) -> Vec<u8> {
        assert!(
            dst.len() < 256,
            "dst of more than 255bytes is not supported"
        );
        let b_in_bytes = <HashT as Digest>::OutputSize::to_usize();
        let ell = (len_in_bytes + b_in_bytes - 1) / b_in_bytes;
        if ell > 255 {
            panic!("ell was too big in expand_message_xmd");
        }
        let b_0 = HashT::new()
            .chain(GenericArray::<u8, <HashT as BlockInput>::BlockSize>::default())
            .chain(msg)
            .chain([(len_in_bytes >> 8) as u8, len_in_bytes as u8, 0u8])
            .chain(dst)
            .chain([dst.len() as u8])
            .finalize();

        let mut b_vals = Vec::<u8>::with_capacity(ell * b_in_bytes);
        // b_1
        b_vals.extend_from_slice(
            HashT::new()
                .chain(&b_0[..])
                .chain([1u8])
                .chain(dst)
                .chain([dst.len() as u8])
                .finalize()
                .as_ref(),
        );

        for idx in 1..ell {
            // b_0 XOR b_(idx - 1)
            let mut tmp = GenericArray::<u8, <HashT as Digest>::OutputSize>::default();
            b_0.iter()
                .zip(&b_vals[(idx - 1) * b_in_bytes..idx * b_in_bytes])
                .enumerate()
                .for_each(|(jdx, (b0val, bi1val))| tmp[jdx] = b0val ^ bi1val);
            b_vals.extend_from_slice(
                HashT::new()
                    .chain(tmp)
                    .chain([(idx + 1) as u8])
                    .chain(dst)
                    .chain([dst.len() as u8])
                    .finalize()
                    .as_ref(),
            );
        }

        b_vals.truncate(len_in_bytes);
        b_vals
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::Sha256;

    // Except introducing new internal variables, expand_message_xmd did not change
    // between draft 7 and draft 8 (https://tools.ietf.org/rfcdiff?difftype=--hwdiff&url2=draft-irtf-cfrg-hash-to-curve-08.txt).
    // So we use draft 8 test vectors.

    /// From https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-08#appendix-I.1
    #[test]
    fn expand_message_xmd_works_for_draft8_testvectors_sha256() {
        let dst = b"QUUX-V01-CS02-with-expander";

        let msg = b"";
        let len_in_bytes = 0x20;
        let uniform_bytes =
            hex::decode("f659819a6473c1835b25ea59e3d38914c98b374f0970b7e4c92181df928fca88")
                .unwrap();
        assert_eq!(
            ExpandMsgXmd::<Sha256>::expand_message(msg, dst, len_in_bytes),
            uniform_bytes
        );

        let msg = b"abc";
        let len_in_bytes = 0x20;
        let uniform_bytes =
            hex::decode("1c38f7c211ef233367b2420d04798fa4698080a8901021a795a1151775fe4da7")
                .unwrap();
        assert_eq!(
            ExpandMsgXmd::<Sha256>::expand_message(msg, dst, len_in_bytes),
            uniform_bytes
        );

        let msg = b"abcdef0123456789";
        let len_in_bytes = 0x20;
        let uniform_bytes =
            hex::decode("8f7e7b66791f0da0dbb5ec7c22ec637f79758c0a48170bfb7c4611bd304ece89")
                .unwrap();
        assert_eq!(
            ExpandMsgXmd::<Sha256>::expand_message(msg, dst, len_in_bytes),
            uniform_bytes
        );

        let msg = b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq";
        let len_in_bytes = 0x20;
        let uniform_bytes =
            hex::decode("72d5aa5ec810370d1f0013c0df2f1d65699494ee2a39f72e1716b1b964e1c642")
                .unwrap();
        assert_eq!(
            ExpandMsgXmd::<Sha256>::expand_message(msg, dst, len_in_bytes),
            uniform_bytes
        );

        let msg = b"a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let len_in_bytes = 0x20;
        let uniform_bytes =
            hex::decode("3b8e704fc48336aca4c2a12195b720882f2162a4b7b13a9c350db46f429b771b")
                .unwrap();
        assert_eq!(
            ExpandMsgXmd::<Sha256>::expand_message(msg, dst, len_in_bytes),
            uniform_bytes
        );

        let msg = b"";
        let len_in_bytes = 0x80;
        let uniform_bytes =
            hex::decode("8bcffd1a3cae24cf9cd7ab85628fd111bb17e3739d3b53f89580d217aa79526f1708354a76a402d3569d6a9d19ef3de4d0b991e4f54b9f20dcde9b95a66824cbdf6c1a963a1913d43fd7ac443a02fc5d9d8d77e2071b86ab114a9f34150954a7531da568a1ea8c760861c0cde2005afc2c114042ee7b5848f5303f0611cf297f")
                .unwrap();
        assert_eq!(
            ExpandMsgXmd::<Sha256>::expand_message(msg, dst, len_in_bytes),
            uniform_bytes
        );

        let msg = b"abc";
        let len_in_bytes = 0x80;
        let uniform_bytes =
            hex::decode("fe994ec51bdaa821598047b3121c149b364b178606d5e72bfbb713933acc29c186f316baecf7ea22212f2496ef3f785a27e84a40d8b299cec56032763eceeff4c61bd1fe65ed81decafff4a31d0198619c0aa0c6c51fca15520789925e813dcfd318b542f8799441271f4db9ee3b8092a7a2e8d5b75b73e28fb1ab6b4573c192")
                .unwrap();
        assert_eq!(
            ExpandMsgXmd::<Sha256>::expand_message(msg, dst, len_in_bytes),
            uniform_bytes
        );

        let msg = b"abcdef0123456789";
        let len_in_bytes = 0x80;
        let uniform_bytes =
            hex::decode("c9ec7941811b1e19ce98e21db28d22259354d4d0643e301175e2f474e030d32694e9dd5520dde93f3600d8edad94e5c364903088a7228cc9eff685d7eaac50d5a5a8229d083b51de4ccc3733917f4b9535a819b445814890b7029b5de805bf62b33a4dc7e24acdf2c924e9fe50d55a6b832c8c84c7f82474b34e48c6d43867be")
                .unwrap();
        assert_eq!(
            ExpandMsgXmd::<Sha256>::expand_message(msg, dst, len_in_bytes),
            uniform_bytes
        );

        let msg = b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq";
        let len_in_bytes = 0x80;
        let uniform_bytes =
            hex::decode("48e256ddba722053ba462b2b93351fc966026e6d6db493189798181c5f3feea377b5a6f1d8368d7453faef715f9aecb078cd402cbd548c0e179c4ed1e4c7e5b048e0a39d31817b5b24f50db58bb3720fe96ba53db947842120a068816ac05c159bb5266c63658b4f000cbf87b1209a225def8ef1dca917bcda79a1e42acd8069")
                .unwrap();
        assert_eq!(
            ExpandMsgXmd::<Sha256>::expand_message(msg, dst, len_in_bytes),
            uniform_bytes
        );

        let msg = b"a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let len_in_bytes = 0x80;
        let uniform_bytes =
            hex::decode("396962db47f749ec3b5042ce2452b619607f27fd3939ece2746a7614fb83a1d097f554df3927b084e55de92c7871430d6b95c2a13896d8a33bc48587b1f66d21b128a1a8240d5b0c26dfe795a1a842a0807bb148b77c2ef82ed4b6c9f7fcb732e7f94466c8b51e52bf378fba044a31f5cb44583a892f5969dcd73b3fa128816e")
                .unwrap();
        assert_eq!(
            ExpandMsgXmd::<Sha256>::expand_message(msg, dst, len_in_bytes),
            uniform_bytes
        );
    }
}
