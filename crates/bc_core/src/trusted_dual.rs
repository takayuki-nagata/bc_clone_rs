// SPDX-License-Identifier: MIT

//! `dual_verified!`, the macro of the kernels in `verified_kernels.rs`. Trusted: Verus checks a
//! kernel as the first expansion (inside `verus!`, with its contract), and the normal build
//! compiles the second, which is assumed to keep the body unchanged (it drops only the
//! contract and adds `#[inline]`). Kani re-checks the kernels in the normal build
//! (`kani_proofs.rs`).

#[cfg(verus_keep_ghost)]
macro_rules! dual_verified {
    (
        $(
            pub const $cname:ident : $cty:ty = $cval:expr;
        )*
        $(
            $(#[$meta:meta])*
            pub $(($scope:tt))? fn $name:ident( $($arg:ident : $arg_ty:ty),* $(,)? ) -> ($ret_name:ident : $ret_ty:ty)
                $(requires [ $($req:tt)* ])?
                ensures [ $($ens:tt)* ]
            $body:block
        )+
    ) => {
        verus! {
            $(
                pub const $cname : $cty = $cval;
            )*
            $(
                $(#[$meta])*
                pub $(($scope))? fn $name( $($arg : $arg_ty),* ) -> ($ret_name : $ret_ty)
                    $(requires $($req)*)?
                    ensures $($ens)*
                $body
            )+
        }
    };
}

#[cfg(not(verus_keep_ghost))]
macro_rules! dual_verified {
    (
        $(
            pub const $cname:ident : $cty:ty = $cval:expr;
        )*
        $(
            $(#[$meta:meta])*
            pub $(($scope:tt))? fn $name:ident( $($arg:ident : $arg_ty:ty),* $(,)? ) -> ($ret_name:ident : $ret_ty:ty)
                $(requires [ $($req:tt)* ])?
                ensures [ $($ens:tt)* ]
            $body:block
        )+
    ) => {
        $(
            pub const $cname : $cty = $cval;
        )*
        $(
            $(#[$meta])*
            #[inline]
            #[allow(
                clippy::manual_range_contains,
                clippy::manual_clamp,
                clippy::implicit_saturating_sub
            )]
            pub $(($scope))? fn $name( $($arg : $arg_ty),* ) -> $ret_ty
            $body
        )+
    };
}
