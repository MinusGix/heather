//! The one place the solver is called: CaDiCaL behind `src/shim.cpp`.
//!
//! Safety: a `Session` owns one shim pointer from `heather_sat_new`, freed
//! once in `Drop`; the slices it hands out borrow the session and are copied
//! before the next call into the solver.
#![allow(unsafe_code)]

use std::os::raw::{c_int, c_void};

unsafe extern "C" {
    fn heather_sat_new() -> *mut c_void;
    fn heather_sat_free(p: *mut c_void);
    fn heather_sat_add(p: *mut c_void, lit: c_int);
    fn heather_sat_solve(p: *mut c_void) -> c_int;
    fn heather_sat_val(p: *mut c_void, lit: c_int) -> c_int;
    fn heather_sat_steps_len(p: *mut c_void) -> usize;
    fn heather_sat_steps(p: *mut c_void) -> *const i64;
    fn heather_sat_originals_len(p: *mut c_void) -> usize;
    fn heather_sat_originals(p: *mut c_void) -> *const i64;
    fn heather_sat_restored(p: *mut c_void) -> c_int;
}

pub(crate) struct Session(*mut c_void);

impl Session {
    pub(crate) fn new() -> Session {
        // SAFETY: the shim allocates and configures a fresh solver.
        Session(unsafe { heather_sat_new() })
    }

    pub(crate) fn add(&mut self, lit: i32) {
        // SAFETY: `self.0` is live; literals are any nonzero int, 0 ends a clause.
        unsafe { heather_sat_add(self.0, lit) }
    }

    pub(crate) fn solve(&mut self) -> i32 {
        // SAFETY: `self.0` is live.
        unsafe { heather_sat_solve(self.0) }
    }

    pub(crate) fn val(&mut self, lit: i32) -> i32 {
        // SAFETY: `self.0` is live and was answered satisfiable.
        unsafe { heather_sat_val(self.0, lit) }
    }

    /// The derived clauses, flattened (see `src/shim.cpp`).
    pub(crate) fn steps(&mut self) -> Vec<i64> {
        // SAFETY: the shim's vector is live while `self` is and is not
        // touched while we copy it.
        unsafe { copy(heather_sat_steps(self.0), heather_sat_steps_len(self.0)) }
    }

    pub(crate) fn originals(&mut self) -> Vec<i64> {
        // SAFETY: as `steps`.
        unsafe { copy(heather_sat_originals(self.0), heather_sat_originals_len(self.0)) }
    }

    pub(crate) fn restored(&mut self) -> bool {
        // SAFETY: `self.0` is live.
        unsafe { heather_sat_restored(self.0) != 0 }
    }
}

unsafe fn copy(p: *const i64, n: usize) -> Vec<i64> {
    if n == 0 {
        return Vec::new();
    }
    // SAFETY: the caller passes a vector's data pointer and its length.
    unsafe { std::slice::from_raw_parts(p, n) }.to_vec()
}

impl Drop for Session {
    fn drop(&mut self) {
        // SAFETY: freed once, here.
        unsafe { heather_sat_free(self.0) }
    }
}
