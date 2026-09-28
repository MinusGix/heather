//! Core search and reflection half of the kernel-certified Omega acceptance.

use crate::omega_cases;

#[test]
fn omega_core_suite() {
    omega_cases::omega_core_suite();
}

#[test]
fn omega_shadowed_binder_certificates() {
    omega_cases::omega_shadowed_binder_certificates();
}
