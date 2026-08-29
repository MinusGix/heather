//! Core search and reflection half of the kernel-certified Omega acceptance.

mod omega_cases;
mod support;

#[test]
fn omega_core_suite() {
    omega_cases::omega_core_suite();
}
