//! Reconstruction and refusal half of the kernel-certified Omega acceptance.

mod omega_cases;
mod support;

#[test]
fn omega_reconstruction_suite() {
    omega_cases::omega_reconstruction_suite();
}
