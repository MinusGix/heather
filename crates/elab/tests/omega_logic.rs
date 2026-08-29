//! Logical and natural-arithmetic half of the kernel-certified Omega acceptance.

mod omega_cases;
mod support;

#[test]
fn omega_logic_suite() {
    omega_cases::omega_logic_suite();
}
