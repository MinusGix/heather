//! Shared vocabulary and queries for surface dispatch policies.

mod carrier;
pub(crate) use carrier::Carriers;
mod cast;
pub(crate) use cast::Casts;
mod dictionary;
pub(crate) use dictionary::Dictionaries;
mod member;
pub(crate) use member::Members;
mod operator;
pub(crate) use operator::Operators;
mod projection;
pub(crate) use projection::Projections;
mod receiver;
pub(crate) use receiver::Receivers;

pub(crate) use carrier::Carrier;
