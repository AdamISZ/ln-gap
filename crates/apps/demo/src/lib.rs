//! The demos' shared session layer (D58): the shared directory, the venue
//! process, the channel session, one game's venue view and disputes, and
//! the pages' server. A demo supplies its game's [`hand::Rules`], its
//! pages and its move buttons.

pub mod hand;
pub mod session;
pub mod store;
pub mod venue;
pub mod web;
