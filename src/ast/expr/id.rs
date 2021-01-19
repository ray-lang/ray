#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Id {
    pub module_id: u64,
    pub local_id: u64,
}
