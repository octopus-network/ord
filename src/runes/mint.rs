use super::*;

#[derive(Default, Deserialize, Serialize, Debug, PartialEq, Copy, Clone)]
pub struct Mint {
  pub deadline: Option<u32>,
  pub limit: Option<u128>,
  pub term: Option<u32>,
}
