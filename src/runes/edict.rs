use super::*;

#[derive(Default, Deserialize, Serialize, Debug, PartialEq, Eq, Copy, Clone)]
pub struct Edict {
  pub id: u128,
  pub amount: u128,
  pub output: u128,
}
