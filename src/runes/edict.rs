use super::*;

#[derive(Default, Deserialize, Serialize, Debug, PartialEq, Eq, Copy, Clone)]
pub struct Edict {
  pub id: u128,
  pub amount: u128,
  pub output: u128,
}

#[derive(Default, Deserialize, Serialize, Debug, PartialEq, Eq, Clone)]
pub struct RunescanEdict {
  pub id: u128,
  pub rune: String,
  pub rune_id: String,
  pub amount: u128,
  pub output: u128,
}
