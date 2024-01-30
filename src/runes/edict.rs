use super::*;

#[derive(Default, Deserialize, Serialize, Debug, PartialEq, Eq, Copy, Clone)]
pub struct Edict {
  pub id: u128,
  pub amount: u128,
  pub output: u128,
}

#[derive(Default, Deserialize, Serialize, Debug, PartialEq, Eq, Clone)]
pub struct RunescanEdict {
  pub rune: Rune,
  pub rune_id: HexRuneId,
  #[serde(flatten)]
  pub edict: Edict,
}
