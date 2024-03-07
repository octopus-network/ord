use super::*;

#[derive(Default, Serialize, Debug, PartialEq, Copy, Clone)]
pub struct Edict {
  #[serde(with = "serde_rune_id")]
  pub id: u128,
  pub amount: u128,
  pub output: u128,
}

pub mod serde_rune_id {
  use super::RuneId;
  use serde::Serializer;

  pub fn serialize<S: Serializer>(b: &u128, s: S) -> Result<S::Ok, S::Error> {
    RuneId::try_from(*b)
      .map(|rune_id| s.collect_str(&rune_id))
      .map_err(serde::ser::Error::custom)?
  }
}
