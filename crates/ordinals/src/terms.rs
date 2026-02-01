use super::*;

#[derive(Default, Serialize, Deserialize, Debug, PartialEq, Copy, Clone, Eq)]
pub struct Terms {
  #[serde(with = "serde_with::As::<Option<serde_with::DisplayFromStr>>")]
  pub amount: Option<u128>,
  #[serde(with = "serde_with::As::<Option<serde_with::DisplayFromStr>>")]
  pub cap: Option<u128>,
  pub height: (Option<u64>, Option<u64>),
  pub offset: (Option<u64>, Option<u64>),
}
