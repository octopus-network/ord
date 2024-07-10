use super::*;

use bitcoin::{address::Address, Amount};

#[derive(Default, Serialize, Debug, Clone)]
pub struct RsTransaction {
  pub inputs: Vec<RsTxIn>,
  pub outputs: Vec<RsTxOut>,
}

#[derive(Serialize, Debug, Clone)]
pub struct RsTxIn {
  #[serde(with = "bitcoin::amount::serde::as_btc")]
  pub value: Amount,
  pub address: Address,
  pub runes: Vec<(RuneId, u128)>,
}

#[derive(Serialize, Debug, Clone)]
pub struct RsTxOut {
  #[serde(with = "bitcoin::amount::serde::as_btc")]
  pub value: Amount,
  pub address: Option<Address>,
  pub op_return: Option<Artifact>,
  pub runes: Vec<(RuneId, u128)>,
}
