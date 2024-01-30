use super::*;
use crate::runes::HexRuneId;
use crate::templates::transaction::RawTransactionResult;

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct AddressHolderRuneIdJson {
  pub rune_ids: Vec<AddressHolderItem>,
  pub total: usize,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct AddressHolderItem {
  pub rune: Rune,
  pub rune_id: HexRuneId,
  pub amount: u64,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct AddressTransactionsJson {
  pub txs: Vec<RawTransactionResult>,
  pub total: usize,
}

#[derive(Debug, PartialEq, Clone, Hash, Eq, Ord, PartialOrd)]
pub struct AddressRequest {
  pub address: String,
}

impl Display for AddressRequest {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    write!(f, "{}", self.address)
  }
}

impl FromStr for AddressRequest {
  type Err = crate::Error;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    Ok(Self {
      address: s.to_string(),
    })
  }
}

impl Serialize for AddressRequest {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    serializer.collect_str(self)
  }
}

impl<'de> Deserialize<'de> for AddressRequest {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    Ok(DeserializeFromStr::deserialize(deserializer)?.0)
  }
}
