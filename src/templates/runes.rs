use super::*;
use crate::templates::transaction::RawTransactionResult;

pub type RunesJson = RunesHtml;

#[derive(Boilerplate, Debug, PartialEq, Serialize, Deserialize)]
pub struct RunesHtml {
  pub entries: Vec<(RuneId, RuneEntry)>,
}

impl PageContent for RunesHtml {
  fn title(&self) -> String {
    "Runes".to_string()
  }
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct TransactionIdsJson {
  pub ids: Vec<Txid>,
  pub page_index: usize,
  pub more: bool,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct TransactionsPaginatedJson {
  pub txs: Vec<RawTransactionResult>,
  pub page_index: usize,
  pub more: bool,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct OutPointsJson {
  pub outpoints: Vec<OutPoint>,
  pub page_index: usize,
  pub more: bool,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct HolderAddressWithAmountJson {
  pub holder_with_amount: Vec<(Option<Address<NetworkUnchecked>>, u64)>,
  pub page_index: usize,
  pub more: bool,
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn display() {
    assert_eq!(
      RunesHtml {
        entries: vec![(
          RuneId {
            height: 0,
            index: 0,
          },
          RuneEntry {
            rune: Rune(26),
            spacers: 1,
            ..Default::default()
          }
        )],
      }
      .to_string(),
      "<h1>Runes</h1>
<ul>
  <li><a href=/rune/A•A>A•A</a></li>
</ul>
"
    );
  }
}
