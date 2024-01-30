use super::*;
use crate::index::RunescanRuneEntry;
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
pub struct OctupusRunesJson {
  pub entries: Vec<RunescanRuneEntry>,
  pub total: usize,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct TransactionsPaginatedJson {
  pub txs: Vec<RawTransactionResult>,
  pub page_index: usize,
  pub total: usize,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct HolderAddressWithAmountJson {
  pub holder_with_amount: Vec<HolderAddressWithAmount>,
  pub page_index: usize,
  pub total: usize,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct HolderAddressWithAmount {
  pub address: String,
  pub amount: u128,
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
