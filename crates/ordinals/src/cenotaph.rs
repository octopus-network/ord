use super::*;

#[derive(Serialize, Eq, PartialEq, Deserialize, Debug, Default, Clone)]
pub struct Cenotaph {
  pub etching: Option<Rune>,
  pub flaw: Option<Flaw>,
  pub mint: Option<RuneId>,
}
