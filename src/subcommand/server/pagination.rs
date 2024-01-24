use serde::Deserialize;

fn default_page() -> usize {
  1
}

fn default_size() -> usize {
  100
}

#[derive(Deserialize, Debug)]
pub struct Pagination {
  #[serde(default = "default_page")]
  pub page: usize,
  #[serde(default = "default_size")]
  pub size: usize,
}
