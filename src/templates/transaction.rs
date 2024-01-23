use super::*;
use crate::runes::RunescanRunestone;
use bitcoin::hashes::hex::FromHex;
use bitcoincore_rpc::bitcoincore_rpc_json::{
  serde_hex, GetRawTransactionResultVinScriptSig, GetRawTransactionResultVoutScriptPubKey,
};
use serde::de::Error;

pub type TransactionJson = TransactionHtml;

#[derive(Boilerplate, Debug, PartialEq, Serialize, Deserialize)]
pub struct TransactionHtml {
  pub chain: Chain,
  pub etching: Option<SpacedRune>,
  pub inscription_count: u32,
  pub transaction: Transaction,
  pub txid: Txid,
}

impl PageContent for TransactionHtml {
  fn title(&self) -> String {
    format!("Transaction {}", self.txid)
  }
}

// Custom deserializer functions.

/// deserialize_hex_array_opt deserializes a vector of hex-encoded byte arrays.
fn deserialize_hex_array_opt<'de, D>(deserializer: D) -> Result<Option<Vec<Vec<u8>>>, D::Error>
where
  D: serde::Deserializer<'de>,
{
  //TODO(stevenroose) Revisit when issue is fixed:
  // https://github.com/serde-rs/serde/issues/723

  let v: Vec<String> = Vec::deserialize(deserializer)?;
  let mut res = Vec::new();
  for h in v.into_iter() {
    res.push(FromHex::from_hex(&h).map_err(D::Error::custom)?);
  }
  Ok(Some(res))
}

#[derive(Clone, PartialEq, Eq, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RawTransactionResultVin {
  pub sequence: u32,
  /// The raw scriptSig in case of a coinbase tx.
  #[serde(default, with = "serde_hex::opt")]
  pub coinbase: Option<Vec<u8>>,
  /// Not provided for coinbase txs.
  pub txid: Option<bitcoin::Txid>,
  /// Not provided for coinbase txs.
  pub vout: Option<u32>,
  #[serde(with = "bitcoin::amount::serde::as_btc")]
  pub value: Amount,
  /// The scriptSig in case of a non-coinbase tx.
  pub script_sig: Option<GetRawTransactionResultVinScriptSig>,
  /// Not provided for coinbase txs.
  #[serde(default, deserialize_with = "deserialize_hex_array_opt")]
  pub txinwitness: Option<Vec<Vec<u8>>>,
  pub rune_balances: Vec<(SpacedRune, Pile)>,
}

#[derive(Clone, PartialEq, Eq, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RawTransactionResultVout {
  #[serde(with = "bitcoin::amount::serde::as_btc")]
  pub value: Amount,
  pub n: u32,
  pub script_pub_key: GetRawTransactionResultVoutScriptPubKey,
  pub rune_balances: Vec<(SpacedRune, Pile)>,
  pub runestone: Option<RunescanRunestone>,
}

#[derive(Clone, PartialEq, Eq, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RawTransactionResult {
  #[serde(rename = "in_active_chain")]
  pub in_active_chain: Option<bool>,
  #[serde(with = "serde_hex")]
  pub hex: Vec<u8>,
  pub txid: bitcoin::Txid,
  pub hash: bitcoin::Wtxid,
  pub size: usize,
  pub vsize: usize,
  pub version: u32,
  pub locktime: u32,
  pub vin: Vec<RawTransactionResultVin>,
  pub vout: Vec<RawTransactionResultVout>,
  pub blockhash: Option<bitcoin::BlockHash>,
  pub confirmations: Option<u32>,
  pub time: Option<usize>,
  pub blocktime: Option<usize>,
}

#[cfg(test)]
mod tests {
  use {super::*, bitcoin::blockdata::script};

  #[test]
  fn html() {
    let transaction = Transaction {
      version: 2,
      lock_time: LockTime::ZERO,
      input: vec![TxIn {
        sequence: Default::default(),
        previous_output: Default::default(),
        script_sig: Default::default(),
        witness: Default::default(),
      }],
      output: vec![
        TxOut {
          value: 50 * COIN_VALUE,
          script_pubkey: script::Builder::new().push_int(0).into_script(),
        },
        TxOut {
          value: 50 * COIN_VALUE,
          script_pubkey: script::Builder::new().push_int(1).into_script(),
        },
      ],
    };

    let txid = transaction.txid();

    pretty_assert_eq!(
      TransactionHtml {
        chain: Chain::Mainnet,
        etching: None,
        inscription_count: 0,
        txid: transaction.txid(),
        transaction,
      }.to_string(),
      format!(
        "
        <h1>Transaction <span class=monospace>{txid}</span></h1>
        <dl>
        </dl>
        <h2>1 Input</h2>
        <ul>
          <li><a class=monospace href=/output/0000000000000000000000000000000000000000000000000000000000000000:4294967295>0000000000000000000000000000000000000000000000000000000000000000:4294967295</a></li>
        </ul>
        <h2>2 Outputs</h2>
        <ul class=monospace>
          <li>
            <a href=/output/{txid}:0 class=monospace>
              {txid}:0
            </a>
            <dl>
              <dt>value</dt><dd>5000000000</dd>
              <dt>script pubkey</dt><dd class=monospace>OP_0</dd>
            </dl>
          </li>
          <li>
            <a href=/output/{txid}:1 class=monospace>
              {txid}:1
            </a>
            <dl>
              <dt>value</dt><dd>5000000000</dd>
              <dt>script pubkey</dt><dd class=monospace>OP_PUSHNUM_1</dd>
            </dl>
          </li>
        </ul>
      "
      )
      .unindent()
    );
  }
}
