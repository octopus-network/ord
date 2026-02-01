use super::*;

use bitcoin::{Amount, OutPoint, address::Address};
use sqlx::{
  QueryBuilder, Row,
  postgres::{PgPool, PgPoolOptions},
  types::{BigDecimal, time::OffsetDateTime},
};
use std::collections::HashMap;
use std::env;
use std::time::Duration;
use tokio::runtime::Runtime;

/// Default chunk size for batch database operations
pub const PG_CHUNK_SIZE: usize = 500;

/// Maximum retry delay in seconds for database operations
const MAX_RETRY_DELAY_SECS: u64 = 8;

/// Macro to execute a QueryBuilder query with exponential backoff retry.
/// Usage: execute_with_retry!(self, "operation name", pool, { /* build qb */ qb })
macro_rules! execute_with_retry {
  ($self:expr, $operation:expr, $pool:expr, $build_qb:block) => {{
    $self.runtime.block_on(async {
      let mut delay_secs = 1u64;
      loop {
        let mut qb = $build_qb;
        match qb.build().execute($pool).await {
          Ok(result) => {
            log::debug!("{}: {} rows affected", $operation, result.rows_affected());
            return Ok(());
          }
          Err(error) => {
            log::warn!(
              "{} failed, retrying in {}s. Error: {}",
              $operation,
              delay_secs,
              error
            );
            tokio::time::sleep(Duration::from_secs(delay_secs)).await;
            delay_secs = (delay_secs * 2).min(MAX_RETRY_DELAY_SECS);
          }
        }
      }
    })
  }};
}

/// Macro to execute a raw SQL query with exponential backoff retry.
/// Returns Result<T> where T is the return type of the async block.
macro_rules! query_with_retry {
  ($self:expr, $operation:expr, $query:expr) => {{
    $self.runtime.block_on(async {
      let mut delay_secs = 1u64;
      loop {
        match $query.await {
          Ok(result) => return Ok::<_, sqlx::Error>(result),
          Err(error) => {
            log::warn!(
              "{} failed, retrying in {}s. Error: {}",
              $operation,
              delay_secs,
              error
            );
            tokio::time::sleep(Duration::from_secs(delay_secs)).await;
            delay_secs = (delay_secs * 2).min(MAX_RETRY_DELAY_SECS);
          }
        }
      }
    })
  }};
}

#[derive(Default, Serialize, Debug, Clone)]
pub struct RsTransaction {
  pub inputs: Vec<RsTxIn>,
  pub outputs: Vec<RsTxOut>,
}

#[derive(Serialize, Debug, Clone)]
pub struct RsTxIn {
  pub previous_output: OutPoint,
  pub value: Amount,
  pub address: Address,
  #[serde(
    with = "serde_with::As::<Vec<(serde_with::DisplayFromStr, serde_with::DisplayFromStr)>>"
  )]
  pub runes: Vec<(RuneId, u128)>,
}

#[derive(Serialize, Debug, Clone)]
pub struct RsTxOut {
  pub value: Amount,
  pub address: Option<Address>,
  pub op_return: Option<Artifact>,
  #[serde(
    with = "serde_with::As::<Vec<(serde_with::DisplayFromStr, serde_with::DisplayFromStr)>>"
  )]
  pub runes: Vec<(RuneId, u128)>,
}

pub struct PgDatabase {
  pub runtime: Runtime,
  pub pg_pool: PgPool,
}

impl PgDatabase {
  pub fn new() -> Self {
    let runtime = tokio::runtime::Builder::new_multi_thread()
      .enable_all()
      .build()
      .unwrap();

    let database_url = env::var("DATABASE_URL").unwrap();
    let pg_pool = runtime
      .block_on(async {
        PgPoolOptions::new()
          .max_connections(5)
          .acquire_timeout(std::time::Duration::from_secs(3))
          .idle_timeout(std::time::Duration::from_secs(10))
          .max_lifetime(Some(std::time::Duration::from_secs(60 * 30)))
          .connect(&database_url)
          .await
      })
      .unwrap();

    Self { runtime, pg_pool }
  }

  pub fn pg_insert_runes(&self, runes: HashMap<RuneId, RuneEntry>) -> Result {
    if runes.is_empty() {
      return Ok(());
    }

    // Preprocess data for retry
    let runes_data: Vec<_> = runes
      .into_iter()
      .map(|(rune_id, rune_entry)| {
        let symbol = rune_entry.symbol.and_then(|s| {
          if s == '\0' {
            log::warn!("Found null byte as symbol - Rune ID: {}.", rune_id);
            None
          } else {
            Some(s.to_string())
          }
        });
        (
          BigDecimal::from(rune_entry.number),
          rune_id.to_string(),
          rune_entry.burned.to_string(),
          rune_entry.divisibility as i16,
          rune_entry.etching.to_string(),
          rune_entry.mints.to_string(),
          rune_entry.premine.to_string(),
          rune_entry.spaced_rune.to_string(),
          symbol,
          rune_entry.terms.and_then(|t| t.cap).map(|c| c.to_string()),
          rune_entry
            .terms
            .and_then(|t| t.height.0)
            .map(|h| h.to_string()),
          rune_entry
            .terms
            .and_then(|t| t.height.1)
            .map(|h| h.to_string()),
          rune_entry
            .terms
            .and_then(|t| t.amount)
            .map(|a| a.to_string()),
          rune_entry
            .terms
            .and_then(|t| t.offset.0)
            .map(|o| o.to_string()),
          rune_entry
            .terms
            .and_then(|t| t.offset.1)
            .map(|o| o.to_string()),
          OffsetDateTime::from_unix_timestamp(rune_entry.timestamp as i64).unwrap(),
          rune_entry.turbo,
          BigDecimal::from(rune_entry.block),
        )
      })
      .collect();

    execute_with_retry!(self, "insert runes", &self.pg_pool, {
      let mut qb = QueryBuilder::new(
        "INSERT INTO public.runes (
          number, rune_id, burned, divisibility, etching,
          mints, premine, spaced_rune, symbol,
          terms_cap, terms_height_start, terms_height_end,
          terms_amount, terms_offset_start, terms_offset_end,
          timestamp, turbo, block, reorg
        ) ",
      );
      qb.push_values(&runes_data, |mut b, data| {
        b.push_bind(&data.0)
          .push_bind(&data.1)
          .push_bind(&data.2)
          .push_bind(data.3)
          .push_bind(&data.4)
          .push_bind(&data.5)
          .push_bind(&data.6)
          .push_bind(&data.7)
          .push_bind(&data.8)
          .push_bind(&data.9)
          .push_bind(&data.10)
          .push_bind(&data.11)
          .push_bind(&data.12)
          .push_bind(&data.13)
          .push_bind(&data.14)
          .push_bind(data.15)
          .push_bind(data.16)
          .push_bind(&data.17)
          .push_bind(false);
      });
      qb.push(
        " ON CONFLICT (rune_id) WHERE NOT reorg DO UPDATE SET
          number = EXCLUDED.number,
          burned = EXCLUDED.burned,
          divisibility = EXCLUDED.divisibility,
          etching = EXCLUDED.etching,
          mints = EXCLUDED.mints,
          premine = EXCLUDED.premine,
          spaced_rune = EXCLUDED.spaced_rune,
          symbol = EXCLUDED.symbol,
          terms_cap = EXCLUDED.terms_cap,
          terms_height_start = EXCLUDED.terms_height_start,
          terms_height_end = EXCLUDED.terms_height_end,
          terms_amount = EXCLUDED.terms_amount,
          terms_offset_start = EXCLUDED.terms_offset_start,
          terms_offset_end = EXCLUDED.terms_offset_end,
          timestamp = EXCLUDED.timestamp,
          turbo = EXCLUDED.turbo,
          block = EXCLUDED.block,
          reorg = EXCLUDED.reorg",
      );
      qb
    })
  }

  pub fn pg_insert_transactions(&self, block: u32, rs_txs: HashMap<Txid, RsTransaction>) -> Result {
    if rs_txs.is_empty() {
      return Ok(());
    }

    // Preprocess data for retry
    let tx_data: Vec<_> = rs_txs
      .into_iter()
      .map(|(txid, mut transaction)| {
        for output in &mut transaction.outputs {
          if let Some(ref mut artifact) = output.op_return {
            if let Artifact::Runestone(runestone) = artifact {
              if let Some(etching) = &mut runestone.etching {
                if let Some(symbol) = etching.symbol {
                  if symbol == '\0' {
                    etching.symbol = None;
                  }
                }
              }
            }
          }
        }
        (
          txid.to_string(),
          serde_json::to_value(&transaction).unwrap(),
          BigDecimal::from(block),
        )
      })
      .collect();

    execute_with_retry!(self, "insert transactions", &self.pg_pool, {
      let mut qb =
        QueryBuilder::new("INSERT INTO public.transactions (txid, transaction, block, reorg) ");
      qb.push_values(&tx_data, |mut b, (txid, tx_json, blk)| {
        b.push_bind(txid)
          .push_bind(tx_json)
          .push_bind(blk)
          .push_bind(false);
      });
      qb.push(
        " ON CONFLICT (txid) WHERE NOT reorg DO UPDATE SET
              transaction = EXCLUDED.transaction,
              block = EXCLUDED.block,
              reorg = EXCLUDED.reorg",
      );
      qb
    })
  }

  pub fn pg_insert_rune_transactions(
    &self,
    rune_transactions: HashMap<(Txid, RuneId), TxTag>,
    block: u64,
    timestamp: u32,
  ) -> Result {
    if rune_transactions.is_empty() {
      return Ok(());
    }

    let ts = OffsetDateTime::from_unix_timestamp(timestamp as i64).unwrap();
    let blk = BigDecimal::from(block);
    let tx_data: Vec<_> = rune_transactions
      .into_iter()
      .map(|((txid, rune_id), tags)| {
        (
          rune_id.to_string(),
          txid.to_string(),
          tags.burn,
          tags.etch,
          tags.mint,
          tags.transfer,
        )
      })
      .collect();

    execute_with_retry!(self, "insert rune transactions", &self.pg_pool, {
      let mut qb = QueryBuilder::new(
        "INSERT INTO public.rune_transactions (
              rune_id, txid, burn, etch, mint, transfer, block, timestamp, reorg) ",
      );
      qb.push_values(
        &tx_data,
        |mut b, (rune_id, txid, burn, etch, mint, transfer)| {
          b.push_bind(rune_id)
            .push_bind(txid)
            .push_bind(burn)
            .push_bind(etch)
            .push_bind(mint)
            .push_bind(transfer)
            .push_bind(&blk)
            .push_bind(ts)
            .push_bind(false);
        },
      );
      qb.push(
        " ON CONFLICT (rune_id, txid) WHERE NOT reorg DO UPDATE SET
              burn = EXCLUDED.burn, etch = EXCLUDED.etch, mint = EXCLUDED.mint,
              transfer = EXCLUDED.transfer, block = EXCLUDED.block,
              timestamp = EXCLUDED.timestamp, reorg = EXCLUDED.reorg",
      );
      qb
    })
  }

  pub fn pg_insert_rune_transactions_chunked(
    &self,
    rune_transactions: HashMap<(Txid, RuneId), TxTag>,
    block: u64,
    timestamp: u32,
    chunk_size: usize,
  ) -> Result {
    let items: Vec<_> = rune_transactions.into_iter().collect();
    for chunk in items.chunks(chunk_size) {
      self.pg_insert_rune_transactions(chunk.iter().cloned().collect(), block, timestamp)?;
    }
    Ok(())
  }

  pub fn pg_insert_address_transactions(
    &self,
    block: u32,
    address_transactions: HashSet<(Txid, Address)>,
  ) -> Result {
    if address_transactions.is_empty() {
      return Ok(());
    }

    let blk = BigDecimal::from(block);
    let addr_data: Vec<_> = address_transactions
      .into_iter()
      .map(|(txid, address)| (address.to_string(), txid.to_string()))
      .collect();

    execute_with_retry!(self, "insert address transactions", &self.pg_pool, {
      let mut qb =
        QueryBuilder::new("INSERT INTO public.address_transactions (address, txid, block, reorg) ");
      qb.push_values(&addr_data, |mut b, (addr, txid)| {
        b.push_bind(addr)
          .push_bind(txid)
          .push_bind(&blk)
          .push_bind(false);
      });
      qb.push(
        " ON CONFLICT (address, txid) WHERE NOT reorg DO UPDATE SET
              block = EXCLUDED.block, reorg = EXCLUDED.reorg",
      );
      qb
    })
  }

  pub fn pg_insert_address_transactions_chunked(
    &self,
    block: u32,
    address_transactions: HashSet<(Txid, Address)>,
    chunk_size: usize,
  ) -> Result {
    let items: Vec<_> = address_transactions.into_iter().collect();
    for chunk in items.chunks(chunk_size) {
      self.pg_insert_address_transactions(block, chunk.iter().cloned().collect())?;
    }
    Ok(())
  }

  pub fn pg_mark_reorg(&self, block: u32) -> Result {
    const TABLES: &[&str] = &[
      "runes",
      "transactions",
      "rune_transactions",
      "address_transactions",
      "updated_runes",
      "updated_addresses",
    ];
    let blk = BigDecimal::from(block);

    for table in TABLES {
      loop {
        let affected = self.runtime.block_on(async {
          let mut delay_secs = 1u64;
          loop {
            let sql = format!(
              "WITH to_update AS (
                SELECT id FROM public.{}
                WHERE block >= $1 AND reorg = FALSE
                ORDER BY id LIMIT {}
              )
              UPDATE public.{} SET reorg = TRUE
              WHERE id IN (SELECT id FROM to_update)",
              table, PG_CHUNK_SIZE, table
            );
            match sqlx::query(&sql).bind(&blk).execute(&self.pg_pool).await {
              Ok(result) => {
                log::debug!(
                  "Marked {} rows as reorg in public.{} at height {}",
                  result.rows_affected(),
                  table,
                  block
                );
                return result.rows_affected();
              }
              Err(error) => {
                log::warn!(
                  "mark reorg {} failed, retrying in {}s. Error: {}",
                  table,
                  delay_secs,
                  error
                );
                tokio::time::sleep(Duration::from_secs(delay_secs)).await;
                delay_secs = (delay_secs * 2).min(MAX_RETRY_DELAY_SECS);
              }
            }
          }
        });

        if affected == 0 {
          break;
        }
      }
    }

    Ok(())
  }

  pub fn pg_insert_runes_chunked(
    &self,
    runes: HashMap<RuneId, RuneEntry>,
    chunk_size: usize,
  ) -> Result {
    let items: Vec<_> = runes.into_iter().collect();
    for chunk in items.chunks(chunk_size) {
      self.pg_insert_runes(chunk.iter().cloned().collect())?;
    }
    Ok(())
  }

  pub fn pg_insert_transactions_chunked(
    &self,
    block: u32,
    rs_txs: HashMap<Txid, RsTransaction>,
    chunk_size: usize,
  ) -> Result {
    let items: Vec<_> = rs_txs.into_iter().collect();
    for chunk in items.chunks(chunk_size) {
      self.pg_insert_transactions(block, chunk.iter().cloned().collect())?;
    }
    Ok(())
  }

  fn pg_update_runes(&self, runes: &[(RuneId, u128, u128)]) -> Result {
    if runes.is_empty() {
      return Ok(());
    }

    let runes_data: Vec<_> = runes
      .iter()
      .map(|(rune_id, burned, mints)| {
        (
          rune_id.to_string(),
          BigDecimal::from(*burned),
          BigDecimal::from(*mints),
        )
      })
      .collect();

    execute_with_retry!(self, "update runes", &self.pg_pool, {
      let mut qb = QueryBuilder::new(
        "UPDATE public.runes AS t SET burned = c.burned::numeric, mints = c.mints::numeric FROM (",
      );
      qb.push_values(&runes_data, |mut b, (rune_id, burned, mints)| {
        b.push_bind(rune_id).push_bind(burned).push_bind(mints);
      });
      qb.push(") AS c(rune_id, burned, mints) WHERE c.rune_id = t.rune_id AND t.reorg = false");
      qb
    })
  }

  pub fn pg_update_runes_chunked(
    &self,
    runes: Vec<(RuneId, u128, u128)>,
    chunk_size: usize,
  ) -> Result {
    for chunk in runes.chunks(chunk_size) {
      self.pg_update_runes(chunk)?;
    }
    Ok(())
  }

  fn pg_upsert_address_rune_balances(&self, addresses: &[(Address, RuneId, u128)]) -> Result {
    if addresses.is_empty() {
      return Ok(());
    }

    let addr_data: Vec<_> = addresses
      .iter()
      .map(|(addr, rune_id, balance)| (addr.to_string(), rune_id.to_string(), balance.to_string()))
      .collect();

    execute_with_retry!(self, "upsert address rune balances", &self.pg_pool, {
      let mut qb =
        QueryBuilder::new("INSERT INTO public.address_rune_balance (address, rune_id, balance) ");
      qb.push_values(&addr_data, |mut b, (addr, rune_id, balance)| {
        b.push_bind(addr).push_bind(rune_id).push_bind(balance);
      });
      qb.push(" ON CONFLICT (address, rune_id) DO UPDATE SET balance = EXCLUDED.balance");
      qb
    })
  }

  pub fn pg_upsert_address_rune_balances_chunked(
    &self,
    addresses: Vec<(Address, RuneId, u128)>,
    chunk_size: usize,
  ) -> Result {
    for chunk in addresses.chunks(chunk_size) {
      self.pg_upsert_address_rune_balances(chunk)?;
    }
    Ok(())
  }

  fn pg_clear_rune_balance_addresses(&self, addresses: &[String]) -> Result {
    if addresses.is_empty() {
      return Ok(());
    }

    let result: sqlx::postgres::PgQueryResult = query_with_retry!(
      self,
      "clear rune balance addresses",
      sqlx::query("DELETE FROM public.address_rune_balance WHERE address = ANY($1)")
        .bind(addresses)
        .execute(&self.pg_pool)
    )?;
    log::debug!(
      "clear rune balance addresses: {} rows affected",
      result.rows_affected()
    );
    Ok(())
  }

  pub fn pg_clear_rune_balance_addresses_chunked(
    &self,
    addresses: Vec<String>,
    chunk_size: usize,
  ) -> Result {
    for chunk in addresses.chunks(chunk_size) {
      self.pg_clear_rune_balance_addresses(chunk)?;
    }
    Ok(())
  }

  fn pg_insert_updated_runes(&self, block: u32, updated_runes: HashSet<RuneId>) -> Result {
    if updated_runes.is_empty() {
      return Ok(());
    }

    let blk = BigDecimal::from(block);
    let rune_ids: Vec<_> = updated_runes.into_iter().map(|r| r.to_string()).collect();

    execute_with_retry!(self, "insert updated runes", &self.pg_pool, {
      let mut qb = QueryBuilder::new("INSERT INTO public.updated_runes (rune_id, block, reorg) ");
      qb.push_values(&rune_ids, |mut b, rune_id| {
        b.push_bind(rune_id).push_bind(&blk).push_bind(false);
      });
      qb
    })
  }

  pub fn pg_insert_updated_runes_chunked(
    &self,
    block: u32,
    updated_runes: HashSet<RuneId>,
    chunk_size: usize,
  ) -> Result {
    let items: Vec<_> = updated_runes.into_iter().collect();
    for chunk in items.chunks(chunk_size) {
      self.pg_insert_updated_runes(block, chunk.iter().cloned().collect())?;
    }
    Ok(())
  }

  fn pg_insert_updated_addresses(&self, block: u32, updated_addresses: HashSet<Address>) -> Result {
    if updated_addresses.is_empty() {
      return Ok(());
    }

    let blk = BigDecimal::from(block);
    let addrs: Vec<_> = updated_addresses
      .into_iter()
      .map(|a| a.to_string())
      .collect();

    execute_with_retry!(self, "insert updated addresses", &self.pg_pool, {
      let mut qb =
        QueryBuilder::new("INSERT INTO public.updated_addresses (address, block, reorg) ");
      qb.push_values(&addrs, |mut b, addr| {
        b.push_bind(addr).push_bind(&blk).push_bind(false);
      });
      qb
    })
  }

  pub fn pg_insert_updated_addresses_chunked(
    &self,
    block: u32,
    updated_addresses: HashSet<Address>,
    chunk_size: usize,
  ) -> Result {
    let items: Vec<_> = updated_addresses.into_iter().collect();
    for chunk in items.chunks(chunk_size) {
      self.pg_insert_updated_addresses(block, chunk.iter().cloned().collect())?;
    }
    Ok(())
  }

  pub fn pg_query_updated_runes(&self, block: u32) -> Result<HashSet<RuneId>> {
    let blk = BigDecimal::from(block);
    let rows: Vec<sqlx::postgres::PgRow> = query_with_retry!(
      self,
      "query updated runes",
      sqlx::query("SELECT rune_id FROM public.updated_runes WHERE block >= $1 AND reorg = FALSE")
        .bind(&blk)
        .fetch_all(&self.pg_pool)
    )?;

    Ok(
      rows
        .iter()
        .map(|row| RuneId::from_str(&row.get::<String, _>(0)).unwrap())
        .collect(),
    )
  }

  pub fn pg_query_updated_addresses(&self, block: u32) -> Result<HashSet<Address>> {
    let blk = BigDecimal::from(block);
    let rows: Vec<sqlx::postgres::PgRow> = query_with_retry!(
      self,
      "query updated addresses",
      sqlx::query(
        "SELECT address FROM public.updated_addresses WHERE block >= $1 AND reorg = FALSE"
      )
      .bind(&blk)
      .fetch_all(&self.pg_pool)
    )?;

    Ok(
      rows
        .iter()
        .map(|row| {
          row
            .get::<String, _>(0)
            .parse::<bitcoin::Address<_>>()
            .unwrap()
            .assume_checked()
        })
        .collect(),
    )
  }
}

#[derive(Debug, Default)]
pub struct RsUpdates {
  pub rs_tx: RsTransaction,
  pub runes: HashMap<RuneId, RuneEntry>,
  pub transactions: HashMap<Txid, RsTransaction>,
  pub rune_transactions: HashMap<(Txid, RuneId), TxTag>,
  pub address_transactions: HashSet<(Txid, Address)>,
  pub updated_addresses: HashSet<Address>,
  pub updated_runes: HashSet<RuneId>,
}

#[derive(Debug, Default, Clone)]
pub struct TxTag {
  pub burn: bool,
  pub etch: bool,
  pub mint: bool,
  pub transfer: bool,
}
