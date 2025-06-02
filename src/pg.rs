use super::*;

use bitcoin::{address::Address, Amount, OutPoint};
use sqlx::{
  postgres::{PgPool, PgPoolOptions},
  types::{time::OffsetDateTime, BigDecimal},
  Execute, QueryBuilder, Row,
};
use std::collections::HashMap;
use std::env;
use tokio::runtime::Runtime;

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
  pub runes: Vec<(RuneId, String)>,
}

#[derive(Serialize, Debug, Clone)]
pub struct RsTxOut {
  pub value: Amount,
  pub address: Option<Address>,
  pub op_return: Option<Artifact>,
  pub runes: Vec<(RuneId, String)>,
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

    let mut query_builder = QueryBuilder::new(
      "INSERT INTO public.runes (
        number, rune_id, burned, divisibility, etching,
        mints, premine, spaced_rune, symbol,
        terms_cap, terms_height_start, terms_height_end,
        terms_amount, terms_offset_start, terms_offset_end,
        timestamp, turbo, block, reorg
      ) ",
    );

    query_builder.push_values(runes, |mut b, (rune_id, rune_entry)| {
      b.push_bind(BigDecimal::from(rune_entry.number))
        .push_bind(rune_id.to_string())
        .push_bind(BigDecimal::from(rune_entry.burned))
        .push_bind(rune_entry.divisibility as i16)
        .push_bind(rune_entry.etching.to_string())
        .push_bind(BigDecimal::from(rune_entry.mints))
        .push_bind(BigDecimal::from(rune_entry.premine))
        .push_bind(rune_entry.spaced_rune.to_string())
        .push_bind(rune_entry.symbol.map(|s| {
          if s == '\0' {
            log::warn!(
              "Found null byte as symbol - Rune ID: {}.",
              rune_id.to_string()
            );

            None
          } else {
            Some(s.to_string())
          }
        }))
        .push_bind(rune_entry.terms.and_then(|t| t.cap).map(BigDecimal::from))
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.height.0)
            .map(BigDecimal::from),
        )
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.height.1)
            .map(BigDecimal::from),
        )
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.amount)
            .map(BigDecimal::from),
        )
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.offset.0)
            .map(BigDecimal::from),
        )
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.offset.1)
            .map(BigDecimal::from),
        )
        .push_bind(OffsetDateTime::from_unix_timestamp(rune_entry.timestamp as i64).unwrap())
        .push_bind(rune_entry.turbo)
        .push_bind(BigDecimal::from(rune_entry.block))
        .push_bind(false);
    });

    query_builder.push(
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

    let query = query_builder.build();
    let sql = query.sql().to_string();

    self.runtime.block_on(async {
      match query.execute(&self.pg_pool).await {
        Ok(result) => {
          log::debug!("Successfully inserted {} runes", result.rows_affected());
          Ok(())
        }
        Err(error) => {
          panic!("Failed to insert runes. SQL: {}\nError: {}", sql, error);
        }
      }
    })
  }

  pub fn pg_insert_transactions(&self, block: u32, rs_txs: HashMap<Txid, RsTransaction>) -> Result {
    if rs_txs.is_empty() {
      return Ok(());
    }

    let processed_rs_txs = rs_txs
      .into_iter()
      .map(|(txid, mut transaction)| {
        for output in &mut transaction.outputs {
          if let Some(ref mut artifact) = output.op_return {
            if let Artifact::Runestone(ref mut runestone) = artifact {
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

        (txid, transaction)
      })
      .collect::<HashMap<_, _>>();

    let mut query_builder = QueryBuilder::new(
      "INSERT INTO public.transactions (
            txid,
            transaction,
            block,
            reorg
        ) ",
    );

    query_builder.push_values(processed_rs_txs, |mut b, (txid, transaction)| {
      b.push_bind(txid.to_string())
        .push_bind(serde_json::to_value(transaction).unwrap())
        .push_bind(BigDecimal::from(block))
        .push_bind(false);
    });

    query_builder.push(
      " ON CONFLICT (txid) WHERE NOT reorg DO UPDATE SET
            transaction = EXCLUDED.transaction,
            block = EXCLUDED.block,
            reorg = EXCLUDED.reorg",
    );

    let query = query_builder.build();
    let sql = query.sql().to_string();

    self.runtime.block_on(async {
      match query.execute(&self.pg_pool).await {
        Ok(result) => {
          log::debug!(
            "Successfully inserted {} transactions",
            result.rows_affected()
          );
          Ok(())
        }
        Err(error) => {
          panic!(
            "Failed to insert transactions at block {}. SQL: {}\nError: {}",
            block, sql, error
          );
        }
      }
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

    let mut query_builder = QueryBuilder::new(
      "INSERT INTO public.rune_transactions (
            rune_id,
            txid,
            burn,
            etch,
            mint,
            transfer,
            block,
            timestamp,
            reorg
        ) ",
    );

    query_builder.push_values(rune_transactions, |mut b, ((txid, rune_id), tags)| {
      b.push_bind(rune_id.to_string())
        .push_bind(txid.to_string())
        .push_bind(tags.burn)
        .push_bind(tags.etch)
        .push_bind(tags.mint)
        .push_bind(tags.transfer)
        .push_bind(BigDecimal::from(block))
        .push_bind(OffsetDateTime::from_unix_timestamp(timestamp as i64).unwrap())
        .push_bind(false);
    });

    query_builder.push(
      " ON CONFLICT (rune_id, txid) WHERE NOT reorg DO UPDATE SET
            burn = EXCLUDED.burn,
            etch = EXCLUDED.etch,
            mint = EXCLUDED.mint,
            transfer = EXCLUDED.transfer,
            block = EXCLUDED.block,
            timestamp = EXCLUDED.timestamp,
            reorg = EXCLUDED.reorg",
    );

    let query = query_builder.build();
    let sql = query.sql().to_string();

    self.runtime.block_on(async {
      match query.execute(&self.pg_pool).await {
        Ok(result) => {
          log::debug!(
            "Successfully inserted {} rune transactions at block {}",
            result.rows_affected(),
            block
          );
          Ok(())
        }
        Err(error) => {
          panic!(
            "Failed to insert rune transactions at block {}. SQL: {}\nError: {}",
            block, sql, error
          );
        }
      }
    })
  }

  pub fn pg_insert_rune_transactions_chunked(
    &self,
    rune_transactions: HashMap<(Txid, RuneId), TxTag>,
    block: u64,
    timestamp: u32,
    chunk_size: usize,
  ) -> Result {
    if rune_transactions.is_empty() {
      return Ok(());
    }

    for chunk in rune_transactions
      .into_iter()
      .collect::<Vec<_>>()
      .chunks(chunk_size)
    {
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

    let mut query_builder = QueryBuilder::new(
      "INSERT INTO public.address_transactions (
            address,
            txid,
            block,
            reorg
        ) ",
    );

    query_builder.push_values(address_transactions, |mut b, (txid, address)| {
      b.push_bind(address.to_string())
        .push_bind(txid.to_string())
        .push_bind(BigDecimal::from(block))
        .push_bind(false);
    });

    query_builder.push(
      " ON CONFLICT (address, txid) WHERE NOT reorg DO UPDATE SET
            block = EXCLUDED.block,
            reorg = EXCLUDED.reorg",
    );

    let query = query_builder.build();
    let sql = query.sql().to_string();

    self.runtime.block_on(async {
      match query.execute(&self.pg_pool).await {
        Ok(result) => {
          log::debug!(
            "Successfully inserted {} address transactions at block {}",
            result.rows_affected(),
            block
          );
          Ok(())
        }
        Err(error) => {
          panic!(
            "Failed to insert address transactions at block {}. SQL: {}\nError: {}",
            block, sql, error
          );
        }
      }
    })
  }

  pub fn pg_insert_address_transactions_chunked(
    &self,
    block: u32,
    address_transactions: HashSet<(Txid, Address)>,
    chunk_size: usize,
  ) -> Result {
    if address_transactions.is_empty() {
      return Ok(());
    }

    for chunk in address_transactions
      .into_iter()
      .collect::<Vec<_>>()
      .chunks(chunk_size)
    {
      self.pg_insert_address_transactions(block, chunk.iter().cloned().collect())?;
    }
    Ok(())
  }

  pub fn pg_mark_reorg(&self, block: u32) -> Result {
    let tables = vec![
      "runes",
      "transactions",
      "rune_transactions",
      "address_transactions",
      "updated_runes",
      "updated_addresses",
    ];
    for table in tables.iter() {
      loop {
        let affected = self.runtime.block_on(async {
          let result = sqlx::query(&format!(
            "WITH to_update AS (
              SELECT id FROM public.{} 
              WHERE block >= $1 AND reorg = FALSE 
              ORDER BY id LIMIT 1000
            )
            UPDATE public.{} SET reorg = TRUE 
            WHERE id IN (SELECT id FROM to_update)",
            table, table
          ))
          .bind(BigDecimal::from(block))
          .execute(&self.pg_pool)
          .await;

          match result {
            Ok(result) => {
              log::debug!(
                "Marked {} rows as reorg in public.{} at height {}",
                result.rows_affected(),
                table,
                block
              );
              result.rows_affected()
            }
            Err(error) => {
              panic!(
                "Failed to roll back public.{} to height {}. Error: {}",
                table, block, error
              );
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
    for chunk in runes.into_iter().collect::<Vec<_>>().chunks(chunk_size) {
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
    for chunk in rs_txs.into_iter().collect::<Vec<_>>().chunks(chunk_size) {
      self.pg_insert_transactions(block, chunk.iter().cloned().collect())?;
    }
    Ok(())
  }

  fn pg_update_runes(&self, runes: Vec<(RuneId, u128, u128)>) -> Result {
    if runes.is_empty() {
      return Ok(());
    }

    let mut query_builder = QueryBuilder::new(
      "UPDATE public.runes AS t SET
            burned = c.burned::numeric,
            mints = c.mints::numeric
         FROM (",
    );

    query_builder.push_values(runes, |mut b, (rune_id, burned, mints)| {
      b.push_bind(rune_id.to_string())
        .push_bind(BigDecimal::from(burned))
        .push_bind(BigDecimal::from(mints));
    });

    query_builder.push(
      ") AS c(rune_id, burned, mints)
         WHERE c.rune_id = t.rune_id
         AND t.reorg = false",
    );

    let query = query_builder.build();
    let sql = query.sql().to_string();

    self.runtime.block_on(async {
      match query.execute(&self.pg_pool).await {
        Ok(result) => {
          log::debug!(
            "Successfully updated burned and mints for {} runes",
            result.rows_affected()
          );
          Ok(())
        }
        Err(error) => {
          panic!(
            "Failed to update runes burned and mints. SQL: {}\nError: {}",
            sql, error
          );
        }
      }
    })
  }

  pub fn pg_update_runes_chunked(
    &self,
    runes: Vec<(RuneId, u128, u128)>,
    chunk_size: usize,
  ) -> Result {
    if runes.is_empty() {
      return Ok(());
    }

    for chunk in runes.chunks(chunk_size) {
      self.pg_update_runes(chunk.to_vec())?;
    }

    Ok(())
  }

  fn pg_upsert_address_rune_balances(&self, addresses: Vec<(Address, RuneId, u128)>) -> Result {
    if addresses.is_empty() {
      return Ok(());
    }

    let mut query_builder = QueryBuilder::new(
      "INSERT INTO public.address_rune_balance (
            address,
            rune_id,
            balance
        ) ",
    );

    query_builder.push_values(addresses, |mut b, (address, rune_id, balance)| {
      b.push_bind(address.to_string())
        .push_bind(rune_id.to_string())
        .push_bind(BigDecimal::from(balance));
    });

    // Add ON CONFLICT clause for upsert
    query_builder.push(
      " ON CONFLICT (address, rune_id) DO UPDATE SET
            balance = EXCLUDED.balance",
    );

    let query = query_builder.build();
    let sql = query.sql().to_string();

    self.runtime.block_on(async {
      match query.execute(&self.pg_pool).await {
        Ok(result) => {
          log::debug!(
            "Successfully upserted {} address rune balances",
            result.rows_affected()
          );
          Ok(())
        }
        Err(error) => {
          panic!(
            "Failed to upsert address rune balances. SQL: {}\nError: {}",
            sql, error
          );
        }
      }
    })
  }

  pub fn pg_upsert_address_rune_balances_chunked(
    &self,
    addresses: Vec<(Address, RuneId, u128)>,
    chunk_size: usize,
  ) -> Result {
    if addresses.is_empty() {
      return Ok(());
    }

    for chunk in addresses.chunks(chunk_size) {
      self.pg_upsert_address_rune_balances(chunk.to_vec())?;
    }
    Ok(())
  }

  fn pg_clear_rune_balance_addresses(&self, addresses: Vec<String>) -> Result {
    if addresses.is_empty() {
      return Ok(());
    }

    let query = sqlx::query("DELETE FROM public.address_rune_balance WHERE address = ANY($1)")
      .bind(addresses);

    self.runtime.block_on(async {
      match query.execute(&self.pg_pool).await {
        Ok(result) => {
          log::debug!(
            "Successfully deleted {} address rune balance records",
            result.rows_affected()
          );
          Ok(())
        }
        Err(error) => {
          log::error!("Failed to delete address rune balances. Error: {}", error);
          Err(error.into())
        }
      }
    })
  }

  pub fn pg_clear_rune_balance_addresses_chunked(
    &self,
    addresses: Vec<String>,
    chunk_size: usize,
  ) -> Result {
    if addresses.is_empty() {
      return Ok(());
    }

    for chunk in addresses.chunks(chunk_size) {
      self.pg_clear_rune_balance_addresses(chunk.to_vec())?;
    }
    Ok(())
  }

  fn pg_insert_updated_runes(&self, block: u32, updated_runes: HashSet<RuneId>) -> Result {
    if updated_runes.is_empty() {
      return Ok(());
    }

    let mut query_builder = QueryBuilder::new(
      "INSERT INTO public.updated_runes (
            rune_id,
            block,
            reorg
        ) ",
    );

    query_builder.push_values(updated_runes, |mut b, rune_id| {
      b.push_bind(rune_id.to_string())
        .push_bind(BigDecimal::from(block))
        .push_bind(false);
    });

    let query = query_builder.build();
    let sql = query.sql().to_string();

    self.runtime.block_on(async {
      match query.execute(&self.pg_pool).await {
        Ok(result) => {
          log::debug!(
            "Successfully inserted {} updated runes at block {}",
            result.rows_affected(),
            block
          );
          Ok(())
        }
        Err(error) => {
          panic!(
            "Failed to insert updated runes at block {}. SQL: {}\nError: {}",
            block, sql, error
          );
        }
      }
    })
  }

  pub fn pg_insert_updated_runes_chunked(
    &self,
    block: u32,
    updated_runes: HashSet<RuneId>,
    chunk_size: usize,
  ) -> Result {
    if updated_runes.is_empty() {
      return Ok(());
    }

    for chunk in updated_runes
      .into_iter()
      .collect::<Vec<_>>()
      .chunks(chunk_size)
    {
      self.pg_insert_updated_runes(block, chunk.iter().cloned().collect())?;
    }
    Ok(())
  }

  fn pg_insert_updated_addresses(&self, block: u32, updated_addresses: HashSet<Address>) -> Result {
    if updated_addresses.is_empty() {
      return Ok(());
    }

    let mut query_builder = QueryBuilder::new(
      "INSERT INTO public.updated_addresses (
            address,
            block,
            reorg
        ) ",
    );

    query_builder.push_values(updated_addresses, |mut b, address| {
      b.push_bind(address.to_string())
        .push_bind(BigDecimal::from(block))
        .push_bind(false);
    });

    let query = query_builder.build();
    let sql = query.sql().to_string();

    self.runtime.block_on(async {
      match query.execute(&self.pg_pool).await {
        Ok(result) => {
          log::debug!(
            "Successfully inserted {} updated addresses at block {}",
            result.rows_affected(),
            block
          );
          Ok(())
        }
        Err(error) => {
          panic!(
            "Failed to insert updated addresses at block {}. SQL: {}\nError: {}",
            block, sql, error
          );
        }
      }
    })
  }

  pub fn pg_insert_updated_addresses_chunked(
    &self,
    block: u32,
    updated_addresses: HashSet<Address>,
    chunk_size: usize,
  ) -> Result {
    if updated_addresses.is_empty() {
      return Ok(());
    }

    for chunk in updated_addresses
      .into_iter()
      .collect::<Vec<_>>()
      .chunks(chunk_size)
    {
      self.pg_insert_updated_addresses(block, chunk.iter().cloned().collect())?;
    }
    Ok(())
  }

  pub fn pg_query_updated_runes(&self, block: u32) -> Result<HashSet<RuneId>> {
    let query =
      sqlx::query("SELECT rune_id FROM public.updated_runes WHERE block >= $1 AND reorg = FALSE")
        .bind(BigDecimal::from(block));
    let rows = self
      .runtime
      .block_on(async { query.fetch_all(&self.pg_pool).await })?;

    Ok(
      rows
        .iter()
        .map(|row| RuneId::from_str(&row.get::<String, _>(0)).unwrap())
        .collect(),
    )
  }

  pub fn pg_query_updated_addresses(&self, block: u32) -> Result<HashSet<Address>> {
    let query = sqlx::query(
      "SELECT address FROM public.updated_addresses WHERE block >= $1 AND reorg = FALSE",
    )
    .bind(BigDecimal::from(block));
    let rows = self
      .runtime
      .block_on(async { query.fetch_all(&self.pg_pool).await })?;

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
