use super::*;

use crate::index::lot::Lot;
use ordinals::RsTransaction;
use sqlx::{
  postgres::{PgPool, PgPoolOptions},
  types::{time::OffsetDateTime, BigDecimal},
  Execute, QueryBuilder,
};
use std::env;
use tokio::runtime::Runtime;

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
      .block_on(async { PgPoolOptions::new().connect(&database_url).await })
      .unwrap();

    Self { runtime, pg_pool }
  }

  pub fn pg_insert_runes(&self, runes: HashMap<RuneId, RuneEntry>) -> Result {
    if runes.is_empty() {
      return Ok(());
    }
    let mut query_builder = QueryBuilder::new("INSERT INTO public.runes (number, rune_id, spaced_rune, divisibility, symbol, etching, premine, terms_amount, terms_cap, terms_height_start, terms_height_end, terms_offset_start, terms_offset_end, mints, burned, block, timestamp, turbo) ");

    query_builder.push_values(runes, |mut b, rune| {
      let rune_id = rune.0;
      let rune_entry = rune.1;

      b.push_bind(BigDecimal::from(rune_entry.number))
        .push_bind(rune_id.to_string())
        .push_bind(rune_entry.spaced_rune.to_string())
        .push_bind(rune_entry.divisibility as i16)
        .push_bind(rune_entry.symbol.map(|s| s.to_string()))
        .push_bind(rune_entry.etching.to_string())
        .push_bind(BigDecimal::from(rune_entry.premine))
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.amount)
            .map(|n| BigDecimal::from(n)),
        )
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.cap)
            .map(|n| BigDecimal::from(n)),
        )
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.height.0)
            .map(|n| BigDecimal::from(n)),
        )
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.height.1)
            .map(|n| BigDecimal::from(n)),
        )
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.offset.0)
            .map(|n| BigDecimal::from(n)),
        )
        .push_bind(
          rune_entry
            .terms
            .and_then(|t| t.offset.1)
            .map(|n| BigDecimal::from(n)),
        )
        .push_bind(BigDecimal::from(rune_entry.mints))
        .push_bind(BigDecimal::from(rune_entry.burned))
        .push_bind(BigDecimal::from(rune_entry.block))
        .push_bind(OffsetDateTime::from_unix_timestamp(rune_entry.timestamp as i64).unwrap())
        .push_bind(rune_entry.turbo);
    });

    let query = query_builder.build();

    self.runtime.block_on(async {
      let result = query.execute(&self.pg_pool).await;
      match result {
        Ok(_) => {}
        Err(error) => {
          log::error!("An error occurred INSERT INTO public.runes: {}", error);
        }
      }
    });

    Ok(())
  }

  pub fn pg_insert_transactions(&self, block: u32, rs_txs: HashMap<Txid, RsTransaction>) -> Result {
    if rs_txs.is_empty() {
      return Ok(());
    }
    let mut query_builder =
      QueryBuilder::new("INSERT INTO public.transactions (txid, transaction, block) ");

    query_builder.push_values(rs_txs, |mut b, rs_tx| {
      b.push_bind(rs_tx.0.to_string())
        .push_bind(serde_json::to_value(rs_tx.1).unwrap())
        .push_bind(BigDecimal::from(block));
    });

    let query = query_builder.build();

    self.runtime.block_on(async {
      let result = query.execute(&self.pg_pool).await;
      match result {
        Ok(_) => {}
        Err(error) => {
          log::error!("An error occurred INSERT INTO transactions: {}", error);
        }
      }

      Ok(())
    })
  }

  pub fn pg_insert_rune_burned(&self, block: u32, burned: HashMap<RuneId, Lot>) -> Result {
    if burned.is_empty() {
      return Ok(());
    }

    let mut query_builder =
      QueryBuilder::new("INSERT INTO public.rune_burned (rune_id, burned, block) ");

    query_builder.push_values(burned, |mut b, rune_burned| {
      let rune_id = rune_burned.0;
      let burned_amount = rune_burned.1 .0;
      b.push_bind(rune_id.to_string())
        .push_bind(BigDecimal::from(burned_amount))
        .push_bind(BigDecimal::from(block));
    });

    let query = query_builder.build();

    self.runtime.block_on(async {
      let result = query.execute(&self.pg_pool).await;

      match result {
        Ok(_) => {}
        Err(error) => {
          log::error!("An error occurred INSERT public.rune_burned: {}", error);
        }
      }

      Ok(())
    })
  }

  pub fn pg_insert_rune_mints(&self, block: u32, mints: HashMap<RuneId, u128>) -> Result {
    if mints.is_empty() {
      return Ok(());
    }

    let mut query_builder =
      QueryBuilder::new("INSERT INTO public.rune_mints (rune_id, mints, block) ");

    query_builder.push_values(mints, |mut b, rune_mints| {
      let rune_id = rune_mints.0;
      let mints_amount = rune_mints.1;
      b.push_bind(rune_id.to_string())
        .push_bind(BigDecimal::from(mints_amount))
        .push_bind(BigDecimal::from(block));
    });

    let query = query_builder.build();

    self.runtime.block_on(async {
      let result = query.execute(&self.pg_pool).await;

      match result {
        Ok(_) => {}
        Err(error) => {
          log::error!("An error occurred INSERT public.rune_mints: {}", error);
        }
      }

      Ok(())
    })
  }

  pub fn pg_insert_rune_balances(
    &self,
    block: u32,
    rune_balances: HashMap<(Address, RuneId), Vec<(bool, u128)>>,
  ) -> Result {
    let mut balances: HashMap<(Address, RuneId), (bool, u128)> = HashMap::new();
    for ((address, rune_id), changes) in &rune_balances {
      let mut increase_total: u128 = 0;
      let mut decrease_total: u128 = 0;
      for (is_increased, amount) in changes {
        if *is_increased {
          increase_total += *amount;
        } else {
          decrease_total += *amount;
        }
      }
      if increase_total > decrease_total {
        let diff = increase_total - decrease_total;
        balances.insert((address.clone(), *rune_id), (true, diff));
      } else if decrease_total > increase_total {
        let diff = decrease_total - increase_total;
        balances.insert((address.clone(), *rune_id), (false, diff));
      }
    }
    if balances.is_empty() {
      return Ok(());
    }

    if balances.len() > 10000 {
      log::warn!("There are too many({}) rune_balance to insert at block {}, so we will insert them in batches.", balances.len(), block);
    }

    let keys: Vec<_> = balances.keys().cloned().collect();
    let chunks = keys.chunks(10000);

    for chunk in chunks {
      let mut query_builder = QueryBuilder::new(
        "INSERT INTO public.rune_balances (rune_id, address, is_increased, amount, block) ",
      );
      query_builder.push_values(chunk, |mut b, value| {
        let rune_id = value.1;
        let address = value.0.clone();
        let is_increased = balances.get(&value).unwrap().0;
        let amount = balances.get(&value).unwrap().1;

        b.push_bind(rune_id.to_string())
          .push_bind(address.to_string())
          .push_bind(is_increased)
          .push_bind(BigDecimal::from(amount))
          .push_bind(BigDecimal::from(block));
      });

      let query = query_builder.build();
      let sql = query.sql();

      self.runtime.block_on(async {
        let result = query.execute(&self.pg_pool).await;

        match result {
          Ok(_) => {}
          Err(error) => {
            log::error!(
              "An error occurred INSERT public.rune_balances: {}, sql: {}",
              error,
              sql
            );
          }
        }
      });
    }
    Ok(())
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

    if rune_transactions.len() > 5000 {
      log::warn!("There are too many({}) rune_transactions to insert at block {}, so we will insert them in batches.", rune_transactions.len(), block);
    }

    let keys: Vec<_> = rune_transactions.keys().cloned().collect();
    let chunks = keys.chunks(5000);

    for chunk in chunks {
      let mut query_builder =
      QueryBuilder::new("INSERT INTO public.rune_transactions (rune_id, txid, burn, etch, mint, transfer, block, timestamp) ");

      query_builder.push_values(chunk, |mut b, rt| {
        let txid = rt.0;
        let rune_id = rt.1;
        let tags = rune_transactions.get(&rt).unwrap();

        b.push_bind(rune_id.to_string())
          .push_bind(txid.to_string())
          .push_bind(tags.burn)
          .push_bind(tags.etch)
          .push_bind(tags.mint)
          .push_bind(tags.transfer)
          .push_bind(BigDecimal::from(block))
          .push_bind(OffsetDateTime::from_unix_timestamp(timestamp as i64).unwrap());
      });

      let query = query_builder.build();

      self.runtime.block_on(async {
        let result = query.execute(&self.pg_pool).await;
        match result {
          Ok(_) => {}
          Err(error) => {
            log::error!("An error occurred INSERT INTO rune_transactions: {}", error,);
          }
        }
      });
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
    if address_transactions.len() > 10000 {
      log::warn!("There are too many({}) address_transaction to insert at block {}, so we will insert them in batches.", address_transactions.len(), block);
    }
    let ats: Vec<_> = address_transactions.into_iter().collect();
    let chunks = ats.chunks(10000);

    for chunk in chunks {
      let mut query_builder =
        QueryBuilder::new("INSERT INTO public.address_transactions (address, txid, block) ");

      query_builder.push_values(chunk, |mut b, at| {
        let txid = at.0;
        let address = at.1.clone();

        b.push_bind(address.to_string())
          .push_bind(txid.to_string())
          .push_bind(BigDecimal::from(block));
      });

      let query = query_builder.build();

      self.runtime.block_on(async {
        let result = query.execute(&self.pg_pool).await;

        match result {
          Ok(_) => {}
          Err(error) => {
            log::error!(
              "An error occurred INSERT INTO address_transactions: {}",
              error
            );
          }
        }
      });
    }
    Ok(())
  }

  pub fn pg_mark_reorg(&self, block: u32) -> Result {
    let tables = vec![
      "runes",
      "transactions",
      "rune_burned",
      "rune_mints",
      "rune_balances",
      "rune_transactions",
      "address_transactions",
    ];
    for table in tables.iter() {
      self.runtime.block_on(async {
        let result = sqlx::query(&format!(
          "UPDATE public.{} SET reorg = TRUE WHERE block >= $1",
          table
        ))
        .bind(BigDecimal::from(block))
        .execute(&self.pg_pool)
        .await;

        match result {
          Ok(_) => {
            log::debug!(
              "public.{} has been successfully rolled back to height {}",
              table,
              block
            );
          }
          Err(error) => {
            log::error!(
              "An error occurred when rolling back public.{} to height {}: {}",
              table,
              block,
              error
            );
          }
        }
      });
    }

    Ok(())
  }
}

#[derive(Debug, Default)]
pub struct RsUpdates {
  pub rs_tx: RsTransaction,
  pub runes: HashMap<RuneId, RuneEntry>,
  pub transactions: HashMap<Txid, RsTransaction>,
  /// Stores the balance changes for each rune and address.
  ///
  /// The key of the HashMap is a tuple containing an address and a RuneId.
  /// The value is a vector of tuples, where each tuple represents a balance change.
  /// The first element of the tuple is a boolean that indicates the type of change:
  /// - `true` represents an increase in balance.
  /// - `false` represents a decrease in balance.
  /// The second element of the tuple is the amount of the change.
  pub rune_balances: HashMap<(Address, RuneId), Vec<(bool, u128)>>,
  pub rune_transactions: HashMap<(Txid, RuneId), TxTag>,
  pub address_transactions: HashSet<(Txid, Address)>,
  pub mints: HashMap<RuneId, u128>,
}

#[derive(Debug, Default)]
pub struct TxTag {
  pub burn: bool,
  pub etch: bool,
  pub mint: bool,
  pub transfer: bool,
}
