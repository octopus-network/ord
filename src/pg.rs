use super::*;

use sqlx::{
  postgres::{PgPool, PgPoolOptions},
  types::{time::OffsetDateTime, BigDecimal},
  QueryBuilder,
};
use std::env;
use tokio::runtime::Runtime;
use {num_traits::cast::ToPrimitive, ordinals::RsTransaction};

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
    let mut query_builder = QueryBuilder::new("INSERT INTO public.rs_runes (number, rune_id, spaced_rune, divisibility, symbol, etching, premine, terms_amount, terms_cap, terms_height_start, terms_height_end, terms_offset_start, terms_offset_end, mints, burned, block, timestamp, turbo) ");

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
          log::error!("An error occurred INSERT INTO public.rs_runes: {}", error);
        }
      }
    });

    Ok(())
  }

  pub fn pg_insert_rs_transactions(&self, rs_txs: HashMap<Txid, RsTransaction>) -> Result {
    if rs_txs.is_empty() {
      return Ok(());
    }
    let mut query_builder =
      QueryBuilder::new("INSERT INTO public.rs_transactions (txid, transaction) ");

    query_builder.push_values(rs_txs, |mut b, rs_tx| {
      b.push_bind(rs_tx.0.to_string())
        .push_bind(serde_json::to_value(rs_tx.1).unwrap());
    });

    let query = query_builder.build();

    self.runtime.block_on(async {
      let result = query.execute(&self.pg_pool).await;
      match result {
        Ok(_) => {}
        Err(error) => {
          log::error!("An error occurred INSERT INTO rs_transactions: {}", error);
        }
      }

      Ok(())
    })
  }

  pub fn pg_update_rune_burned(&self, rune_id: RuneId, burned: u128) -> Result<(), sqlx::Error> {
    self.runtime.block_on(async {
      let result = sqlx::query!(
        r#"
          UPDATE public.rs_runes
          SET burned = $2
          WHERE rune_id = $1
      "#,
        rune_id.to_string(),
        BigDecimal::from(burned)
      )
      .execute(&self.pg_pool)
      .await;

      match result {
        Ok(_) => {
          log::debug!(
            "UPDATE public.rs_runes: {}, new burned: {}",
            rune_id,
            burned
          );
        }
        Err(error) => {
          log::error!(
            "An error occurred UPDATE public.rs_runes: {}, new burned: {}, err: {}",
            rune_id,
            burned,
            error
          );
        }
      }

      Ok(())
    })
  }

  pub fn pg_update_rune_mints(&self, rune_id: RuneId, mints: u128) -> Result<(), sqlx::Error> {
    self.runtime.block_on(async {
      let result = sqlx::query!(
        r#"
          UPDATE public.rs_runes
          SET mints = $2
          WHERE rune_id = $1
      "#,
        rune_id.to_string(),
        BigDecimal::from(mints)
      )
      .execute(&self.pg_pool)
      .await;

      match result {
        Ok(_) => {
          log::debug!("UPDATE public.rs_runes: {}, new mints: {}", rune_id, mints);
        }
        Err(error) => {
          log::error!(
            "An error occurred UPDATE public.rs_runes: {}, new mints: {}, err: {}",
            rune_id,
            mints,
            error
          );
        }
      }

      Ok(())
    })
  }

  pub fn pg_query_rune_balance(
    &self,
    rune_id: RuneId,
    address: Address,
  ) -> Result<Option<u128>, sqlx::Error> {
    self.runtime.block_on(async {
      let result = sqlx::query!(
        r#"
          SELECT rune_id, address, amount
          FROM public.rune_balances
          WHERE rune_id = $1 AND address = $2
        "#,
        rune_id.to_string(),
        address.to_string(),
      )
      .fetch_optional(&self.pg_pool)
      .await;
      match result {
        Ok(row) => {
          log::debug!("QUERY public.rune_balances: {}, {}", rune_id, address);
          return Ok(row.map(|r| r.amount.to_u128().unwrap()));
        }
        Err(error) => {
          log::error!(
            "An error occurred QUERY public.rune_balances: {},{},{}",
            rune_id,
            address,
            error
          );
          return Err(error);
        }
      }
    })
  }

  pub fn pg_update_rune_balance(
    &self,
    rune_id: RuneId,
    address: Address,
    amount: u128,
  ) -> Result<(), sqlx::Error> {
    self.runtime.block_on(async {
      let result = sqlx::query!(
        r#"
          INSERT INTO public.rune_balances (rune_id, address, amount)
          VALUES ($1, $2, $3)
          ON CONFLICT (rune_id, address)
          DO UPDATE SET amount = EXCLUDED.amount
        "#,
        rune_id.to_string(),
        address.to_string(),
        BigDecimal::from(amount)
      )
      .execute(&self.pg_pool)
      .await;

      match result {
        Ok(_) => {
          log::debug!("UPDATE public.rune_balances: {},{}", rune_id, address);
          Ok(())
        }
        Err(error) => {
          log::error!(
            "An error occurred UPDATE public.rune_balances: {},{},{}",
            rune_id,
            address,
            error
          );
          Err(error)
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
    let mut query_builder =
      QueryBuilder::new("INSERT INTO public.rune_transactions (rune_id, txid, burn, etch, mint, transfer, block, timestamp) ");

    query_builder.push_values(rune_transactions, |mut b, rt| {
      let txid = rt.0 .0;
      let rune_id = rt.0 .1;
      let tags = rt.1;

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

      Ok(())
    })
  }

  pub fn pg_insert_address_transactions(
    &self,
    address_transactions: HashSet<(Txid, Address)>,
  ) -> Result {
    if address_transactions.is_empty() {
      return Ok(());
    }
    let mut query_builder =
      QueryBuilder::new("INSERT INTO public.address_transactions (address, txid) ");

    query_builder.push_values(address_transactions, |mut b, at| {
      let txid = at.0;
      let address = at.1;

      b.push_bind(address.to_string()).push_bind(txid.to_string());
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

      Ok(())
    })
  }
}

#[derive(Debug, Default)]
pub struct RsUpdates {
  pub rs_tx: RsTransaction,
  pub rs_runes: HashMap<RuneId, RuneEntry>,
  pub rs_transactions: HashMap<Txid, RsTransaction>,
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
