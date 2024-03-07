use super::*;

use sqlx::{
  postgres::{PgPool, PgPoolOptions},
  types::{time::OffsetDateTime, BigDecimal},
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

  pub fn pg_insert_rs_transaction(&self, txid: Txid, rs_tx: &RsTransaction) -> Result<()> {
    self.runtime.block_on(async {
      let result = sqlx::query!(
        r#"
          INSERT INTO public.rs_transactions (txid, transaction)
          VALUES ($1, $2)
          ON CONFLICT (txid) DO NOTHING
        "#,
        txid.to_string(),
        serde_json::to_value(rs_tx)?,
      )
      .execute(&self.pg_pool)
      .await;

      match result {
        Ok(_) => {
          log::debug!("INSERT INTO rs_transactions: {}", txid);
        }
        Err(error) => {
          log::error!("An error occurred INSERT INTO rs_transactions: {}", error);
        }
      }

      Ok(())
    })
  }

  pub fn pg_insert_rune(&self, rune_id: RuneId, rune_entry: RuneEntry) -> Result<()> {
    self.runtime.block_on(async {
    let result = sqlx::query!(
      r#"
          INSERT INTO public.runes
          (number, rune_id, spaced_rune, divisibility, symbol, etching, premine, terms_amount, terms_cap, terms_height_start, terms_height_end, terms_offset_start, terms_offset_end, mints, burned, block, timestamp, turbo)
          VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13, $14, $15, $16, $17, $18)
        "#,
      BigDecimal::from(rune_entry.number),
      rune_id.to_string(),
      rune_entry.spaced_rune.to_string(),
      rune_entry.divisibility as i16,
      rune_entry.symbol.map(|s|s.to_string()),
      rune_entry.etching.to_string(),
      BigDecimal::from(rune_entry.premine),
      rune_entry.terms.and_then(|t|t.amount).map(|n| BigDecimal::from(n)),
      rune_entry.terms.and_then(|t|t.cap).map(|n| BigDecimal::from(n)),
      rune_entry.terms.and_then(|t|t.height.0).map(|n| BigDecimal::from(n)),
      rune_entry.terms.and_then(|t|t.height.1).map(|n| BigDecimal::from(n)),
      rune_entry.terms.and_then(|t|t.offset.0).map(|n| BigDecimal::from(n)),
      rune_entry.terms.and_then(|t|t.offset.1).map(|n| BigDecimal::from(n)),
      BigDecimal::from(rune_entry.mints),
      BigDecimal::from(rune_entry.burned),
      BigDecimal::from(rune_entry.block),
      OffsetDateTime::from_unix_timestamp(rune_entry.timestamp as i64).unwrap(),
      rune_entry.turbo,
    )
    .execute(&self.pg_pool)
    .await;

    match result {
      Ok(_) => {
        log::debug!(
          "INSERT INTO public.runes: {},{}",
          rune_id,
          rune_entry.etching
        );
      }
      Err(error) => {
        log::error!(
          "An error occurred INSERT INTO public.runes: {},{}",
          rune_id,
          error
        );
      }
    }

    Ok(())
})
  }

  pub fn pg_update_rune_burned(&self, rune_id: RuneId, burned: u128) -> Result<(), sqlx::Error> {
    self.runtime.block_on(async {
      let result = sqlx::query!(
        r#"
          UPDATE public.runes
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
          log::debug!("UPDATE public.runes: {}, new burned: {}", rune_id, burned);
        }
        Err(error) => {
          log::error!(
            "An error occurred UPDATE public.runes: {}, new burned: {}, err: {}",
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
          UPDATE public.runes
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
          log::debug!("UPDATE public.runes: {}, new mints: {}", rune_id, mints);
        }
        Err(error) => {
          log::error!(
            "An error occurred UPDATE public.runes: {}, new mints: {}, err: {}",
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

  pub fn pg_insert_rune_transaction(
    &self,
    rune_id: RuneId,
    txid: Txid,
    block: u64,
    timestamp: u32,
  ) -> Result<()> {
    self.runtime.block_on(async {
      let result = sqlx::query!(
        r#"
          INSERT INTO public.rune_transactions (rune_id, txid, block, timestamp)
          VALUES ($1, $2, $3, $4)
          ON CONFLICT (rune_id, txid) DO NOTHING
        "#,
        rune_id.to_string(),
        txid.to_string(),
        BigDecimal::from(block),
        OffsetDateTime::from_unix_timestamp(timestamp as i64).unwrap()
      )
      .execute(&self.pg_pool)
      .await;

      match result {
        Ok(_) => {
          log::debug!("INSERT INTO rune_transactions: {}", txid);
        }
        Err(error) => {
          log::error!(
            "An error occurred INSERT INTO rune_transactions: {}, rune_id: {:?}, txid: {:?}",
            error,
            rune_id.to_string(),
            txid.to_string()
          );
        }
      }

      Ok(())
    })
  }

  pub fn pg_insert_address_transaction(&self, address: Address, txid: Txid) -> Result<()> {
    self.runtime.block_on(async {
      let result = sqlx::query!(
        r#"
          INSERT INTO public.address_transactions (address, txid)
          VALUES ($1, $2)
          ON CONFLICT (address, txid) DO NOTHING
        "#,
        address.to_string(),
        txid.to_string(),
      )
      .execute(&self.pg_pool)
      .await;

      match result {
        Ok(_) => {
          log::debug!("INSERT INTO address_transactions: {},{}", txid, address);
        }
        Err(error) => {
          log::error!(
            "An error occurred INSERT INTO address_transactions: {},{},{}",
            txid,
            address,
            error
          );
        }
      }

      Ok(())
    })
  }
}
