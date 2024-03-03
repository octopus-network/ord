use {
  super::*,
  crate::{
    index::entry::{OutpointBalance, RuneBalance, TxInput, TxOutput},
    runes::{varint, Edict, Runestone, CLAIM_BIT},
  },
  bigdecimal::{BigDecimal, FromPrimitive, Zero},
  sqlx::{Pool, Postgres},
};

fn claim(id: u128) -> Option<u128> {
  (id & CLAIM_BIT != 0).then_some(id ^ CLAIM_BIT)
}

struct Allocation {
  balance: u128,
  divisibility: u8,
  id: u128,
  mint: Option<MintEntry>,
  rune: Rune,
  spacers: u32,
  symbol: Option<char>,
}

#[derive(Default)]
pub(crate) struct RuneUpdate {
  pub(crate) burned: u128,
  pub(crate) mints: u64,
  pub(crate) supply: u128,
}

pub(super) struct RuneUpdater<'a, 'db, 'tx, 'index> {
  pub(super) height: u32,
  pub(super) id_to_entry: &'a mut Table<'db, 'tx, RuneIdValue, RuneEntryValue>,
  pub(super) inscription_id_to_sequence_number: &'a Table<'db, 'tx, InscriptionIdValue, u32>,
  pub(super) minimum: Rune,
  pub(super) outpoint_to_balances: &'a mut Table<'db, 'tx, &'static OutPointValue, &'static [u8]>,
  pub(super) rune_to_id: &'a mut Table<'db, 'tx, u128, RuneIdValue>,
  pub(super) runes: u64,
  pub(super) sequence_number_to_rune_id: &'a mut Table<'db, 'tx, u32, RuneIdValue>,
  pub(super) statistic_to_count: &'a mut Table<'db, 'tx, u64, u64>,
  pub(super) timestamp: u32,
  pub(super) transaction_id_to_rune: &'a mut Table<'db, 'tx, &'static TxidValue, u128>,
  pub(super) updates: HashMap<RuneId, RuneUpdate>,
  pub(super) index: &'index Index,
}

impl<'a, 'db, 'tx, 'index> RuneUpdater<'a, 'db, 'tx, 'index> {
  pub(super) fn index_runes(&mut self, index: usize, tx: &Transaction, txid: Txid) -> Result<()> {
    let runestone = Runestone::from_transaction(tx);
    // A mapping of rune ID to un-allocated balance of that rune
    let mut unallocated: HashMap<u128, u128> = HashMap::new();
    let mut tx_inputs: Vec<TxInput> = Vec::new();
    let mut tx_outputs: Vec<TxOutput> = Vec::new();
    let mut outpoints: Vec<OutpointBalance> = Vec::new();
    let mut update_rune_balances: Vec<RuneBalance> = Vec::new();
    let mut add_rune_balances: Vec<RuneBalance> = Vec::new();
    // (rune_id, address) -> rune_amount
    let mut rune_balance_map: HashMap<(String, String), BigDecimal> = HashMap::new();
    // Increment unallocated runes with the runes in this transaction's inputs
    for input in &tx.input {
      if let Some(guard) = self
        .outpoint_to_balances
        .remove(&input.previous_output.store())?
      {
        let buffer = guard.value();
        let mut i = 0;
        while i < buffer.len() {
          let (id, len) = varint::decode(&buffer[i..]);
          i += len;
          let (balance, len) = varint::decode(&buffer[i..]);
          i += len;
          *unallocated.entry(id).or_default() += balance;
        }
      }
    }

    let burn = runestone
      .as_ref()
      .map(|runestone| runestone.burn)
      .unwrap_or_default();

    let default_output = runestone.as_ref().and_then(|runestone| {
      runestone
        .default_output
        .and_then(|default| usize::try_from(default).ok())
    });

    // A vector of allocated transaction output rune balances
    let mut allocated: Vec<HashMap<u128, u128>> = vec![HashMap::new(); tx.output.len()];

    if let Some(runestone) = runestone {
      // Determine if this runestone contains a valid issuance
      let mut allocation = match runestone.etching {
        Some(etching) => {
          if etching
            .rune
            .map(|rune| rune < self.minimum || rune.is_reserved())
            .unwrap_or_default()
            || etching
              .rune
              .and_then(|rune| self.rune_to_id.get(rune.0).transpose())
              .transpose()?
              .is_some()
          {
            None
          } else {
            let rune = if let Some(rune) = etching.rune {
              log::info!("runestone.etching rune: {}", rune.clone());
              rune
            } else {
              let reserved_runes = self
                .statistic_to_count
                .get(&Statistic::ReservedRunes.into())?
                .map(|entry| entry.value())
                .unwrap_or_default();

              self
                .statistic_to_count
                .insert(&Statistic::ReservedRunes.into(), reserved_runes + 1)?;

              Rune::reserved(reserved_runes.into())
            };

            // Construct an allocation, representing the new runes that may be
            // allocated. Beware: Because it would require constructing a block
            // with 2**16 + 1 transactions, there is no test that checks that
            // an eching in a transaction with an out-of-bounds index is
            // ignored.
            match u16::try_from(index) {
              Ok(index) => Some(Allocation {
                balance: if let Some(mint) = etching.mint {
                  if mint.term == Some(0) {
                    0
                  } else {
                    mint.limit.unwrap_or(runes::MAX_LIMIT)
                  }
                } else {
                  u128::max_value()
                },
                divisibility: etching.divisibility,
                id: u128::from(self.height) << 16 | u128::from(index),
                rune,
                spacers: etching.spacers,
                symbol: etching.symbol,
                mint: etching.mint.map(|mint| MintEntry {
                  deadline: mint.deadline,
                  end: mint.term.map(|term| term + self.height),
                  limit: mint.limit.map(|limit| limit.min(runes::MAX_LIMIT)),
                }),
              }),
              Err(_) => None,
            }
          }
        }
        None => None,
      };

      // handle runes related outputs
      for (output_n, txout) in tx.output.iter().enumerate() {
        let mut tx_output = TxOutput::from_txout(txout, &txid, output_n as i32);

        if tx_output.is_op_return {
          let json_value = serde_json::to_value(runestone.clone()).ok();
          tx_output.op_return_data = json_value;
        }
        tx_outputs.push(tx_output.clone());
      }

      if !burn {
        let mut mintable: HashMap<u128, u128> = HashMap::new();

        let mut claims = runestone
          .edicts
          .iter()
          .filter_map(|edict| claim(edict.id))
          .collect::<Vec<u128>>();
        claims.sort();
        claims.dedup();
        for id in claims {
          if let Ok(key) = RuneId::try_from(id) {
            if let Some(entry) = self.id_to_entry.get(&key.store())? {
              let entry = RuneEntry::load(entry.value());
              if let Some(mint) = entry.mint {
                if let Some(end) = mint.end {
                  if self.height >= end {
                    continue;
                  }
                }
                if let Some(deadline) = mint.deadline {
                  if self.timestamp >= deadline {
                    continue;
                  }
                }
                mintable.insert(id, mint.limit.unwrap_or(runes::MAX_LIMIT));
              }
            }
          }
        }

        let limits = mintable.clone();

        for Edict { id, amount, output } in runestone.edicts {
          let Ok(output) = usize::try_from(output) else {
            continue;
          };

          // Skip edicts not referring to valid outputs
          if output > tx.output.len() {
            continue;
          }

          let (balance, id) = if id == 0 {
            // If this edict allocates new issuance runes, skip it
            // if no issuance was present, or if the issuance was invalid.
            // Additionally, replace ID 0 with the newly assigned ID, and
            // get the unallocated balance of the issuance.
            match allocation.as_mut() {
              Some(Allocation { balance, id, .. }) => (balance, *id),
              None => continue,
            }
          } else if let Some(claim) = claim(id) {
            match mintable.get_mut(&claim) {
              Some(balance) => (balance, claim),
              None => continue,
            }
          } else {
            // Get the unallocated balance of the given ID
            match unallocated.get_mut(&id) {
              Some(balance) => (balance, id),
              None => continue,
            }
          };

          let mut allocate = |balance: &mut u128, amount: u128, output: usize| {
            if amount > 0 {
              *balance -= amount;
              *allocated[output].entry(id).or_default() += amount;
            }
          };

          if output == tx.output.len() {
            // find non-OP_RETURN outputs
            let destinations = tx
              .output
              .iter()
              .enumerate()
              .filter_map(|(output, tx_out)| {
                (!tx_out.script_pubkey.is_op_return()).then_some(output)
              })
              .collect::<Vec<usize>>();

            if amount == 0 {
              // if amount is zero, divide balance between eligible outputs
              let amount = *balance / destinations.len() as u128;
              let remainder = usize::try_from(*balance % destinations.len() as u128).unwrap();

              for (i, output) in destinations.iter().enumerate() {
                allocate(
                  balance,
                  if i < remainder { amount + 1 } else { amount },
                  *output,
                );
              }
            } else {
              // if amount is non-zero, distribute amount to eligible outputs
              for output in destinations {
                allocate(balance, amount.min(*balance), output);
              }
            }
          } else {
            // Get the allocatable amount
            let amount = if amount == 0 {
              *balance
            } else {
              amount.min(*balance)
            };

            allocate(balance, amount, output);
          }

          log::info!("runestone.edicts edict.id: {}", id);
          let hex_rune_id = if id == 0 {
            match allocation.as_mut() {
              Some(Allocation { id, .. }) => {
                let edicting_rune_id = format!("{:x}", *id);
                log::info!("runestone.edicts edicting_rune_id: {}", &edicting_rune_id);
                edicting_rune_id
              }
              None => continue,
            }
          } else {
            let edicts_rune_id = format!("{:x}", id);
            log::info!("runestone.edicts edicts_rune_id: {}", &edicts_rune_id);
            edicts_rune_id
          };

          // handle runes related outpoits
          for (output_n, txout) in tx.output.iter().enumerate() {
            if !txout.script_pubkey.is_op_return() && output_n == output {
              let outpoint = OutpointBalance {
                tx_id: txid.to_string().clone(),
                vout: output as i32,
                address: self
                  .get_address_from_script_pubkey(txout.script_pubkey.clone().into_bytes()),
                rune_id: hex_rune_id.clone(),
                rune_amount: BigDecimal::from_i128(amount as i128).unwrap_or(BigDecimal::from(0)),
                burn,
                spent: false,
                value: txout.value as i64,
              };
              outpoints.push(outpoint.clone());

              let key = (outpoint.rune_id.clone(), outpoint.address.clone());
              rune_balance_map
                .entry(key)
                .and_modify(|amount| *amount += &outpoint.rune_amount)
                .or_insert_with(|| outpoint.rune_amount.clone());
            }
          }
        }

        // increment entries with minted runes
        for (id, amount) in mintable {
          let minted = limits[&id] - amount;
          if minted > 0 {
            let update = self
              .updates
              .entry(RuneId::try_from(id).unwrap())
              .or_default();
            update.mints += 1;
            update.supply += minted;
          }
        }
      }

      if let Some(Allocation {
        balance,
        divisibility,
        id,
        mint,
        rune,
        spacers,
        symbol,
      }) = allocation
      {
        let id = RuneId::try_from(id).unwrap();
        self.rune_to_id.insert(rune.0, id.store())?;
        self.transaction_id_to_rune.insert(&txid.store(), rune.0)?;
        let number = self.runes;
        self.runes += 1;
        self
          .statistic_to_count
          .insert(&Statistic::Runes.into(), self.runes)?;

        let hex_rune_id = format!("{:x}", u128::from(id));
        let rune_entry = RuneEntry {
          burned: 0,
          divisibility,
          etching: txid,
          mints: 0,
          number,
          mint: mint.and_then(|mint| (!burn).then_some(mint)),
          rune,
          spacers,
          supply: if let Some(mint) = mint {
            if mint.end == Some(self.height) {
              0
            } else {
              mint.limit.unwrap_or(runes::MAX_LIMIT)
            }
          } else {
            u128::max_value()
          } - balance,
          symbol,
          timestamp: self.timestamp,
        };
        if let (Some(pg_pool), Some(runtime)) = (&self.index.pg_pool, &self.index.runtime) {
          runtime.block_on(async {
            log::info!("pg_insert_runes: {}", &hex_rune_id);
            let _ = self
              .pg_insert_runes(pg_pool, &hex_rune_id, rune_entry.clone())
              .await;
          });
        }
        self.id_to_entry.insert(id.store(), rune_entry.store())?;

        let inscription_id = InscriptionId { txid, index: 0 };

        if let Some(sequence_number) = self
          .inscription_id_to_sequence_number
          .get(&inscription_id.store())?
        {
          self
            .sequence_number_to_rune_id
            .insert(sequence_number.value(), id.store())?;
        }
      }

      // handle runes related inputs
      for (input_n, input) in tx.input.iter().enumerate() {
        let tx_input = TxInput::from_txin(input, &txid, input_n as i32);
        tx_inputs.push(tx_input.clone());
        if let (Some(pg_pool), Some(runtime)) = (&self.index.pg_pool, &self.index.runtime) {
          runtime.block_on(async {
            if !tx_inputs.is_empty() {
              let mut update_outpoints: Vec<OutpointBalance> = Vec::new();
              for input in &tx_inputs {
                let outpoint = self
                  .pg_select_outpoint_balances(
                    pg_pool,
                    input.prevout_tx_id.as_ref().unwrap(),
                    input.prevout,
                  )
                  .await;

                if let Ok(Some(mut out_item)) = outpoint {
                  out_item.spent = true;
                  update_outpoints.push(out_item.clone());

                  let key = (out_item.rune_id.clone(), out_item.address.clone());
                  // neg rune_amount
                  let rune_amount = -out_item.rune_amount.clone();
                  rune_balance_map.insert(key, rune_amount);
                }
              }

              let _ = self
                .pg_update_outpoint_balances(pg_pool, update_outpoints)
                .await;
            }
          });
        }
      }

      if let (Some(pg_pool), Some(runtime)) = (&self.index.pg_pool, &self.index.runtime) {
        runtime.block_on(async {
          if !tx_outputs.is_empty() {
            let _ = self.pg_insert_tx_outputs(pg_pool, tx_outputs).await;
          }
          if !outpoints.is_empty() {
            let _ = self.pg_insert_outpoint_balances(pg_pool, outpoints).await;
          }
          if !tx_inputs.is_empty() {
            let _ = self.pg_insert_tx_inputs(pg_pool, tx_inputs).await;
          }

          for (key, amount) in rune_balance_map.iter() {
            let rune = self.pg_select_rune_balances(pg_pool, &key.0, &key.1).await;
            if let Ok(Some(db_rune)) = rune {
              update_rune_balances.push(RuneBalance {
                rune_id: db_rune.rune_id.clone(),
                address: db_rune.address.clone(),
                rune_amount: db_rune.rune_amount.clone() + amount,
              });
            } else {
              add_rune_balances.push(RuneBalance {
                rune_id: key.0.clone(),
                address: key.1.clone(),
                rune_amount: amount.clone(),
              })
            };
          }
          if !add_rune_balances.is_empty() {
            let _ = self
              .pg_insert_rune_balances(pg_pool, add_rune_balances)
              .await;
          }
          if !update_rune_balances.is_empty() {
            let _ = self
              .pg_update_rune_balances(pg_pool, update_rune_balances)
              .await;
          }
        });
      }
    }

    let mut burned: HashMap<u128, u128> = HashMap::new();

    if burn {
      for (id, balance) in unallocated {
        *burned.entry(id).or_default() += balance;
      }
    } else {
      // assign all un-allocated runes to the default output, or the first non
      // OP_RETURN output if there is no default, or if the default output is
      // too large
      if let Some(vout) = default_output
        .filter(|vout| *vout < allocated.len())
        .or_else(|| {
          tx.output
            .iter()
            .enumerate()
            .find(|(_vout, tx_out)| !tx_out.script_pubkey.is_op_return())
            .map(|(vout, _tx_out)| vout)
        })
      {
        for (id, balance) in unallocated {
          if balance > 0 {
            *allocated[vout].entry(id).or_default() += balance;
          }
        }
      } else {
        for (id, balance) in unallocated {
          if balance > 0 {
            *burned.entry(id).or_default() += balance;
          }
        }
      }
    }

    // update outpoint balances
    let mut buffer: Vec<u8> = Vec::new();
    for (vout, balances) in allocated.into_iter().enumerate() {
      if balances.is_empty() {
        continue;
      }

      // increment burned balances
      if tx.output[vout].script_pubkey.is_op_return() {
        for (id, balance) in &balances {
          *burned.entry(*id).or_default() += balance;
        }
        continue;
      }

      buffer.clear();

      let mut balances = balances.into_iter().collect::<Vec<(u128, u128)>>();

      // Sort balances by id so tests can assert balances in a fixed order
      balances.sort();

      for (id, balance) in balances {
        varint::encode_to_vec(id, &mut buffer);
        varint::encode_to_vec(balance, &mut buffer);
      }

      self.outpoint_to_balances.insert(
        &OutPoint {
          txid,
          vout: vout.try_into().unwrap(),
        }
        .store(),
        buffer.as_slice(),
      )?;
    }

    // increment entries with burned runes
    for (id, amount) in burned {
      self
        .updates
        .entry(RuneId::try_from(id).unwrap())
        .or_default()
        .burned += amount;
    }

    Ok(())
  }

  // PostgreSQL
  pub(crate) async fn pg_insert_tx_inputs(
    &self,
    pg_pool: &Pool<Postgres>,
    tx_inputs: Vec<TxInput>,
  ) -> Result<()> {
    for tx_input in tx_inputs {
      let result = sqlx::query!(
        r#"
          INSERT INTO public.tx_inputs (
          tx_id, n, prevout_tx_id, prevout, script_sig, sequence, witness
          ) VALUES ($1, $2, $3, $4, $5, $6, $7)
          ON CONFLICT (tx_id, n) DO NOTHING
          "#,
        tx_input.tx_id,
        tx_input.n,
        tx_input.prevout_tx_id,
        tx_input.prevout,
        tx_input.script_sig,
        tx_input.sequence,
        tx_input.witness
      )
      .execute(pg_pool)
      .await;

      match result {
        Ok(_) => {
          log::info!("INSERT INTO public.tx_inputs: {}", tx_input.tx_id);
        }
        Err(error) => {
          log::error!("An error occurred INSERT INTO public.tx_inputs: {}", error);
        }
      }
    }

    Ok(())
  }

  pub(crate) async fn pg_insert_tx_outputs(
    &self,
    pg_pool: &Pool<Postgres>,
    tx_outputs: Vec<TxOutput>,
  ) -> Result<()> {
    for tx_output in tx_outputs {
      let result = sqlx::query!(
        r#"
          INSERT INTO tx_outputs (tx_id, vout, value, script_pubkey, is_op_return, op_return_data)
          VALUES ($1, $2, $3, $4, $5, $6)
          ON CONFLICT (tx_id, vout) DO NOTHING
        "#,
        tx_output.tx_id,
        tx_output.vout,
        tx_output.value,
        tx_output.script_pubkey,
        tx_output.is_op_return,
        tx_output.op_return_data,
      )
      .execute(pg_pool)
      .await;

      match result {
        Ok(_) => {
          log::info!("INSERT INTO public.tx_outputs: {}", tx_output.tx_id);
        }
        Err(error) => {
          log::error!("An error occurred INSERT INTO public.tx_outputs: {}", error);
        }
      }
    }
    Ok(())
  }

  pub(crate) async fn pg_insert_runes(
    &self,
    pg_pool: &Pool<Postgres>,
    hex_rune_id: &str,
    rune_entry: RuneEntry,
  ) -> Result<()> {
    let mut mint_deadline: i32 = 0;
    let mut mint_limit = BigDecimal::from(0);
    let mut mint_term: i32 = 0;
    match rune_entry.mint {
      Some(mint_entry) => {
        if let Some(deadline_value) = mint_entry.deadline {
          mint_deadline = deadline_value as i32;
        } else if let Some(end_value) = mint_entry.end {
          mint_term = end_value as i32;
        } else if let Some(limit_value) = mint_entry.limit {
          mint_limit = BigDecimal::from_i128(limit_value as i128).unwrap_or(BigDecimal::from(0));
        }
      }
      None => {}
    }

    let open_etching: bool = match rune_entry.mint {
      Some(mint_entry) => {
        if mint_entry.deadline.is_some() || mint_entry.end.is_some() {
          true
        } else {
          false
        }
      }
      None => false,
    };

    let rune_timestamp = Utc.timestamp_opt(rune_entry.timestamp as i64, 0).unwrap();

    let result = sqlx::query!(
      r#"
        INSERT INTO public.runes
        (rune_id, rune, symbol, divisibility, spacers, open_etching, mint_deadline, mint_limit, mint_term, rune_timestamp, etching_txid, burned, mints, supply)
        VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13, $14)
        "#,
      hex_rune_id,
      rune_entry.rune.to_string(),
      rune_entry.symbol.map(|c| c as i8),
      rune_entry.divisibility as i16,
      rune_entry.spacers.to_string(),
      open_etching,
      mint_deadline,
      mint_limit,
      mint_term,
      rune_timestamp,
      rune_entry.etching.to_string(),
      BigDecimal::from_i128(rune_entry.burned as i128).unwrap_or(BigDecimal::from(0)),
      BigDecimal::from_i128(rune_entry.mints as i128).unwrap_or(BigDecimal::from(0)),
      BigDecimal::from_i128(rune_entry.supply as i128).unwrap_or(BigDecimal::from(0)),
    )
    .execute(pg_pool)
    .await;

    match result {
      Ok(_) => {
        log::info!(
          "INSERT INTO public.runes: {},{}",
          hex_rune_id,
          rune_entry.etching
        );
      }
      Err(error) => {
        log::error!(
          "An error occurred INSERT INTO public.runes: {},{}",
          hex_rune_id,
          error
        );
      }
    }

    Ok(())
  }

  pub(crate) async fn pg_select_outpoint_balances(
    &self,
    pg_pool: &Pool<Postgres>,
    txid: &str,
    vout: i32,
  ) -> Result<Option<OutpointBalance>> {
    let result = sqlx::query!(
      r#"
        SELECT * FROM public.outpoint_balances
        WHERE tx_id = $1 AND vout = $2
        "#,
      txid,
      vout,
    )
    .fetch_optional(pg_pool)
    .await;

    match result {
      Ok(Some(row)) => {
        log::info!(
          "SELECT public.outpoint_balances with txid and vout: {},{}",
          row.tx_id,
          row.vout,
        );
        Ok(Some(OutpointBalance {
          tx_id: row.tx_id,
          vout: row.vout,
          address: row.address,
          rune_id: row.rune_id,
          rune_amount: row.rune_amount,
          burn: row.burn.unwrap_or(false),
          spent: row.spent.unwrap_or(false),
          value: row.value,
        }))
      }
      Ok(None) => {
        log::info!("No. SELECT public.outpoint_balances: {},{}", txid, vout,);
        Ok(None)
      }
      Err(error) => {
        log::error!(
          "An error occurred SELECT public.outpoint_balances: {}",
          error
        );
        Ok(None)
      }
    }
  }

  pub(crate) async fn pg_select_rune_balances(
    &self,
    pool: &PgPool,
    rune_id: &str,
    address: &str,
  ) -> Result<Option<RuneBalance>> {
    let result = sqlx::query!(
      r#"
        SELECT * FROM public.runes_balances
        WHERE rune_id = $1 AND address = $2
        "#,
      rune_id,
      address,
    )
    .fetch_optional(pool)
    .await;

    match result {
      Ok(Some(row)) => {
        log::info!(
          "Exist. SELECT public.runes_balances: {},{}",
          rune_id,
          address,
        );
        Ok(Some(RuneBalance {
          rune_id: row.rune_id,
          address: row.address,
          rune_amount: row.rune_amount,
        }))
      }
      Ok(None) => {
        log::info!("No. SELECT public.runes_balances: {},{}", rune_id, address,);
        Ok(None)
      }
      Err(error) => {
        log::error!(
          "An error occurred SELECT public.runes_balances: {},{},{}",
          rune_id,
          address,
          error
        );
        Ok(None)
      }
    }
  }

  pub(crate) async fn pg_insert_rune_balances(
    &self,
    pool: &PgPool,
    rune_balances: Vec<RuneBalance>,
  ) -> Result<()> {
    for balance in rune_balances {
      let result = sqlx::query!(
        r#"
          INSERT INTO public.runes_balances (rune_id, address, rune_amount)
          VALUES ($1, $2, $3)
          ON CONFLICT (rune_id, address) DO NOTHING
        "#,
        &balance.rune_id,
        &balance.address,
        balance.rune_amount.clone(),
      )
      .execute(pool)
      .await;

      match result {
        Ok(_) => {
          log::info!(
            "INSERT INTO public.runes_balances: {}",
            balance.address.clone()
          );
        }
        Err(error) => {
          log::error!(
            "An error occurred INSERT INTO public.runes_balances: {},{},{}",
            balance.rune_id.clone(),
            balance.address.clone(),
            error
          );
        }
      }
    }
    Ok(())
  }

  pub(crate) async fn pg_insert_outpoint_balances(
    &self,
    pool: &PgPool,
    outpoint_balances: Vec<OutpointBalance>,
  ) -> Result<()> {
    for outpoint in outpoint_balances {
      let result = sqlx::query!(
        r#"INSERT INTO public.outpoint_balances (tx_id, vout, address, rune_id, rune_amount, burn, spent, value) 
         VALUES ($1, $2, $3, $4, $5, $6, $7, $8)"#,
         outpoint.tx_id,
         outpoint.vout,
         outpoint.address,
         outpoint.rune_id,
         outpoint.rune_amount,
         outpoint.burn,
         outpoint.spent,
         outpoint.value,
    )
    .execute(pool)
    .await;

      match result {
        Ok(_) => {
          log::info!(
            "INSERT INTO public.outpoint_balances: {}",
            outpoint.address.clone()
          );
        }
        Err(error) => {
          log::error!(
            "An error occurred INSERT INTO public.outpoint_balances: {},{}",
            outpoint.address.clone(),
            error
          );
        }
      }
    }
    Ok(())
  }

  pub(crate) async fn pg_update_outpoint_balances(
    &self,
    pool: &PgPool,
    outpoint_balances: Vec<OutpointBalance>,
  ) -> Result<()> {
    for outpoint in outpoint_balances {
      let result = sqlx::query!(
        r#"UPDATE public.outpoint_balances
          SET spent = $1
          WHERE tx_id = $2 AND vout = $3
         "#,
        outpoint.spent,
        outpoint.tx_id,
        outpoint.vout,
      )
      .execute(pool)
      .await;

      match result {
        Ok(_) => {
          log::info!(
            "UPDATE public.outpoint_balances: {},{}",
            outpoint.address.clone(),
            outpoint.spent,
          );
        }
        Err(error) => {
          log::error!(
            "An error occurred UPDATE public.outpoint_balances: {}",
            error
          );
        }
      }
    }
    Ok(())
  }

  pub(crate) async fn pg_update_rune_balances(
    &self,
    pool: &PgPool,
    rune_balances: Vec<RuneBalance>,
  ) -> Result<()> {
    for rune in rune_balances {
      let result = sqlx::query!(
        r#"UPDATE public.runes_balances
          SET rune_amount = $1
          WHERE rune_id = $2 AND address = $3
         "#,
        rune.rune_amount.clone(),
        rune.rune_id.clone(),
        rune.address.clone(),
      )
      .execute(pool)
      .await;

      match result {
        Ok(_) => {
          log::info!(
            "UPDATE public.runes_balances: {},{},{}",
            rune.rune_id.clone(),
            rune.address.clone(),
            rune.rune_amount.clone(),
          );
        }
        Err(error) => {
          log::error!(
            "An error occurred UPDATE public.runes_balances: {},{},{}",
            rune.rune_id.clone(),
            rune.address.clone(),
            error
          );
        }
      }
    }
    Ok(())
  }

  fn get_address_from_script_pubkey(&self, script_pubkey: Vec<u8>) -> String {
    self
      .index
      .options
      .chain()
      .address_from_script(&ScriptBuf::from_bytes(script_pubkey))
      .map(|address| address.to_string())
      .unwrap_or_else(|e| e.to_string())
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn claim_from_id() {
    assert_eq!(claim(1), None);
    assert_eq!(claim(1 | CLAIM_BIT), Some(1));
  }
}
