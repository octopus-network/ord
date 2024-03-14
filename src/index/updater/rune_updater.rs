use {
  self::runes::transaction::{RsTxIn, RsTxOut},
  super::*,
  crate::runes::{transaction::RsTransaction, varint, Edict, Runestone},
  sqlx::postgres::PgPool,
};

struct Claim {
  id: u128,
  limit: u128,
}

struct Etched {
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

pub(super) struct RuneUpdater<'a, 'db, 'tx, 'pool, 'index> {
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
  pub(super) runtime: Arc<Runtime>,
  pub(super) pg_pool: &'pool PgPool,
  pub(super) index: &'index Index,
  pub(super) rs_tx: RsTransaction,
  /// Stores the balance changes for each rune and address.
  ///
  /// The key of the HashMap is a tuple containing an address and a RuneId.
  /// The value is a vector of tuples, where each tuple represents a balance change.
  /// The first element of the tuple is a boolean that indicates the type of change:
  /// - `true` represents an increase in balance.
  /// - `false` represents a decrease in balance.
  /// The second element of the tuple is the amount of the change.
  pub(super) rune_balances: HashMap<(Address, RuneId), Vec<(bool, u128)>>,
  pub(super) rune_transactions: HashSet<(Txid, RuneId)>,
}

impl<'a, 'db, 'tx, 'pool, 'index> RuneUpdater<'a, 'db, 'tx, 'pool, 'index> {
  pub(super) fn index_runes(&mut self, index: usize, tx: &Transaction, txid: Txid) -> Result<()> {
    self.rs_tx = RsTransaction::default();

    let runestone = Runestone::from_transaction(tx);
    let has_runes = tx.input.iter().any(|input| {
      self
        .outpoint_to_balances
        .get(&input.previous_output.store())
        .map_or(false, |v| v.is_some())
    });

    if runestone.is_some() || has_runes {
      for input in tx.input.iter() {
        if input.previous_output.txid
          == Txid::from_str("0000000000000000000000000000000000000000000000000000000000000000")
            .unwrap()
        {
          continue;
        }
        let prev_output = self
          .index
          .get_transaction(input.previous_output.txid)?
          .unwrap()
          .output
          .into_iter()
          .nth(input.previous_output.vout as usize)
          .unwrap();

        if let Ok(address) = self
          .index
          .settings
          .chain()
          .address_from_script(&prev_output.script_pubkey)
        {
          let tx_in = RsTxIn {
            value: Amount::from_sat(prev_output.value),
            address,
            runes: vec![],
          };
          self.rs_tx.inputs.push(tx_in);
        } else {
          log::error!(
            "Failed to convert script_pubkey to address: {:?}",
            prev_output.script_pubkey
          );
          continue;
        }
      }
      for output in tx.output.iter() {
        let tx_out = RsTxOut {
          value: Amount::from_sat(output.value),
          address: if output.script_pubkey.is_op_return() {
            None
          } else {
            self
              .index
              .settings
              .chain()
              .address_from_script(&output.script_pubkey)
              .ok()
          },
          op_return: if output.script_pubkey.is_op_return() {
            runestone.clone()
          } else {
            None
          },
          runes: vec![],
        };
        self.rs_tx.outputs.push(tx_out);
      }
    }

    let mut unallocated = self.unallocated(tx)?;

    let burn = runestone
      .as_ref()
      .map(|runestone| runestone.burn)
      .unwrap_or_default();

    let default_output = runestone.as_ref().and_then(|runestone| {
      runestone
        .default_output
        .and_then(|default| usize::try_from(default).ok())
    });

    let mut allocated: Vec<HashMap<u128, u128>> = vec![HashMap::new(); tx.output.len()];

    if let Some(runestone) = runestone {
      if let Some(claim) = runestone
        .claim
        .and_then(|id| self.claim(id).transpose())
        .transpose()?
      {
        *unallocated.entry(claim.id).or_default() += claim.limit;

        let update = self
          .updates
          .entry(RuneId::try_from(claim.id).unwrap())
          .or_default();

        update.mints += 1;
        update.supply += claim.limit;
      }

      let mut etched = self.etched(index, &runestone)?;

      if !burn {
        for Edict { id, amount, output } in runestone.edicts.clone() {
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
            match etched.as_mut() {
              Some(Etched { balance, id, .. }) => (balance, *id),
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
        }
      }

      if let Some(etched) = etched {
        self.create_rune_entry(txid, burn, etched)?;
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

          if let Ok(rune_id) = RuneId::try_from(*id) {
            self
              .rs_tx
              .outputs
              .get_mut(vout)
              .expect("op_return must exist; QED")
              .runes
              .push((rune_id, *balance));
            self.rune_transactions.insert((txid, rune_id));
          } else {
            log::warn!("Failed to convert id to RuneId: {}", id);
            continue;
          }
        }
        continue;
      }

      buffer.clear();

      let mut balances = balances.into_iter().collect::<Vec<(u128, u128)>>();

      // Sort balances by id so tests can assert balances in a fixed order
      balances.sort();

      let address = self.rs_tx.outputs[vout].address.clone().unwrap();
      for (id, balance) in balances {
        varint::encode_to_vec(id, &mut buffer);
        varint::encode_to_vec(balance, &mut buffer);
        if let Ok(rune_id) = RuneId::try_from(id) {
          self
            .rune_balances
            .entry((address.clone(), rune_id))
            .or_default()
            .push((true, balance));

          self
            .rs_tx
            .outputs
            .get_mut(vout)
            .expect("output must exist; QED")
            .runes
            .push((rune_id, balance));
          self.rune_transactions.insert((txid, rune_id));
        } else {
          log::warn!("Failed to convert id to RuneId: {}", id);
          continue;
        }
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
    if !self.rs_tx.outputs.is_empty() || !self.rs_tx.inputs.is_empty() {
      self.runtime.block_on(async {
        if let Err(error) = self
          .pg_insert_rs_transaction(txid, self.rs_tx.clone())
          .await
        {
          log::error!(
            "An error occurred INSERT INTO rs_transactions: {} {:?}",
            error,
            self.rs_tx
          );
        }
      });
    }

    let mut rs_txid_address_set: HashSet<(Txid, Address)> = HashSet::new();
    for output in &self.rs_tx.outputs {
      if let Some(ref address) = output.address {
        rs_txid_address_set.insert((txid, address.clone()));
      }
    }
    for input in &self.rs_tx.inputs {
      rs_txid_address_set.insert((txid, input.address.clone()));
    }
    for (txid, address) in rs_txid_address_set {
      self.runtime.block_on(async {
        if let Err(error) = self.pg_insert_rs_address_transaction(txid, address).await {
          log::error!(
            "An error occurred INSERT INTO rs_address_transactions: {}, {}",
            error,
            txid
          );
        }
      });
    }

    Ok(())
  }

  fn create_rune_entry(&mut self, txid: Txid, burn: bool, etched: Etched) -> Result {
    let Etched {
      balance,
      divisibility,
      id,
      mint,
      rune,
      spacers,
      symbol,
    } = etched;

    let id = RuneId::try_from(id).unwrap();
    self.rune_to_id.insert(rune.0, id.store())?;
    self.transaction_id_to_rune.insert(&txid.store(), rune.0)?;
    let number = self.runes;
    self.runes += 1;
    self
      .statistic_to_count
      .insert(&Statistic::Runes.into(), self.runes)?;

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
        u128::MAX
      } - balance,
      symbol,
      timestamp: self.timestamp,
    };
    self.id_to_entry.insert(id.store(), rune_entry.store())?;

    self.runtime.block_on(async {
      let _ = self.pg_insert_rune(id, rune_entry).await;
    });
    self.rune_transactions.insert((txid, id));

    let inscription_id = InscriptionId { txid, index: 0 };

    if let Some(sequence_number) = self
      .inscription_id_to_sequence_number
      .get(&inscription_id.store())?
    {
      self
        .sequence_number_to_rune_id
        .insert(sequence_number.value(), id.store())?;
    }

    Ok(())
  }

  fn etched(&mut self, index: usize, runestone: &Runestone) -> Result<Option<Etched>> {
    let Some(etching) = runestone.etching else {
      return Ok(None);
    };

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
      return Ok(None);
    }

    let rune = if let Some(rune) = etching.rune {
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

    // Nota bene: Because it would require constructing a block
    // with 2**16 + 1 transactions, there is no test that checks that
    // an eching in a transaction with an out-of-bounds index is
    // ignored.
    let Ok(index) = u16::try_from(index) else {
      return Ok(None);
    };

    Ok(Some(Etched {
      balance: if let Some(mint) = etching.mint {
        if mint.term == Some(0) {
          0
        } else {
          mint.limit.unwrap_or(runes::MAX_LIMIT)
        }
      } else {
        u128::MAX
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
    }))
  }

  fn claim(&self, id: u128) -> Result<Option<Claim>> {
    let Ok(key) = RuneId::try_from(id) else {
      return Ok(None);
    };

    let Some(entry) = self.id_to_entry.get(&key.store())? else {
      return Ok(None);
    };

    let entry = RuneEntry::load(entry.value());

    let Some(mint) = entry.mint else {
      return Ok(None);
    };

    if let Some(end) = mint.end {
      if self.height >= end {
        return Ok(None);
      }
    }

    if let Some(deadline) = mint.deadline {
      if self.timestamp >= deadline {
        return Ok(None);
      }
    }

    Ok(Some(Claim {
      id,
      limit: mint.limit.unwrap_or(runes::MAX_LIMIT),
    }))
  }

  fn unallocated(&mut self, tx: &Transaction) -> Result<HashMap<u128, u128>> {
    // map of rune ID to un-allocated balance of that rune
    let mut unallocated: HashMap<u128, u128> = HashMap::new();

    // increment unallocated runes with the runes in tx inputs
    for (index, input) in tx.input.iter().enumerate() {
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

          let address = self.rs_tx.inputs[index].address.clone();

          if let Ok(rune_id) = RuneId::try_from(id) {
            self
              .rune_balances
              .entry((address, rune_id))
              .or_default()
              .push((false, balance));

            self
              .rs_tx
              .inputs
              .get_mut(index)
              .expect("input must exist; QED")
              .runes
              .push((rune_id, balance));
          } else {
            log::warn!("Failed to convert id to RuneId: {}", id);
            continue;
          }
        }
      }
    }

    Ok(unallocated)
  }

  pub(crate) async fn pg_insert_rs_transaction(
    &self,
    txid: Txid,
    rs_tx: RsTransaction,
  ) -> Result<()> {
    let result = sqlx::query!(
      r#"
          INSERT INTO public.rs_transactions (txid, transaction)
          VALUES ($1, $2)
          ON CONFLICT (txid) DO NOTHING
        "#,
      txid.to_string(),
      serde_json::to_value(rs_tx)?,
    )
    .execute(self.pg_pool)
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
  }

  pub(crate) async fn pg_insert_rs_address_transaction(
    &self,
    txid: Txid,
    address: Address,
  ) -> Result<()> {
    let result = sqlx::query!(
      r#"
          INSERT INTO public.rs_address_transactions (txid, address)
          VALUES ($1, $2)
        "#,
      txid.to_string(),
      address.to_string(),
    )
    .execute(self.pg_pool)
    .await;

    match result {
      Ok(_) => {
        log::debug!("INSERT INTO rs_address_transactions: {},{}", txid, address);
      }
      Err(error) => {
        log::error!(
          "An error occurred INSERT INTO rs_address_transactions: {},{},{}",
          txid,
          address,
          error
        );
      }
    }

    Ok(())
  }

  pub(crate) async fn pg_insert_rune(&self, rune_id: RuneId, rune_entry: RuneEntry) -> Result<()> {
    let result = sqlx::query!(
      r#"
        INSERT INTO public.runes
        (rune_id, spaced_rune, number, divisibility, symbol, etching, mint_deadline, mint_end, mint_limit, mints, burned, supply, timestamp)
        VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13)
        "#,
      rune_id.to_string(),
      SpacedRune{rune: rune_entry.rune, spacers: rune_entry.spacers}.to_string(),
      rune_entry.number.to_string(),
      rune_entry.divisibility as i16,
      rune_entry.symbol.map(|s|s.to_string()),
      rune_entry.etching.to_string(),
      rune_entry.mint.and_then(|m|m.deadline).map(|d| d as i64),
      rune_entry.mint.and_then(|m|m.end).map(|e| e as i64),
      rune_entry.mint.and_then(|m|m.limit).map(|l| l.to_string()),
      rune_entry.mints.to_string(),
      rune_entry.burned.to_string(),
      rune_entry.supply.to_string(),
      Utc.timestamp_opt(rune_entry.timestamp as i64, 0).unwrap(),
    )
    .execute(self.pg_pool)
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
  }

  pub(crate) async fn pg_query_rune(
    pg_pool: &PgPool,
    rune_id: RuneId,
  ) -> Result<RuneEntry, sqlx::Error> {
    let result = sqlx::query!(
      r#"
      SELECT rune_id, spaced_rune, number, divisibility, symbol, etching, mint_deadline, mint_end, mint_limit, mints, burned, supply, timestamp
      FROM public.runes
      WHERE rune_id = $1
      "#,
      rune_id.to_string()
    )
    .fetch_one(pg_pool)
    .await;

    match result {
      Ok(row) => {
        log::debug!("UPDATE public.runes: {}", rune_id);
        let spaced_rune = SpacedRune::from_str(&row.spaced_rune).unwrap();
        let rune_entry = RuneEntry {
          rune: spaced_rune.rune,
          spacers: spaced_rune.spacers,
          number: u64::from_str(&row.number).unwrap(),
          divisibility: row.divisibility as u8,
          symbol: row.symbol.map(|s| s.parse::<char>().unwrap()),
          etching: Txid::from_str(&row.etching).unwrap(),
          mint: Some(MintEntry {
            deadline: row.mint_deadline.map(|d| d as u32),
            end: row.mint_end.map(|e| e as u32),
            limit: row.mint_limit.map(|l| l.parse().unwrap()),
          }),
          mints: row.mints.parse().unwrap(),
          burned: row.burned.parse().unwrap(),
          supply: row.supply.parse().unwrap(),
          timestamp: row.timestamp.timestamp() as u32,
        };
        return Ok(rune_entry);
      }
      Err(error) => {
        log::error!(
          "An error occurred UPDATE public.runes: {},{}",
          rune_id,
          error
        );
        return Err(error);
      }
    }
  }

  pub(crate) async fn pg_update_rune(
    pg_pool: &PgPool,
    rune_id: RuneId,
    rune_entry: RuneEntry,
  ) -> Result<(), sqlx::Error> {
    let result = sqlx::query!(
      r#"
      UPDATE public.runes
      SET mints = $2, burned = $3, supply = $4
      WHERE rune_id = $1
      "#,
      rune_id.to_string(),
      rune_entry.mints.to_string(),
      rune_entry.burned.to_string(),
      rune_entry.supply.to_string(),
    )
    .execute(pg_pool)
    .await;

    match result {
      Ok(_) => {
        log::debug!("UPDATE public.runes: {}", rune_id);
      }
      Err(error) => {
        log::error!(
          "An error occurred UPDATE public.runes: {},{}",
          rune_id,
          error
        );
      }
    }

    Ok(())
  }

  pub(crate) async fn pg_query_rune_balance(
    pg_pool: &PgPool,
    rune_id: RuneId,
    address: Address,
  ) -> Result<Option<u128>, sqlx::Error> {
    let result = sqlx::query!(
      r#"
      SELECT rune_id, address, amount
      FROM public.rune_balances
      WHERE rune_id = $1 AND address = $2
      "#,
      rune_id.to_string(),
      address.to_string(),
    )
    .fetch_optional(pg_pool)
    .await;
    match result {
      Ok(row) => {
        log::debug!("QUERY public.rune_balances: {}, {}", rune_id, address);
        return Ok(row.map(|r| r.amount.parse().unwrap()));
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
  }

  pub(crate) async fn pg_update_rune_balance(
    pg_pool: &PgPool,
    rune_id: RuneId,
    address: Address,
    amount: u128,
  ) -> Result<(), sqlx::Error> {
    let result = sqlx::query!(
      r#"
      INSERT INTO public.rune_balances (rune_id, address, amount)
      VALUES ($1, $2, $3)
      ON CONFLICT(rune_id, address)
      DO UPDATE SET
        amount = EXCLUDED.amount;
      "#,
      rune_id.to_string(),
      address.to_string(),
      amount.to_string(),
    )
    .execute(pg_pool)
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
  }

  pub(crate) async fn pg_insert_rune_transaction(
    pg_pool: &PgPool,
    rune_id: RuneId,
    txid: Txid,
    height: u32,
    timestamp: u32,
  ) -> Result<()> {
    let result = sqlx::query!(
      r#"
          INSERT INTO public.rune_transactions (rune_id, txid, height, timestamp)
          VALUES ($1, $2, $3, $4)
          ON CONFLICT (rune_id, txid) DO NOTHING
        "#,
      rune_id.to_string(),
      txid.to_string(),
      height as i64,
      Utc.timestamp_opt(timestamp as i64, 0).unwrap()
    )
    .execute(pg_pool)
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
  }
}
