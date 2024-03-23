use {
  self::runes::transaction::{RsTxIn, RsTxOut},
  super::*,
  crate::runes::{transaction::RsTransaction, varint, Edict, Runestone, CLAIM_BIT},
  sqlx::postgres::PgPool,
};

fn claim(id: u128) -> Option<u128> {
  (id & CLAIM_BIT != 0).then_some(id ^ CLAIM_BIT)
}

struct Allocation {
  balance: u128,
  divisibility: u8,
  end: Option<u64>,
  id: u128,
  limit: Option<u128>,
  rune: Rune,
  symbol: Option<char>,
}

pub(super) struct RuneUpdater<'a, 'db, 'tx, 'pool, 'index> {
  height: u64,
  id_to_entry: &'a mut Table<'db, 'tx, RuneIdValue, RuneEntryValue>,
  inscription_id_to_inscription_entry:
    &'a Table<'db, 'tx, &'static InscriptionIdValue, InscriptionEntryValue>,
  inscription_id_to_rune: &'a mut Table<'db, 'tx, &'static InscriptionIdValue, u128>,
  minimum: Rune,
  outpoint_to_balances: &'a mut Table<'db, 'tx, &'static OutPointValue, &'static [u8]>,
  rune_to_id: &'a mut Table<'db, 'tx, u128, RuneIdValue>,
  runes: u64,
  statistic_to_count: &'a mut Table<'db, 'tx, u64, u64>,
  timestamp: u32,
  transaction_id_to_rune: &'a mut Table<'db, 'tx, &'static TxidValue, u128>,
  runtime: Arc<Runtime>,
  pg_pool: &'pool PgPool,
  index: &'index Index,
  pub rs_tx: RsTransaction,
  /// Stores the balance changes for each rune and address.
  ///
  /// The key of the HashMap is a tuple containing an address and a RuneId.
  /// The value is a vector of tuples, where each tuple represents a balance change.
  /// The first element of the tuple is a boolean that indicates the type of change:
  /// - `true` represents an increase in balance.
  /// - `false` represents a decrease in balance.
  /// The second element of the tuple is the amount of the change.
  pub rune_balances: HashMap<(Address, RuneId), Vec<(bool, u128)>>,
  pub rune_transactions: HashSet<(Txid, RuneId)>,
  pub address_transactions: HashSet<(Txid, Address)>,
}

impl<'a, 'db, 'tx, 'pool, 'index> RuneUpdater<'a, 'db, 'tx, 'pool, 'index> {
  pub(super) fn new(
    height: u64,
    id_to_entry: &'a mut Table<'db, 'tx, RuneIdValue, RuneEntryValue>,
    inscription_id_to_inscription_entry: &'a Table<
      'db,
      'tx,
      &'static InscriptionIdValue,
      InscriptionEntryValue,
    >,
    inscription_id_to_rune: &'a mut Table<'db, 'tx, &'static InscriptionIdValue, u128>,
    outpoint_to_balances: &'a mut Table<'db, 'tx, &'static OutPointValue, &'static [u8]>,
    rune_to_id: &'a mut Table<'db, 'tx, u128, RuneIdValue>,
    statistic_to_count: &'a mut Table<'db, 'tx, u64, u64>,
    timestamp: u32,
    transaction_id_to_rune: &'a mut Table<'db, 'tx, &'static TxidValue, u128>,
    runtime: Arc<Runtime>,
    pg_pool: &'pool PgPool,
    index: &'index Index,
  ) -> Result<Self> {
    let runes = statistic_to_count
      .get(&Statistic::Runes.into())?
      .map(|x| x.value())
      .unwrap_or(0);
    Ok(Self {
      height,
      id_to_entry,
      inscription_id_to_inscription_entry,
      inscription_id_to_rune,
      minimum: Rune::minimum_at_height(Height(height)),
      outpoint_to_balances,
      rune_to_id,
      runes,
      statistic_to_count,
      timestamp,
      transaction_id_to_rune,
      runtime,
      pg_pool,
      index,
      rs_tx: RsTransaction::default(),
      rune_balances: HashMap::new(),
      rune_transactions: HashSet::new(),
      address_transactions: HashSet::new(),
    })
  }

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
          .options
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
              .options
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

    // A mapping of rune ID to un-allocated balance of that rune
    let mut unallocated: HashMap<u128, u128> = HashMap::new();

    // Increment unallocated runes with the runes in this transaction's inputs
    for (vin, input) in tx.input.iter().enumerate() {
      if let Some(guard) = self
        .outpoint_to_balances
        .remove(&input.previous_output.store())?
      {
        let buffer = guard.value();
        let mut i = 0;
        while i < buffer.len() {
          let (id, len) = varint::decode(&buffer[i..])?;
          i += len;
          let (balance, len) = varint::decode(&buffer[i..])?;
          i += len;
          *unallocated.entry(id).or_default() += balance;
          let address = self.rs_tx.inputs[vin].address.clone();

          if let Ok(rune_id) = RuneId::try_from(id) {
            self
              .rune_balances
              .entry((address, rune_id))
              .or_default()
              .push((false, balance));

            self
              .rs_tx
              .inputs
              .get_mut(vin)
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

    let burn = runestone
      .as_ref()
      .map(|runestone| runestone.burn)
      .unwrap_or_default();

    // A vector of allocated transaction output rune balances
    let mut allocated: Vec<HashMap<u128, u128>> = vec![HashMap::new(); tx.output.len()];

    if let Some(runestone) = runestone {
      // Determine if this runestone conains a valid issuance
      let mut allocation = match runestone.etching {
        Some(etching) => {
          // If the issuance symbol is already taken, the issuance is ignored
          if etching.rune < self.minimum || self.rune_to_id.get(etching.rune.0)?.is_some() {
            None
          } else {
            let (limit, term) = match (etching.limit, etching.term) {
              (None, Some(term)) => (Some(runes::MAX_LIMIT), Some(term)),
              (limit, term) => (limit, term),
            };

            // Construct an allocation, representing the new runes that may be
            // allocated. Beware: Because it would require constructing a block
            // with 2**16 + 1 transactions, there is no test that checks that
            // an eching in a transaction with an out-of-bounds index is
            // ignored.
            match u16::try_from(index) {
              Ok(index) => Some(Allocation {
                balance: if let Some(limit) = limit {
                  if term == Some(0) {
                    0
                  } else {
                    limit
                  }
                } else {
                  u128::max_value()
                },
                limit,
                divisibility: etching.divisibility,
                id: u128::from(self.height) << 16 | u128::from(index),
                rune: etching.rune,
                symbol: etching.symbol,
                end: term.map(|term| term + self.height),
              }),
              Err(_) => None,
            }
          }
        }
        None => None,
      };

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
              if let Some(limit) = entry.limit {
                if let Some(end) = entry.end {
                  if self.height >= end {
                    continue;
                  }
                }
                mintable.insert(id, limit);
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

              for output in destinations {
                allocate(balance, amount, output);
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

        // increment entries with minted runes
        for (id, amount) in mintable {
          let minted = limits[&id] - amount;
          if minted > 0 {
            let id = RuneId::try_from(id).unwrap().store();
            let mut entry = RuneEntry::load(self.id_to_entry.get(id)?.unwrap().value());
            entry.supply += minted;
            self.id_to_entry.insert(id, entry.store())?;

            self.runtime.block_on(async {
              let _ = RuneUpdater::pg_update_rune(
                self.pg_pool,
                RuneId {
                  height: id.0,
                  index: id.1,
                },
                entry,
              )
              .await;
            });
          }
        }
      }

      if let Some(Allocation {
        balance,
        divisibility,
        id,
        rune,
        symbol,
        limit,
        end,
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
        let rune_entry = RuneEntry {
          burned: 0,
          divisibility,
          etching: txid,
          number,
          rune,
          supply: if let Some(limit) = limit {
            if end == Some(self.height) {
              0
            } else {
              limit
            }
          } else {
            u128::max_value()
          } - balance,
          end,
          symbol,
          limit,
          timestamp: self.timestamp,
        };
        self.id_to_entry.insert(id.store(), rune_entry.store())?;

        self.runtime.block_on(async {
          let _ = self.pg_insert_rune(id, rune_entry).await;
        });
        self.rune_transactions.insert((txid, id));

        let inscription_id = InscriptionId { txid, index: 0 };

        if self
          .inscription_id_to_inscription_entry
          .get(&inscription_id.store())?
          .is_some()
        {
          self
            .inscription_id_to_rune
            .insert(&inscription_id.store(), rune.0)?;
        }
      }
    }

    let mut burned: HashMap<u128, u128> = HashMap::new();

    if burn {
      for (id, balance) in unallocated {
        *burned.entry(id).or_default() += balance;
      }
    } else {
      // Assign all un-allocated runes to the first non OP_RETURN output
      if let Some((vout, _)) = tx
        .output
        .iter()
        .enumerate()
        .find(|(_, tx_out)| !tx_out.script_pubkey.is_op_return())
      {
        for (id, balance) in unallocated {
          if balance > 0 {
            *allocated[vout].entry(id).or_default() += balance;
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

      if self.rs_tx.outputs[vout].address.is_none() {
        log::warn!("address is none. txid: {:?}, rs_tx: {:?}", txid, self.rs_tx);
        continue;
      }
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
      let id = RuneId::try_from(id).unwrap().store();
      let mut entry = RuneEntry::load(self.id_to_entry.get(id)?.unwrap().value());
      entry.burned += amount;
      self.id_to_entry.insert(id, entry.store())?;

      self.runtime.block_on(async {
        let _ = RuneUpdater::pg_update_rune(
          self.pg_pool,
          RuneId {
            height: id.0,
            index: id.1,
          },
          entry,
        )
        .await;
      });
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

      for output in &self.rs_tx.outputs {
        if let Some(ref address) = output.address {
          self.address_transactions.insert((txid, address.clone()));
        }
      }
      for input in &self.rs_tx.inputs {
        self
          .address_transactions
          .insert((txid, input.address.clone()));
      }
    }

    Ok(())
  }

  pub(crate) async fn pg_insert_rs_transaction(
    &self,
    txid: Txid,
    rs_tx: RsTransaction,
  ) -> Result<()> {
    let result = sqlx::query!(
      r#"
          INSERT INTO public.rs_transactions_legacy (txid, transaction)
          VALUES ($1, $2)
          ON CONFLICT (txid) DO NOTHING
        "#,
      txid.to_string(),
      serde_json::to_value(rs_tx.clone())?,
    )
    .execute(self.pg_pool)
    .await;

    match result {
      Ok(_) => {
        log::debug!("INSERT INTO rs_transactions: {}", txid);
      }
      Err(error) => {
        log::error!(
          "An error occurred INSERT INTO rs_transactions: {}: rs_tx: {:?}",
          error,
          rs_tx
        );
      }
    }

    Ok(())
  }

  pub(crate) async fn pg_insert_rune(&self, rune_id: RuneId, rune_entry: RuneEntry) -> Result<()> {
    let result = sqlx::query!(
      r#"
        INSERT INTO public.runes_legacy
        (rune_id, spaced_rune, number, divisibility, symbol, etching, mint_deadline, mint_end, mint_limit, mints, burned, premine, supply, timestamp)
        VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13, $14)
        "#,
      rune_id.to_string(),
      rune_entry.rune.to_string(),
      rune_entry.number.to_string(),
      rune_entry.divisibility as i16,
      rune_entry.symbol.map(|s|s.to_string()),
      rune_entry.etching.to_string(),
      0,
      rune_entry.end.map(|e| e as i64),
      rune_entry.limit.map(|l| l.to_string()),
      "0",
      rune_entry.burned.to_string(),
      "0",
      rune_entry.supply.to_string(),
      Utc.timestamp_opt(rune_entry.timestamp as i64, 0).unwrap(),
    )
    .execute(self.pg_pool)
    .await;

    match result {
      Ok(_) => {
        log::debug!(
          "INSERT INTO public.runes_legacy: {},{}",
          rune_id,
          rune_entry.etching
        );
      }
      Err(error) => {
        log::error!(
          "An error occurred INSERT INTO public.runes_legacy: {},{}",
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
      SELECT rune_id, spaced_rune, number, divisibility, symbol, etching, mint_deadline, mint_end, mint_limit, mints, burned, premine, supply, timestamp
      FROM public.runes_legacy
      WHERE rune_id = $1
      "#,
      rune_id.to_string()
    )
    .fetch_one(pg_pool)
    .await;

    match result {
      Ok(row) => {
        log::debug!("UPDATE public.runes_legacy: {}", rune_id);
        let rune_entry = RuneEntry {
          rune: Rune::from_str(&row.spaced_rune).unwrap(),
          number: u64::from_str(&row.number).unwrap(),
          divisibility: row.divisibility as u8,
          symbol: row.symbol.map(|s| s.parse::<char>().unwrap()),
          etching: Txid::from_str(&row.etching).unwrap(),
          end: row.mint_end.map(|e| e as u64),
          limit: row.mint_limit.map(|l| l.parse().unwrap()),
          burned: row.burned.parse().unwrap(),
          supply: row.supply.parse().unwrap(),
          timestamp: row.timestamp.timestamp() as u32,
        };
        return Ok(rune_entry);
      }
      Err(error) => {
        log::error!(
          "An error occurred UPDATE public.runes_legacy: {},{}",
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
      UPDATE public.runes_legacy
      SET mints = $2, burned = $3, supply = $4
      WHERE rune_id = $1
      "#,
      rune_id.to_string(),
      // rune_entry.mints.to_string(),
      "0",
      rune_entry.burned.to_string(),
      rune_entry.supply.to_string(),
    )
    .execute(pg_pool)
    .await;

    match result {
      Ok(_) => {
        log::debug!("UPDATE public.runes_legacy: {}", rune_id);
      }
      Err(error) => {
        log::error!(
          "An error occurred UPDATE public.runes_legacy: {},{}",
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
      FROM public.rune_balances_legacy
      WHERE rune_id = $1 AND address = $2
      "#,
      rune_id.to_string(),
      address.to_string(),
    )
    .fetch_optional(pg_pool)
    .await;
    match result {
      Ok(row) => {
        log::debug!(
          "QUERY public.rune_balances_legacy: {}, {}",
          rune_id,
          address
        );
        return Ok(row.map(|r| r.amount.parse().unwrap()));
      }
      Err(error) => {
        log::error!(
          "An error occurred QUERY public.rune_balances_legacy: {},{},{}",
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
      INSERT INTO public.rune_balances_legacy (rune_id, address, amount)
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
        log::debug!(
          "UPDATE public.rune_balances_legacy: {},{}",
          rune_id,
          address
        );
        Ok(())
      }
      Err(error) => {
        log::error!(
          "An error occurred UPDATE public.rune_balances_legacy: {},{},{}",
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
    height: u64,
    timestamp: u32,
  ) -> Result<()> {
    let result = sqlx::query!(
      r#"
          INSERT INTO public.rune_transactions_legacy (rune_id, txid, height, timestamp)
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

  pub(crate) async fn pg_insert_address_transaction(
    pg_pool: &PgPool,
    address: Address,
    txid: Txid,
  ) -> Result<()> {
    let result = sqlx::query!(
      r#"
          INSERT INTO public.address_transactions_legacy (address, txid)
          VALUES ($1, $2)
          ON CONFLICT (address, txid) DO NOTHING
        "#,
      address.to_string(),
      txid.to_string(),
    )
    .execute(pg_pool)
    .await;

    match result {
      Ok(_) => {
        log::debug!(
          "INSERT INTO address_transactions_legacy: {},{}",
          txid,
          address
        );
      }
      Err(error) => {
        log::error!(
          "An error occurred INSERT INTO address_transactions_legacy: {},{},{}",
          txid,
          address,
          error
        );
      }
    }

    Ok(())
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
