use super::*;
use ordinals::{RsTransaction, RsTxIn, RsTxOut};

pub(super) struct RuneUpdater<'a, 'tx, 'client, 'index> {
  pub(super) block_time: u32,
  pub(super) burned: HashMap<RuneId, Lot>,
  pub(super) client: &'client Client,
  pub(super) height: u32,
  pub(super) id_to_entry: &'a mut Table<'tx, RuneIdValue, RuneEntryValue>,
  pub(super) inscription_id_to_sequence_number: &'a Table<'tx, InscriptionIdValue, u32>,
  pub(super) minimum: Rune,
  pub(super) outpoint_to_balances: &'a mut Table<'tx, &'static OutPointValue, &'static [u8]>,
  pub(super) rune_to_id: &'a mut Table<'tx, u128, RuneIdValue>,
  pub(super) runes: u64,
  pub(super) sequence_number_to_rune_id: &'a mut Table<'tx, u32, RuneIdValue>,
  pub(super) statistic_to_count: &'a mut Table<'tx, u64, u64>,
  pub(super) transaction_id_to_rune: &'a mut Table<'tx, &'static TxidValue, u128>,
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
  pub(super) address_transactions: HashSet<(Txid, Address)>,
}

impl<'a, 'tx, 'client, 'index> RuneUpdater<'a, 'tx, 'client, 'index> {
  pub(super) fn index_runes(&mut self, tx_index: u32, tx: &Transaction, txid: Txid) -> Result<()> {
    let artifact = Runestone::decipher(tx);

    let has_runes = tx.input.iter().any(|input| {
      self
        .outpoint_to_balances
        .get(&input.previous_output.store())
        .map_or(false, |v| v.is_some())
    });

    self.rs_tx = RsTransaction::default();
    if artifact.is_some() || has_runes {
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
            artifact.clone()
          } else {
            None
          },
          runes: vec![],
        };
        self.rs_tx.outputs.push(tx_out);
      }
    }

    let mut unallocated = self.unallocated(tx)?;

    let mut allocated: Vec<HashMap<RuneId, Lot>> = vec![HashMap::new(); tx.output.len()];

    if let Some(artifact) = &artifact {
      if let Some(id) = artifact.mint() {
        if let Some(amount) = self.mint(id)? {
          *unallocated.entry(id).or_default() += amount;
        }
      }

      let etched = self.etched(tx_index, tx, artifact)?;

      if let Artifact::Runestone(runestone) = artifact {
        if let Some((id, ..)) = etched {
          *unallocated.entry(id).or_default() +=
            runestone.etching.unwrap().premine.unwrap_or_default();
        }

        for Edict { id, amount, output } in runestone.edicts.iter().copied() {
          let amount = Lot(amount);

          // edicts with output values greater than the number of outputs
          // should never be produced by the edict parser
          let output = usize::try_from(output).unwrap();
          assert!(output <= tx.output.len());

          let id = if id == RuneId::default() {
            let Some((id, ..)) = etched else {
              continue;
            };

            id
          } else {
            id
          };

          let Some(balance) = unallocated.get_mut(&id) else {
            continue;
          };

          let mut allocate = |balance: &mut Lot, amount: Lot, output: usize| {
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

      if let Some((id, rune)) = etched {
        self.create_rune_entry(txid, artifact, id, rune)?;
      }
    }

    let mut burned: HashMap<RuneId, Lot> = HashMap::new();

    if let Some(Artifact::Cenotaph(_)) = artifact {
      for (id, balance) in unallocated {
        *burned.entry(id).or_default() += balance;
      }
    } else {
      let pointer = artifact
        .map(|artifact| match artifact {
          Artifact::Runestone(runestone) => runestone.pointer,
          Artifact::Cenotaph(_) => unreachable!(),
        })
        .unwrap_or_default();

      // assign all un-allocated runes to the default output, or the first non
      // OP_RETURN output if there is no default, or if the default output is
      // too large
      if let Some(vout) = pointer
        .map(|pointer| pointer.into_usize())
        .inspect(|&pointer| assert!(pointer < allocated.len()))
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
          *burned.entry(*id).or_default() += *balance;

          if let Ok(rune_id) = RuneId::try_from(*id) {
            self
              .rs_tx
              .outputs
              .get_mut(vout)
              .expect("op_return must exist; QED")
              .runes
              .push((rune_id, balance.n()));
            self.rune_transactions.insert((txid, rune_id));
          } else {
            log::warn!("Failed to convert id to RuneId: {}", id);
            continue;
          }
        }
        continue;
      }

      buffer.clear();

      let mut balances = balances.into_iter().collect::<Vec<(RuneId, Lot)>>();

      // Sort balances by id so tests can assert balances in a fixed order
      balances.sort();

      if self.rs_tx.outputs[vout].address.is_none() {
        log::warn!("address is none: txid: {:?}, vout: {:?}", txid, vout);
        continue;
      }
      let address = self.rs_tx.outputs[vout].address.clone().unwrap();
      for (id, balance) in balances {
        Index::encode_rune_balance(id, balance.n(), &mut buffer);
        if let Ok(rune_id) = RuneId::try_from(id) {
          self
            .rune_balances
            .entry((address.clone(), rune_id))
            .or_default()
            .push((true, balance.n()));

          self
            .rs_tx
            .outputs
            .get_mut(vout)
            .expect("output must exist; QED")
            .runes
            .push((rune_id, balance.n()));
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
      *self.burned.entry(id).or_default() += amount;
    }

    if !self.rs_tx.outputs.is_empty() || !self.rs_tx.inputs.is_empty() {
      if let Err(error) = self
        .index
        .pg_database
        .pg_insert_rs_transaction(txid, &self.rs_tx)
      {
        log::error!(
          "An error occurred INSERT INTO rs_transactions: {} {:?}",
          error,
          self.rs_tx
        );
      }
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

  pub(super) fn update(self) -> Result {
    for (rune_id, burned) in &self.burned {
      let mut entry = RuneEntry::load(self.id_to_entry.get(&rune_id.store())?.unwrap().value());
      entry.burned = entry.burned.checked_add(burned.n()).unwrap();
      self.id_to_entry.insert(&rune_id.store(), entry.store())?;
      let _ = self
        .index
        .pg_database
        .pg_update_rune_burned(*rune_id, entry.burned);
    }

    Ok(())
  }

  fn create_rune_entry(
    &mut self,
    txid: Txid,
    artifact: &Artifact,
    id: RuneId,
    rune: Rune,
  ) -> Result {
    self.rune_to_id.insert(rune.store(), id.store())?;
    self
      .transaction_id_to_rune
      .insert(&txid.store(), rune.store())?;

    let number = self.runes;
    self.runes += 1;

    self
      .statistic_to_count
      .insert(&Statistic::Runes.into(), self.runes)?;

    let entry = match artifact {
      Artifact::Cenotaph(_) => RuneEntry {
        block: id.block,
        burned: 0,
        divisibility: 0,
        etching: txid,
        terms: None,
        mints: 0,
        number,
        premine: 0,
        spaced_rune: SpacedRune { rune, spacers: 0 },
        symbol: None,
        timestamp: self.block_time.into(),
        turbo: false,
      },
      Artifact::Runestone(Runestone { etching, .. }) => {
        let Etching {
          divisibility,
          terms,
          premine,
          spacers,
          symbol,
          turbo,
          ..
        } = etching.unwrap();

        RuneEntry {
          block: id.block,
          burned: 0,
          divisibility: divisibility.unwrap_or_default(),
          etching: txid,
          terms,
          mints: 0,
          number,
          premine: premine.unwrap_or_default(),
          spaced_rune: SpacedRune {
            rune,
            spacers: spacers.unwrap_or_default(),
          },
          symbol,
          timestamp: self.block_time.into(),
          turbo,
        }
      }
    };

    self.id_to_entry.insert(id.store(), entry.store())?;
    let _ = self.index.pg_database.pg_insert_rune(id, entry);

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

  fn etched(
    &mut self,
    tx_index: u32,
    tx: &Transaction,
    artifact: &Artifact,
  ) -> Result<Option<(RuneId, Rune)>> {
    let rune = match artifact {
      Artifact::Runestone(runestone) => match runestone.etching {
        Some(etching) => etching.rune,
        None => return Ok(None),
      },
      Artifact::Cenotaph(cenotaph) => match cenotaph.etching {
        Some(rune) => Some(rune),
        None => return Ok(None),
      },
    };

    let rune = if let Some(rune) = rune {
      if rune < self.minimum
        || rune.is_reserved()
        || self.rune_to_id.get(rune.0)?.is_some()
        || !self.tx_commits_to_rune(tx, rune)?
      {
        return Ok(None);
      }
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

      Rune::reserved(self.height.into(), tx_index)
    };

    Ok(Some((
      RuneId {
        block: self.height.into(),
        tx: tx_index,
      },
      rune,
    )))
  }

  fn mint(&mut self, id: RuneId) -> Result<Option<Lot>> {
    let Some(entry) = self.id_to_entry.get(&id.store())? else {
      return Ok(None);
    };

    let mut rune_entry = RuneEntry::load(entry.value());

    let Ok(amount) = rune_entry.mintable(self.height.into()) else {
      return Ok(None);
    };

    drop(entry);

    rune_entry.mints += 1;

    self.id_to_entry.insert(&id.store(), rune_entry.store())?;
    let _ = self
      .index
      .pg_database
      .pg_update_rune_mints(id, rune_entry.mints);

    Ok(Some(Lot(amount)))
  }

  fn tx_commits_to_rune(&self, tx: &Transaction, rune: Rune) -> Result<bool> {
    let commitment = rune.commitment();

    for input in &tx.input {
      // extracting a tapscript does not indicate that the input being spent
      // was actually a taproot output. this is checked below, when we load the
      // output's entry from the database
      let Some(tapscript) = input.witness.tapscript() else {
        continue;
      };

      for instruction in tapscript.instructions() {
        // ignore errors, since the extracted script may not be valid
        let Ok(instruction) = instruction else {
          break;
        };

        let Some(pushbytes) = instruction.push_bytes() else {
          continue;
        };

        if pushbytes.as_bytes() != commitment {
          continue;
        }

        let Some(tx_info) = self
          .client
          .get_raw_transaction_info(&input.previous_output.txid, None)
          .into_option()?
        else {
          panic!(
            "can't get input transaction: {}",
            input.previous_output.txid
          );
        };

        let taproot = tx_info.vout[input.previous_output.vout.into_usize()]
          .script_pub_key
          .script()?
          .is_v1_p2tr();

        if !taproot {
          continue;
        }

        let commit_tx_height = self
          .client
          .get_block_header_info(&tx_info.blockhash.unwrap())
          .into_option()?
          .unwrap()
          .height;

        let confirmations = self
          .height
          .checked_sub(commit_tx_height.try_into().unwrap())
          .unwrap()
          + 1;

        if confirmations >= Runestone::COMMIT_CONFIRMATIONS.into() {
          return Ok(true);
        }
      }
    }

    Ok(false)
  }

  fn unallocated(&mut self, tx: &Transaction) -> Result<HashMap<RuneId, Lot>> {
    // map of rune ID to un-allocated balance of that rune
    let mut unallocated: HashMap<RuneId, Lot> = HashMap::new();

    // increment unallocated runes with the runes in tx inputs
    for (index, input) in tx.input.iter().enumerate() {
      if let Some(guard) = self
        .outpoint_to_balances
        .remove(&input.previous_output.store())?
      {
        let buffer = guard.value();
        let mut i = 0;
        while i < buffer.len() {
          let ((id, balance), len) = Index::decode_rune_balance(&buffer[i..]).unwrap();
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
}
