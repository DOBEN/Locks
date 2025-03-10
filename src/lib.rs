//! Token with locking and schedule transfer features.
//!
//!
//! # Schedule transfer Definition
//!
//! A `schedule transfer` is the operation when Alice transfers tokens to Bob with a time lock and the following release behavior:
//! The balance is immediately subtracted from Alice's balance and added to Bob's balance but locked (meaning Bob has the funds
//! not at his disposal) until the timelock has passed.
//!
//! For example: Timelock is 5 hours, amount transferred is 1 token, Alice's token balance is A, and Bob's token balance is B.
//!
//!                              Time | block with timestamp x (including the TokenScheduleTransferTransaction) | block with timestamp x + 5 hours
//! -----------------------------------------------------------------------------------------------------------------------------------
//! Alice Token Balance (at disposal) | A - 1                                                                   | A - 1
//! -----------------------------------------------------------------------------------------------------------------------------------
//! Bob Token Balance (at disposal)   | B                                                                       | B + 1
//! Bob Token Balance (locked)        | 1                                                                       | 0
//!
//!
//! # Schedule transfer Definition
//!
//! A `lock` is the operation when Alice transfers tokens to Bob with a time lock and the following release behavior:
//! The balance is accounted for on Alice's balance but locked (meaning Alice has the funds not at her disposal) and when
//! the the timelock has passed the transfered token is accounted for on Bob's balance.
//!
//! For example: Timelock is 5 hours, amount transferred is 1 token, Alice's token balance is A, and Bob's token balance is B.
//!
//!                              Time | block with timestamp x (including the TokenLockTransaction)             | block with timestamp x + 5 hours
//! -----------------------------------------------------------------------------------------------------------------------------------
//! Alice Token Balance (at disposal) | A - 1                                                                   | A - 1
//! Alice Token Balance (locked)      | 1                                                                       | 0
//!  
//! -----------------------------------------------------------------------------------------------------------------------------------
//! Bob Token Balance (at disposal)   | B                                                                       | B + 1
//!  
//!
//! # Motivation
//! Locking and schedule transfers are common financial operation and usually implemented in the web3 world via `escrow smart contracts`. E.g. Alice sends the funds to the `escrow smart contract`
//! and Bob withdraws the funds after the lock has passed. The funds are accounted for on the balance of the `escrow smart contracts` during the time of the lock.
//! This `escrow` setup has several drawbacks:
//! - Legal implication (licenses and registrations) for the people/business behind the `escrow smart contracts` since they are `in-control` of the users' funds (money-transferring business).
//! - Alice/Bob do not want yield-bearing tokens to be accounted for on an `escrow smart contracts` balance since Alice/Bob will loose revenue.
//! - Bob needs to send a second transaction to claim his funds from the `escrow`.
//!
//! # Implemention of the time locks in the token smart contract
//! To avoid `escrow smart contracts`, the time locks are implemented as part of the token smart contract logic by adding the Bitcoin UTXO model
//! on top-of the Ethereum-style token account balance model. The token smart contract will track the locked/scheduled_transfer balances on the
//! account address that they are associated with. Even `smart contracts` can create `locks/schedule_transfers` with the funds on their balance.
//!
//! # Some disadvantages:
//! It is advised to have an indexer track the UTXO_SET off-chain (based on the events) to provide/calculate for the users which UTXOs should be fed into the `state_transition/transfer` function.
//! The off-chain tool also should accumulate all UTXOs associated with a user and provide a more comprehensive overview of which balance is locked/at disposal for a given user to spend.
//! This is because the on-chain UTXO_SET is unbounded and we cannot/should not iterate over unbounded/large sets in a smart contract, meaning we should NOT provide a query function
//! over the whole UTXO_SET on-chain.
//!
//! TODO: Include a mechanism for allowing `utxo_index` to overflow (or at least to use the
//!  old funds even if no new `utxo_index` is available anymore).
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis2::{Cis2Event, *};
use concordium_std::{collections::BTreeMap, *};

/// The id of the token in this contract.
pub const TOKEN_ID: ContractTokenId = TokenIdUnit();

/// Sha256 digest
pub type Sha256 = [u8; 32];

// Types

/// Contract token ID type.
/// Since this contract will only ever contain this one token type, we use the
/// smallest possible token ID.
pub type ContractTokenId = TokenIdUnit;

/// Contract token amount type.
/// Since this contract is wrapping the CCD and the CCD can be represented as a
/// u64, we can specialize the token amount to u64 reducing module size and cost
/// of arithmetics.
pub type ContractTokenAmount = TokenAmountU64;

/// Event tags.
pub const CREATED_UTXO_EVENT_TAG: u8 = 0;
pub const DESTROYED_UTXO_EVENT_TAG: u8 = 1;

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial, Deserial, PartialEq, Eq)]
#[concordium(repr(u8))]
pub enum TokenEvent {
    ///
    #[concordium(tag = 0)]
    CreatedUTXO(CreatedUTXOEvent),
    ///
    #[concordium(tag = 1)]
    DestroyedUTXO(DestroyedUTXOEvent),
    /// Cis2 token events.
    #[concordium(forward = cis2_events)]
    Cis2Event(Cis2Event<ContractTokenId, ContractTokenAmount>),
}

///
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct DestroyedUTXOEvent {
    ///
    pub token_id: ContractTokenId,
    ///
    pub utxo_index: u64,
    ///
    pub utxo: SpendingRestriction,
    ///
    pub at: Address,
}

///
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct CreatedUTXOEvent {
    ///
    pub token_id: ContractTokenId,
    ///
    pub utxo_index: u64,
    ///
    pub utxo: SpendingRestriction,
    ///
    pub at: Address,
}

// Implementing a custom schemaType for the `TokenEvent` struct containing all
// CIS2 like events and custom events of this token contract. This custom implementation flattens the fields to avoid one
// level of nesting. Deriving the schemaType would result in e.g.: {"Nonce":
// [{...fields}] }. In contrast, this custom schemaType implementation results
// in e.g.: {"Nonce": {...fields} }
impl schema::SchemaType for TokenEvent {
    fn get_type() -> schema::Type {
        let mut event_map = BTreeMap::new();
        // Custom events:
        event_map.insert(
            CREATED_UTXO_EVENT_TAG,
            (
                "CreatedUTXO".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("utxo_index"), u64::get_type()),
                    (String::from("utxo"), SpendingRestriction::get_type()),
                    (String::from("at"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            DESTROYED_UTXO_EVENT_TAG,
            (
                "DestroyedUTXO".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("utxo_index"), u64::get_type()),
                    (String::from("utxo"), SpendingRestriction::get_type()),
                    (String::from("at"), Address::get_type()),
                ]),
            ),
        );

        // CIS2 like events:
        event_map.insert(
            TRANSFER_EVENT_TAG,
            (
                "Transfer".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("amount"), ContractTokenAmount::get_type()),
                    (String::from("from"), Address::get_type()),
                    (String::from("to"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            MINT_EVENT_TAG,
            (
                "Mint".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("amount"), ContractTokenAmount::get_type()),
                    (String::from("owner"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            BURN_EVENT_TAG,
            (
                "Burn".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("amount"), ContractTokenAmount::get_type()),
                    (String::from("owner"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            UPDATE_OPERATOR_EVENT_TAG,
            (
                "UpdateOperator".to_string(),
                schema::Fields::Named(vec![
                    (String::from("update"), OperatorUpdate::get_type()),
                    (String::from("owner"), Address::get_type()),
                    (String::from("operator"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            TOKEN_METADATA_EVENT_TAG,
            (
                "TokenMetadata".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("metadata_url"), MetadataUrl::get_type()),
                ]),
            ),
        );
        schema::Type::TaggedEnum(event_map)
    }
}

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
pub struct Lock {
    pub amount: ContractTokenAmount,
    /// Time when the lock is expired and the creator of the lock is free to transfer/use these funds again.
    pub remove_time: Timestamp,
}

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone, Copy)]
pub struct ScheduleTransfer {
    pub amount: ContractTokenAmount,
    /// Time when the schedule is expired and the account is free to transfer these funds.
    pub release_time: Timestamp,
}

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone, Copy)]
pub enum SpendingRestriction {
    NoRestriction(ContractTokenAmount),
    LockRecipient(ScheduleTransfer),
    LockSender(ScheduleTransfer),
    ScheduleTransfer(ScheduleTransfer),
}

impl SpendingRestriction {
    fn amount(self) -> TokenAmountU64 {
        match self {
            SpendingRestriction::NoRestriction(token_amount_u64) => token_amount_u64,
            SpendingRestriction::LockRecipient(lock) => lock.amount,
            SpendingRestriction::LockSender(lock) => lock.amount,
            SpendingRestriction::ScheduleTransfer(schedule_transfer) => schedule_transfer.amount,
        }
    }

    fn release_time(self) -> Option<Timestamp> {
        match self {
            SpendingRestriction::NoRestriction(_) => None,
            SpendingRestriction::LockRecipient(lock) => Some(lock.release_time),
            SpendingRestriction::LockSender(_) => None,
            SpendingRestriction::ScheduleTransfer(schedule_transfer) => {
                Some(schedule_transfer.release_time)
            }
        }
    }
    fn remove_time(self) -> Option<Timestamp> {
        match self {
            SpendingRestriction::NoRestriction(_) => None,
            SpendingRestriction::LockRecipient(_) => None,
            SpendingRestriction::LockSender(lock) => Some(lock.release_time),
            SpendingRestriction::ScheduleTransfer(_) => None,
        }
    }
}

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
pub struct UTXO {
    /// A unique index for this UTXO across all UTXOs ever existed in this smart contract.
    pub utxo_index: u64,
    pub spending_restriction: SpendingRestriction,
}

#[derive(Serialize, SchemaType, Debug)]
pub struct LockConnection {
    pub from: Address,
    pub to: Address,
    pub transfer_event_emitted: bool,
}

/// The state tracked for each address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
pub struct AddressState<S = StateApi> {
    /// Set of UTXOs that above balance is divided into.
    pub utxo_map: StateMap<u64, SpendingRestriction, S>,
    /// The address which are currently enabled as operators for this token and
    /// this address.
    pub operators: StateSet<Address, S>,
}

/// The contract state,
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi = StateApi> {
    /// Metadata URL
    token_metadata: StateBox<MetadataUrl, S>,
    /// A sequential counter that assigns each newly created UTXO a unique index.
    utxo_counter: u64,
    ///
    lock_connection: StateMap<u64, LockConnection, S>,
    /// All tokens in the contract.
    token: StateMap<Address, AddressState<S>, S>,
}

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
pub struct UTXOToCreate {
    pub recipient: Address,
    pub spending_restriction: SpendingRestrictionToCreate,
}

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
pub enum SpendingRestrictionToCreate {
    NoRestriction(ContractTokenAmount),
    Lock(ScheduleTransfer),
    ScheduleTransfer(ScheduleTransfer),
}

impl UTXOToCreate {
    fn amount(self) -> ContractTokenAmount {
        match self.spending_restriction {
            SpendingRestrictionToCreate::NoRestriction(amount) => amount,
            SpendingRestrictionToCreate::Lock(lock) => lock.amount,
            SpendingRestrictionToCreate::ScheduleTransfer(utxo) => utxo.amount,
        }
    }
}

/// The parameter for the contract function `mint` function which mints a number
/// of tokens to the owner's address.
#[derive(Serialize, SchemaType, Clone)]
pub struct MintParams {
    /// Owner of the newly minted tokens.
    pub owner: Receiver,
    /// Amount of tokens.
    pub amount: ContractTokenAmount,
    /// Additional data that can be sent to the receiving contract.
    pub data: AdditionalData,
}

/// The parameter type for the contract function `unwrap`.
/// Takes an amount of tokens and unwraps the CCD and sends it to a receiver.
#[derive(Serialize, SchemaType)]
pub struct StateTransitionParameter {
    /// The UTXOs to destroy as part of the state transition.
    pub in_utxos: Vec<UTXO>,
    /// The UTXOs to create as part of the state transition.
    ///
    /// The last element in the `out_utxos` vector is usually the `change` that goes
    /// back to the `sender/invoker` of the `state_transition` function
    /// since the sender might not have a set of UTXOs that perfectly equals
    /// the required amount needed for covering the expenses for the `out_utxos` vector.
    pub out_utxos: Vec<UTXOToCreate>,
}

// Vector of `utxo_indexes` associated to old lock UTXOs that should have their transfer event emitted now.
// This entrypoint should be called regularly by a backend to `emit` the associated transfer events at the time that the lock is released.
// This simulates a process in the node where this part will be automated.
// The `TransferEvents` have the same format as `CIS2 Tokens` currently, which requires this `clean-up`/`emittingEvents` function at the
// time the lock is released. If keeping the same format for the `TransferEvents` as `CIS2 Tokens` is not so relevant, emitting
// the `TransferEvents` at the time the UTXOs are created with an addional field for the `release_time` that the transfer will happen might be preferable
// instead of this function/mechanism.
#[receive(
    contract = "token",
    name = "emitLockTransferEvent",
    parameter = "Vec<u64>",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn emit_lock_transfer_event(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: Vec<u64> = ctx.parameter_cursor().get()?;

    emit_lock_transfer_event_internal(params, ctx, host, logger)?;

    Ok(())
}

fn emit_lock_transfer_event_internal(
    vec_utxo_indexes: Vec<u64>,
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    for utxo_index in vec_utxo_indexes {
        // Check that we haven't emitted the event yet, and update flag.
        let Some(mut lock_connection) = host.state.lock_connection.get_mut(&utxo_index) else {
            return Err(ContractError::Custom(CustomContractError::LogRestriction));
        };

        ensure!(
            !lock_connection.transfer_event_emitted,
            ContractError::Custom(CustomContractError::LogRestriction)
        );
        lock_connection.transfer_event_emitted = true;

        let from_lock = host
            .state
            .token
            .get(&lock_connection.from)
            .and_then(|address_state| {
                address_state
                    .utxo_map
                    .get(&utxo_index)
                    .and_then(|utxo_state| match *utxo_state {
                        SpendingRestriction::LockSender(lock) => Some(lock),
                        _ => None,
                    })
            });

        let to_lock = host
            .state
            .token
            .get(&lock_connection.from)
            .and_then(|address_state| {
                address_state
                    .utxo_map
                    .get(&utxo_index)
                    .and_then(|utxo_state| match *utxo_state {
                        SpendingRestriction::LockSender(lock) => Some(lock),
                        _ => None,
                    })
            });

        if let (Some(_), Some(to_lock)) = (from_lock, to_lock) {
            // Check that log is released by now.
            ensure!(
                to_lock.release_time < ctx.metadata().slot_time(),
                ContractError::Custom(CustomContractError::LogRestriction)
            );
            // Log outstanding CIS2 transfer event (lock case)
            logger.log(&TokenEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
                token_id: TOKEN_ID,
                amount: to_lock.amount,
                from: lock_connection.from,
                to: lock_connection.to,
            })))?;
        } else {
            return Err(ContractError::Custom(CustomContractError::LogRestriction));
        }
    }

    Ok(())
}

#[receive(
    contract = "token",
    name = "transfer",
    parameter = "StateTransitionParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn transfer(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    // Parse the parameter.
    let params: StateTransitionParameter = ctx.parameter_cursor().get()?;

    let mut sum_amounts_in_utxos = TokenAmountU64::default();
    let mut sum_amounts_out_utxos = TokenAmountU64::default();

    // Check if we still need to emit the `transferEvent` for old locks.
    let utxo_indexes = params
        .in_utxos
        .clone()
        .into_iter()
        .filter_map(|x| {
            if let SpendingRestriction::LockSender(_) = x.spending_restriction {
                Some(x.utxo_index)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    emit_lock_transfer_event_internal(utxo_indexes, ctx, host, logger)?;

    let (state, state_builder) = host.state_and_builder();
    {
        let mut sender_token_state = state.token.entry(sender).or_insert_with(|| AddressState {
            utxo_map: state_builder.new_map(),
            operators: state_builder.new_set(),
        });

        for utox in params.in_utxos {
            sum_amounts_in_utxos += utox.spending_restriction.amount();

            let sender_utxo_in_state = sender_token_state.utxo_map.remove_and_get(&utox.utxo_index);

            // TODO: Maybe enable `operators` to spend UTXOs on behalf of the sender, similar to:
            //
            // // Authenticate the sender for this transfer
            // ensure!(
            //     from == sender || state.is_operator(&sender, &from),
            //     ContractError::Unauthorized
            // );

            // Check that `UTXO_in` exists in sender's state.
            ensure!(sender_utxo_in_state.is_some(), ContractError::Unauthorized);
            let sender_utxo_in_state = sender_utxo_in_state.unwrap();

            // Ensure that the `in_utxos` have no spending restriction
            // (e.g., locks and scheduled transfers are past/before the release/remove timestamps).
            if let Some(release_time) = sender_utxo_in_state.release_time() {
                ensure!(
                    release_time >= ctx.metadata().slot_time(),
                    ContractError::Custom(CustomContractError::SpendingRestriction)
                );
            }
            if let Some(remove_time) = sender_utxo_in_state.remove_time() {
                ensure!(
                    remove_time < ctx.metadata().slot_time(),
                    ContractError::Custom(CustomContractError::SpendingRestriction)
                );
            }

            // Log destroyed UTXO event
            logger.log(&TokenEvent::DestroyedUTXO(DestroyedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: utox.utxo_index,
                utxo: sender_utxo_in_state,
                at: sender,
            }))?;
        }
    }

    for utox in params.out_utxos {
        sum_amounts_out_utxos += utox.clone().amount();

        // create the `out_utxos`:
        // - a created `Lock` UTXO is usually added the the sender's UTXO set.
        // - a created `ScheduleTransfer` UTXO is usually added the the recipients's UTXO set immediatly.
        // - a created `NoRestriction` UTXO is usually added the the recipients's UTXO set immediatly (this operation is equivalent to the standard CIS2-transfer).
        //   or the `change` UTXO (last element in the `out_utxos` vector) that is usually added the the recipients's UTXO set.
        match utox.spending_restriction {
            SpendingRestrictionToCreate::NoRestriction(amount) => {
                let utxo_index = state.utxo_counter;
                let utxo = SpendingRestriction::NoRestriction(amount);
                let recipient = utox.recipient;

                let mut receipient_token_state =
                    state
                        .token
                        .entry(recipient)
                        .or_insert_with(|| AddressState {
                            utxo_map: state_builder.new_map(),
                            operators: state_builder.new_set(),
                        });
                _ = receipient_token_state.utxo_map.insert(utxo_index, utxo);

                // Log created UTXO event
                logger.log(&TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                    token_id: TOKEN_ID,
                    utxo_index,
                    utxo,
                    at: recipient,
                }))?;

                // Log CIS2 transfer event
                logger.log(&TokenEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
                    token_id: TOKEN_ID,
                    amount,
                    from: sender,
                    to: recipient,
                })))?;
            }
            SpendingRestrictionToCreate::Lock(schedule_transfer) => {
                // Update of the sender's state
                {
                    let utxo_index = state.utxo_counter;
                    let utxo = SpendingRestriction::LockSender(schedule_transfer);

                    let mut sender_token_state = state
                        .token
                        .get_mut(&sender)
                        .ok_or(ContractError::InsufficientFunds)?;

                    _ = sender_token_state.utxo_map.insert(utxo_index, utxo);

                    // Log created UTXO event
                    logger.log(&TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                        token_id: TOKEN_ID,
                        utxo_index,
                        utxo,
                        at: sender,
                    }))?;
                }

                // Update of the recipient's state
                let utxo_index = state.utxo_counter;
                let utxo = SpendingRestriction::LockRecipient(schedule_transfer);
                let recipient = utox.recipient;

                let mut receipient_token_state =
                    state
                        .token
                        .entry(recipient)
                        .or_insert_with(|| AddressState {
                            utxo_map: state_builder.new_map(),
                            operators: state_builder.new_set(),
                        });
                _ = receipient_token_state.utxo_map.insert(utxo_index, utxo);

                // Log created UTXO event
                logger.log(&TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                    token_id: TOKEN_ID,
                    utxo_index,
                    utxo,
                    at: recipient,
                }))?;

                // Emitting the `CIS2 transfer event` is postponed in the `lock` case (see comment at function `emitLockTransferEvent`).
                // We track the `lock_connection` in the state which will be used
                // by the `emitLockTransferEvent` function.
                let old_entry = state.lock_connection.insert(
                    utxo_index,
                    LockConnection {
                        from: sender,
                        to: recipient,
                        transfer_event_emitted: false,
                    },
                );
                ensure!(
                    old_entry.is_none(),
                    ContractError::Custom(CustomContractError::LockConnectionAlreadyExists)
                );
            }
            SpendingRestrictionToCreate::ScheduleTransfer(schedule_transfer) => {
                let utxo_index = state.utxo_counter;
                let utxo = SpendingRestriction::ScheduleTransfer(schedule_transfer);
                let recipient = utox.recipient;

                let mut receipient_token_state =
                    state
                        .token
                        .entry(recipient)
                        .or_insert_with(|| AddressState {
                            utxo_map: state_builder.new_map(),
                            operators: state_builder.new_set(),
                        });
                _ = receipient_token_state.utxo_map.insert(utxo_index, utxo);

                // Log created UTXO event
                logger.log(&TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                    token_id: TOKEN_ID,
                    utxo_index,
                    utxo,
                    at: recipient,
                }))?;

                // Log CIS2 transfer event
                logger.log(&TokenEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
                    token_id: TOKEN_ID,
                    amount: schedule_transfer.amount,
                    from: sender,
                    to: recipient,
                })))?;
            }
        }
        state.utxo_counter += 1;
    }

    // Check that the sum of the amounts in `in_utxos` equals the sum of the amounts in `out_utxos`.
    ensure!(
        sum_amounts_in_utxos == sum_amounts_out_utxos,
        ContractError::Custom(CustomContractError::MismatchOfUTXOSums)
    );

    // TODO: If the receivers are contracts: invoke the receive hook functions.

    Ok(())
}

/// The parameter type for the contract function `setMetadataUrl`.
#[derive(Serialize, SchemaType, Clone, PartialEq, Eq, Debug)]
pub struct SetMetadataUrlParams {
    /// The URL following the specification RFC1738.
    pub url: String,
    /// The hash of the document stored at the above URL.
    pub hash: Option<Sha256>,
}

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
pub enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams, // -1
    /// Failed logging: Log is full.
    LogFull, // -2
    /// Failed logging: Log is malformed.
    LogMalformed, // -3
    /// Failed to invoke a contract.
    InvokeContractError, // -4
    /// Failed to invoke a transfer.
    InvokeTransferError, // -5
    MismatchOfUTXOSums,          // -6
    SpendingRestriction,         // -7
    LogRestriction,              // -8
    LockConnectionAlreadyExists, // -9
}

pub type ContractError = Cis2Error<CustomContractError>;

pub type ContractResult<A> = Result<A, ContractError>;

/// Mapping the logging errors to ContractError.
impl From<LogError> for CustomContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// Mapping errors related to contract invocations to CustomContractError.
impl<T> From<CallContractError<T>> for CustomContractError {
    fn from(_cce: CallContractError<T>) -> Self {
        Self::InvokeContractError
    }
}

/// Mapping errors related to contract invocations to CustomContractError.
impl From<TransferError> for CustomContractError {
    fn from(_te: TransferError) -> Self {
        Self::InvokeTransferError
    }
}

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self {
        Cis2Error::Custom(c)
    }
}

impl State {
    /// Creates a new state with no one owning any tokens by default.
    fn new(state_builder: &mut StateBuilder, metadata_url: MetadataUrl) -> Self {
        State {
            utxo_counter: 0u64,
            token: state_builder.new_map(),
            token_metadata: state_builder.new_box(metadata_url),
            lock_connection: state_builder.new_map(),
        }
    }

    /// Get the current balance of a given token id for a given address.
    fn balance(&self, address: &Address, slot_time: Timestamp) -> ContractResult<TokenBalances> {
        if let Some(address_state) = self.token.get(address) {
            let mut total: ContractTokenAmount = 0u64.into();
            let mut disposal: ContractTokenAmount = 0u64.into();
            let mut locked: ContractTokenAmount = 0u64.into();

            for (_, spending_restriction) in address_state.utxo_map.iter() {
                let amount = spending_restriction.amount();

                if let Some(release_time) = spending_restriction.release_time() {
                    if release_time >= slot_time {
                        locked += amount;
                    } else {
                        disposal += amount;
                    }
                    total += amount;
                }

                if let Some(remove_time) = spending_restriction.remove_time() {
                    if remove_time < slot_time {
                        locked += amount;
                        total += amount;
                    }
                }

                if let SpendingRestriction::NoRestriction(_) = *spending_restriction {
                    disposal += amount;
                    total += amount;
                }
            }

            Ok(TokenBalances::new_with_values(total, disposal, locked))
        } else {
            Ok(TokenBalances::new())
        }
    }

    /// Check if an address is an operator of a specific owner address.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        self.token
            .get(owner)
            .map(|address_state| address_state.operators.contains(address))
            .unwrap_or(false)
    }

    /// Update the state adding a new operator for a given token id and address.
    /// Succeeds even if the `operator` is already an operator for this `address`.
    fn add_operator(
        &mut self,
        owner: &Address,
        operator: &Address,
        state_builder: &mut StateBuilder,
    ) {
        let mut owner_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            utxo_map: state_builder.new_map(),
            operators: state_builder.new_set(),
        });
        owner_state.operators.insert(*operator);
    }

    /// Update the state removing an operator for a given and address.
    /// Succeeds even if the `operator` is not an operator for this `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.token.entry(*owner).and_modify(|address_state| {
            address_state.operators.remove(operator);
        });
    }

    /// Mint an amount of tokens.
    fn mint(
        &mut self,
        amount: ContractTokenAmount,
        owner: &Address,
        state_builder: &mut StateBuilder,
    ) -> ContractResult<()> {
        let mut owner_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            utxo_map: state_builder.new_map(),
            operators: state_builder.new_set(),
        });

        _ = owner_state.utxo_map.insert(
            self.utxo_counter,
            SpendingRestriction::NoRestriction(amount),
        );
        self.utxo_counter += 1;

        Ok(())
    }
}

// Contract functions

/// Initialize contract instance with no initial tokens.
/// Logs a `TokenMetadata` event with the metadata url and hash.
#[init(
    contract = "token",
    enable_logger,
    parameter = "SetMetadataUrlParams",
    event = "TokenEvent"
)]
fn contract_init(
    ctx: &InitContext,
    state_builder: &mut StateBuilder,
    logger: &mut impl HasLogger,
) -> InitResult<State> {
    // Parse the parameter.
    let params: SetMetadataUrlParams = ctx.parameter_cursor().get()?;

    // Create the metadata_url
    let metadata_url = MetadataUrl {
        url: params.url.clone(),
        hash: params.hash,
    };

    // Construct the initial contract state.
    let state = State::new(state_builder, metadata_url.clone());

    // Log event for where to find metadata for the token
    logger.log(&TokenEvent::Cis2Event(Cis2Event::TokenMetadata(
        TokenMetadataEvent {
            token_id: TOKEN_ID,
            metadata_url,
        },
    )))?;

    Ok(state)
}

/// Mint an amount of new tokens to the
/// `owner` address. ATTENTION: Can be called by anyone. You should add your
/// custom access control to this function.
///
/// Logs a `Mint` event for each token.
///
/// It rejects if:
/// - Fails to parse parameter.
/// - Fails to log Mint event.
///
/// TODO: Add logic to also create `schedule_transfers/locks` instead of only `NoRestriction` UTXOs.
#[receive(
    contract = "token",
    name = "mint",
    parameter = "MintParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_mint(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: MintParams = ctx.parameter_cursor().get()?;

    let (state, builder) = host.state_and_builder();
    let owner = match params.owner {
        Receiver::Account(account_address) => Address::from(account_address),
        Receiver::Contract(contract_address, _) => Address::from(contract_address),
    };

    // Update the contract state
    state.mint(params.amount, &owner, builder)?;

    // If the receiver is a contract: invoke the receive hook function.
    if let Receiver::Contract(address, function) = params.owner {
        let parameter = OnReceivingCis2Params {
            token_id: TOKEN_ID,
            amount: params.amount,
            from: Address::from(address),
            data: params.data,
        };
        host.invoke_contract(
            &address,
            &parameter,
            function.as_entrypoint_name(),
            Amount::zero(),
        )?;
    }

    // Log event for the newly minted token.
    logger.log(&TokenEvent::Cis2Event(Cis2Event::Mint(MintEvent {
        token_id: TOKEN_ID,
        amount: params.amount,
        owner,
    })))?;

    Ok(())
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(
    contract = "token",
    name = "updateOperator",
    parameter = "UpdateOperatorParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_operator(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let UpdateOperatorParams(params) = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let (state, state_builder) = host.state_and_builder();
    for param in params {
        // Update the operator in the state.
        match param.update {
            OperatorUpdate::Add => state.add_operator(&sender, &param.operator, state_builder),
            OperatorUpdate::Remove => state.remove_operator(&sender, &param.operator),
        }

        // Log the appropriate event
        logger.log(&TokenEvent::Cis2Event(Cis2Event::UpdateOperator(
            UpdateOperatorEvent {
                owner: sender,
                operator: param.operator,
                update: param.update,
            },
        )))?;
    }

    Ok(())
}

/// Parameter type for the CIS-2 like function `balanceOf` specialized to the subset
/// of TokenIDs used by this contract.
pub type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;

/// Return parameter type for the CIS-2 like function `balanceOf` .
#[derive(Serialize, SchemaType, Debug)]
pub struct TokenBalances {
    pub total_balance: ContractTokenAmount,
    pub at_disposal: ContractTokenAmount,
    pub locked: ContractTokenAmount,
}

impl TokenBalances {
    fn new() -> Self {
        TokenBalances {
            total_balance: 0u64.into(),
            at_disposal: 0u64.into(),
            locked: 0u64.into(),
        }
    }

    fn new_with_values(
        total_balance: ContractTokenAmount,
        at_disposal: ContractTokenAmount,
        locked: ContractTokenAmount,
    ) -> Self {
        TokenBalances {
            total_balance,
            at_disposal,
            locked,
        }
    }
}

/// View function for testing. This function potentially goes through a long array of UTXOs.
/// The recommended way would be track the UTXO set off-chain and provided a `balanceOf` function
/// off-chain instead of this on-chain function.
/// Get the balance (total, at_disposal, and locked balances) of given token IDs and addresses.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "token",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    return_value = "Vec<TokenBalances>",
    error = "ContractError"
)]
fn contract_balance_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<Vec<TokenBalances>> {
    // Parse the parameter.
    let params: ContractBalanceOfQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        ensure_eq!(query.token_id, TOKEN_ID, ContractError::InvalidTokenId);

        // Query the state for balance.
        let balances = host
            .state()
            .balance(&query.address, ctx.metadata().slot_time())?;
        response.push(balances);
    }
    Ok(response)
}

/// Takes a list of queries. Each query contains an owner address and some
/// address that will be checked if it is an operator to the owner address.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "token",
    name = "operatorOf",
    parameter = "OperatorOfQueryParams",
    return_value = "OperatorOfQueryResponse",
    error = "ContractError"
)]
fn contract_operator_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<OperatorOfQueryResponse> {
    // Parse the parameter.
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state if the `address` being an `operator` of `owner`.
        let is_operator = host.state().is_operator(&query.address, &query.owner);
        response.push(is_operator);
    }
    let result = OperatorOfQueryResponse::from(response);
    Ok(result)
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
pub struct ViewAddressState {
    pub balances: Vec<(ContractTokenId, ContractTokenAmount)>,
    pub operators: Vec<Address>,
}

#[derive(Serialize, SchemaType, PartialEq, Eq)]
pub struct ViewState {
    pub utxos: Vec<(u64, SpendingRestriction)>,
    pub operators: Vec<Address>,
}

/// View function for testing. This reports on the entire UTXO state of an account.
#[receive(
    contract = "token",
    name = "view",
    parameter = "Address",
    return_value = "ViewState"
)]
fn contract_view(ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<ViewState> {
    // Parse the parameter.
    let address: Address = ctx.parameter_cursor().get()?;

    let token_state = host.state().token.get(&address);

    Ok(ViewState {
        utxos: token_state.as_ref().map_or_else(Vec::new, |item| {
            item.utxo_map.iter().map(|(k, v)| (*k, *v)).collect()
        }),
        operators: token_state
            .as_ref()
            .map_or_else(Vec::new, |item| item.operators.iter().map(|v| *v).collect()),
    })
}
