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
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis2::{Cis2Event, *};
use concordium_std::*;

/// The id of the token in this contract.
pub const TOKEN_ID: ContractTokenId = TokenIdUnit();

/// List of supported standards by this contract address.
pub const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER];

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

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
pub struct Lock {
    pub amount: ContractTokenAmount,
    /// Time when the lock is expired and the creator of the lock is free to transfer/use these funds again.
    pub remove_time: Timestamp,
}

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
pub struct ScheduleTransfer {
    pub amount: ContractTokenAmount,
    /// Time when the schedule is expired and the account is free to transfer these funds.
    pub release_time: Timestamp,
}

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
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

    fn action_time(self) -> Option<Timestamp> {
        match self {
            SpendingRestriction::NoRestriction(_) => None,
            SpendingRestriction::LockRecipient(lock) => Some(lock.release_time),
            SpendingRestriction::LockSender(lock) => Some(lock.release_time),
            SpendingRestriction::ScheduleTransfer(schedule_transfer) => {
                Some(schedule_transfer.release_time)
            }
        }
    }
}

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
pub struct UTXO {
    /// A unique index for this UTXO across all UTXOs ever existed in this smart contract.
    pub utxo_index: u64,
    pub spending_restriction: SpendingRestriction,
}

/// The state tracked for each address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
pub struct AddressState<S = StateApi> {
    // TODO?
    /// The number of tokens owned by this address (locked + scheduled + notRestrictedBalance).
    // pub total_balance: ContractTokenAmount,

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

#[receive(
    contract = "token",
    name = "state_transition",
    parameter = "StateTransitionParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn state_transition(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    let (state, state_builder) = host.state_and_builder();
    // Parse the parameter.
    let params: StateTransitionParameter = ctx.parameter_cursor().get()?;

    let mut sum_amounts_in_utxos = TokenAmountU64::default();
    let mut sum_amounts_out_utxos = TokenAmountU64::default();

    {
        let mut sender_token_state = state.token.entry(sender).or_insert_with(|| AddressState {
            utxo_map: state_builder.new_map(),
            // total_balance: 0u64.into(),
            operators: state_builder.new_set(),
        });

        for utox in params.in_utxos {
            sum_amounts_in_utxos += utox.spending_restriction.amount();

            let sender_utxo_in_state = sender_token_state.utxo_map.remove_and_get(&utox.utxo_index);

            if let Some(sender_utxo) = sender_utxo_in_state {
                // Ensure that the `in_utxos` have no spending restriction (e.g., locks and scheduled transfers are past the release timestamp).
                if let Some(release_time) = sender_utxo.action_time() {
                    ensure!(
                        release_time < ctx.metadata().slot_time(),
                        ContractError::Custom(CustomContractError::SpendingRestriction)
                    );
                }
            } else {
                return Err(ContractError::Custom(
                    CustomContractError::InputUTXOIndexError,
                ));
            }
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
                let mut receipient_token_state =
                    state
                        .token
                        .entry(utox.recipient)
                        .or_insert_with(|| AddressState {
                            utxo_map: state_builder.new_map(),
                            // total_balance:amount,
                            operators: state_builder.new_set(),
                        });
                _ = receipient_token_state.utxo_map.insert(
                    state.utxo_counter,
                    SpendingRestriction::NoRestriction(amount),
                );
            }
            SpendingRestrictionToCreate::Lock(schedule_transfer) => {
                {
                    let mut sender_token_state = state
                        .token
                        .get_mut(&sender)
                        .ok_or(ContractError::InsufficientFunds)?;

                    _ = sender_token_state.utxo_map.insert(
                        state.utxo_counter,
                        SpendingRestriction::LockSender(schedule_transfer.clone()),
                    );
                }

                let mut receipient_token_state =
                    state
                        .token
                        .entry(utox.recipient)
                        .or_insert_with(|| AddressState {
                            utxo_map: state_builder.new_map(),
                            // total_balance: 0u64.into(),
                            operators: state_builder.new_set(),
                        });
                _ = receipient_token_state.utxo_map.insert(
                    state.utxo_counter,
                    SpendingRestriction::LockRecipient(schedule_transfer),
                );
            }
            SpendingRestrictionToCreate::ScheduleTransfer(schedule_transfer) => {
                let mut receipient_token_state =
                    state
                        .token
                        .entry(utox.recipient)
                        .or_insert_with(|| AddressState {
                            utxo_map: state_builder.new_map(),
                            // total_balance: 0u64.into(),
                            operators: state_builder.new_set(),
                        });
                _ = receipient_token_state.utxo_map.insert(
                    state.utxo_counter,
                    SpendingRestriction::ScheduleTransfer(schedule_transfer),
                );
            }
        }
        state.utxo_counter += 1
    }

    // Check that the sum of the amounts in `in_utxos` equals the sum of the amounts in `out_utxos`.
    ensure!(
        sum_amounts_in_utxos == sum_amounts_out_utxos,
        ContractError::Custom(CustomContractError::MismatchOfUTXOSums)
    );

    // TODO: Emit events of the `destroyed` UTXOs and the `created` UTXOs (e.g. TransferEvent).
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

/// Tagged events to be serialized for the event log.
//  #[derive(SchemaType, Serialize, PartialEq, Eq, Debug)]
pub type TokenEvent = Cis2Event<ContractTokenId, ContractTokenAmount>;

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
pub enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Failed to invoke a transfer.
    InvokeTransferError,
    InputUTXOIndexError,
    MismatchOfUTXOSums,
    SpendingRestriction,
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
        }
    }

    // TODO
    /// Get the current balance of a given token id for a given address.
    fn balance(&self, address: &Address) -> ContractResult<ContractTokenAmount> {
        Ok(0u64.into())
        // Ok(self
        //     .token
        //     .get(address)
        //     .map(|s| s.total_balance)
        //     .unwrap_or_else(|| 0u64.into()))
    }

    // TODO
    /// Update the state with a transfer.
    fn transfer(
        &mut self,
        amount: ContractTokenAmount,
        from: &Address,
        to: &Address,
        state_builder: &mut StateBuilder,
    ) -> ContractResult<()> {
        if amount == 0u64.into() {
            return Ok(());
        }
        // {
        //     let mut from_state = self
        //         .token
        //         .get_mut(from)
        //         .ok_or(ContractError::InsufficientFunds)?;
        //     ensure!(
        //         from_state.total_balance >= amount,
        //         ContractError::InsufficientFunds
        //     );
        //     from_state.total_balance -= amount;
        // }
        // let mut to_state = self.token.entry(*to).or_insert_with(|| AddressState {
        //     utxo_map: state_builder.new_map(),
        //     total_balance: 0u64.into(),
        //     operators: state_builder.new_set(),
        // });
        // to_state.total_balance += amount;

        Ok(())
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
            // total_balance: 0u64.into(),
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
            // total_balance: amount.into(),
            operators: state_builder.new_set(),
        });

        // owner_state.total_balance += amount;
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
    logger.log(&TokenEvent::TokenMetadata(TokenMetadataEvent {
        token_id: TOKEN_ID,
        metadata_url,
    }))?;

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
    logger.log(&TokenEvent::Mint(MintEvent {
        token_id: TOKEN_ID,
        amount: params.amount,
        owner,
    }))?;

    Ok(())
}

type TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

/// Execute a list of token transfers, in the order of the list.
///
/// Logs a `Transfer` event and invokes a receive hook function for every
/// transfer in the list.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the transfers fail to be executed, which could be if:
///     - The `token_id` does not exist.
///     - The sender is not the owner of the token, or an operator for this
///       specific `token_id` and `from` address.
///     - The token is not owned by the `from`.
/// - Fails to log event.
/// - Any of the receive hook function calls rejects.
#[receive(
    contract = "token",
    name = "transfer",
    parameter = "TransferParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_transfer(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let TransferParams(transfers): TransferParameter = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    for Transfer {
        token_id,
        amount,
        from,
        to,
        data,
    } in transfers
    {
        ensure_eq!(token_id, TOKEN_ID, ContractError::InvalidTokenId);

        let (state, builder) = host.state_and_builder();
        // Authenticate the sender for this transfer
        ensure!(
            from == sender || state.is_operator(&sender, &from),
            ContractError::Unauthorized
        );
        let to_address = to.address();
        // Update the contract state
        state.transfer(amount, &from, &to_address, builder)?;

        // Log transfer event
        logger.log(&TokenEvent::Transfer(TransferEvent {
            token_id: TOKEN_ID,
            amount,
            from,
            to: to_address,
        }))?;

        // If the receiver is a contract: invoke the receive hook function.
        if let Receiver::Contract(address, function) = to {
            let parameter = OnReceivingCis2Params {
                token_id: TOKEN_ID,
                amount,
                from,
                data,
            };
            host.invoke_contract(
                &address,
                &parameter,
                function.as_entrypoint_name(),
                Amount::zero(),
            )?;
        }
    }
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
        logger.log(&TokenEvent::UpdateOperator(UpdateOperatorEvent {
            owner: sender,
            operator: param.operator,
            update: param.update,
        }))?;
    }

    Ok(())
}

/// Parameter type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenIDs used by this contract.
pub type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;

pub type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;

/// Get the balance of given token IDs and addresses.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "token",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    return_value = "ContractBalanceOfQueryResponse",
    error = "ContractError"
)]
fn contract_balance_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<ContractBalanceOfQueryResponse> {
    // Parse the parameter.
    let params: ContractBalanceOfQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        ensure_eq!(query.token_id, TOKEN_ID, ContractError::InvalidTokenId);

        // Query the state for balance.
        let amount = host.state().balance(&query.address)?;
        response.push(amount);
    }
    let result = ContractBalanceOfQueryResponse::from(response);
    Ok(result)
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
