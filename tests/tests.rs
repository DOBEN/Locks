//! Tests for the `token` contract.
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std_derive::*;
use token::*;

/// The tests accounts.
const ALICE: AccountAddress =
    account_address!("2wkBET2rRgE8pahuaczxKbmv7ciehqsne57F9gtzf1PVdr2VP3");
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = account_address!("2xBpaHottqhwFZURMZW4uZduQvpxNDSy46iXMYs9kceNGaPpZX");
const BOB_ADDR: Address = Address::Account(BOB);

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

/// A signer for all the transactions.
const SIGNER: Signer = Signer::with_one_key();

/// The metadata url for testing.
const METADATA_URL: &str = "https://example.com";

/// Test no-restriction transfer where sender is the owner.
#[test]
fn test_account_transfer() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Transfer one token from Alice to Bob.
    let transfer_params = StateTransitionParameter {
        in_utxos: vec![UTXO {
            utxo_index: 0u64,
            spending_restriction: SpendingRestriction::NoRestriction(ContractTokenAmount::from(
                100u64,
            )),
        }],
        out_utxos: vec![
            UTXOToCreate {
                recipient: ALICE_ADDR,
                spending_restriction: SpendingRestrictionToCreate::NoRestriction(
                    ContractTokenAmount::from(99u64),
                ),
            },
            UTXOToCreate {
                recipient: BOB_ADDR,
                spending_restriction: SpendingRestrictionToCreate::NoRestriction(
                    ContractTokenAmount::from(1u64),
                ),
            },
        ],
    };

    let update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("token.transfer".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&transfer_params)
                    .expect("No restriction transfer params"),
            },
        )
        .expect("No restriction transfer tokens");

    // Check that Alice now has 99 tokens and Bob has 1 token.
    let utxo_sets = get_utxo_sets(&chain, contract_address);
    let balances = get_balances(&chain, contract_address);

    let expected_utxo_created_alice = SpendingRestriction::NoRestriction(99.into());
    let expected_utxo_created_bob = SpendingRestriction::NoRestriction(1.into());

    let expected_utxo_destroyed = SpendingRestriction::NoRestriction(100.into());

    assert_eq!(utxo_sets.alice, [(1u64, expected_utxo_created_alice)]);
    assert_eq!(utxo_sets.bob, [(2u64, expected_utxo_created_bob)]);
    assert_eq!(
        balances.alice,
        TokenBalances {
            total_balance: 99u64.into(),
            at_disposal: 99u64.into(),
            locked: 0u64.into()
        }
    );
    assert_eq!(
        balances.bob,
        TokenBalances {
            total_balance: 1u64.into(),
            at_disposal: 1u64.into(),
            locked: 0u64.into()
        }
    );

    assert_eq!(utxo_sets.alice, [(1u64, expected_utxo_created_alice)]);
    assert_eq!(utxo_sets.bob, [(2u64, expected_utxo_created_bob)]);

    // Check that a destroy UTXO, a create UTOX, and a transfer event occurred.
    let events = deserialize_update_events(&update);
    assert_eq!(
        events,
        [
            TokenEvent::DestroyedUTXO(DestroyedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: 0u64,
                utxo: expected_utxo_destroyed,
                at: ALICE_ADDR,
            }),
            TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: 1u64,
                utxo: expected_utxo_created_alice,
                at: ALICE_ADDR,
            }),
            TokenEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
                token_id: TOKEN_ID,
                amount: TokenAmountU64(99),
                from: ALICE_ADDR,
                to: ALICE_ADDR,
            })),
            TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: 2u64,
                utxo: expected_utxo_created_bob,
                at: BOB_ADDR,
            }),
            TokenEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
                token_id: TOKEN_ID,
                amount: TokenAmountU64(1),
                from: ALICE_ADDR,
                to: BOB_ADDR,
            }))
        ]
    );
}

/// Test scheduled sender lock transfer where sender is the owner.
#[test]
fn test_account_scheduled_sender_lock_transfer() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Transfer one token from Alice to Bob.
    let transfer_params = StateTransitionParameter {
        in_utxos: vec![UTXO {
            utxo_index: 0u64,
            spending_restriction: SpendingRestriction::NoRestriction(ContractTokenAmount::from(
                100u64,
            )),
        }],
        out_utxos: vec![
            UTXOToCreate {
                recipient: ALICE_ADDR,
                spending_restriction: SpendingRestrictionToCreate::NoRestriction(
                    ContractTokenAmount::from(99u64),
                ),
            },
            UTXOToCreate {
                recipient: BOB_ADDR,
                spending_restriction: SpendingRestrictionToCreate::Lock(ScheduleTransfer {
                    amount: ContractTokenAmount::from(1u64),
                    release_time: Timestamp::from_timestamp_millis(1000),
                }),
            },
        ],
    };

    let update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("token.transfer".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&transfer_params)
                    .expect("Scheduled sender lock transfer params"),
            },
        )
        .expect("Scheduled sender lock transfer tokens to succeed");

    // Check that Alice now has 99 tokens and Bob has 1 token.
    let utxo_sets = get_utxo_sets(&chain, contract_address);
    let balances = get_balances(&chain, contract_address);

    let expected_utxo_created_alice_1 = SpendingRestriction::NoRestriction(99.into());
    let expected_utxo_created_alice_2 = SpendingRestriction::LockSender(ScheduleTransfer {
        amount: ContractTokenAmount::from(1u64),
        release_time: Timestamp::from_timestamp_millis(1000),
    });
    let expected_utxo_created_bob = SpendingRestriction::LockRecipient(ScheduleTransfer {
        amount: ContractTokenAmount::from(1u64),
        release_time: Timestamp::from_timestamp_millis(1000),
    });
    let expected_utxo_destroyed = SpendingRestriction::NoRestriction(100.into());

    assert_eq!(
        utxo_sets.alice,
        [
            (1u64, expected_utxo_created_alice_1),
            (2u64, expected_utxo_created_alice_2)
        ]
    );
    assert_eq!(utxo_sets.bob, [(2u64, expected_utxo_created_bob)]);

    assert_eq!(
        balances.alice,
        TokenBalances {
            total_balance: 100u64.into(),
            at_disposal: 99u64.into(),
            locked: 1u64.into()
        }
    );
    assert_eq!(
        balances.bob,
        TokenBalances {
            total_balance: 0u64.into(),
            at_disposal: 0u64.into(),
            locked: 0u64.into()
        }
    );

    // Check that a destroy UTXO, a create UTOX, and a transfer event occurred.
    let events = deserialize_update_events(&update);
    assert_eq!(
        events,
        [
            TokenEvent::DestroyedUTXO(DestroyedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: 0u64,
                utxo: expected_utxo_destroyed,
                at: ALICE_ADDR,
            }),
            TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: 1u64,
                utxo: expected_utxo_created_alice_1,
                at: ALICE_ADDR,
            }),
            TokenEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
                token_id: TOKEN_ID,
                amount: TokenAmountU64(99),
                from: ALICE_ADDR,
                to: ALICE_ADDR,
            })),
            TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: 2u64,
                utxo: expected_utxo_created_alice_2,
                at: ALICE_ADDR,
            }),
            TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: 2u64,
                utxo: expected_utxo_created_bob,
                at: BOB_ADDR,
            }),
        ]
    );
}

/// Test scheduled receiver lock transfer where sender is the owner.
#[test]
fn test_account_scheduled_receiver_lock_transfer() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Transfer one token from Alice to Bob.
    let transfer_params = StateTransitionParameter {
        in_utxos: vec![UTXO {
            utxo_index: 0u64,
            spending_restriction: SpendingRestriction::NoRestriction(ContractTokenAmount::from(
                100u64,
            )),
        }],
        out_utxos: vec![
            UTXOToCreate {
                recipient: ALICE_ADDR,
                spending_restriction: SpendingRestrictionToCreate::NoRestriction(
                    ContractTokenAmount::from(99u64),
                ),
            },
            UTXOToCreate {
                recipient: BOB_ADDR,
                spending_restriction: SpendingRestrictionToCreate::ScheduleTransfer(
                    ScheduleTransfer {
                        amount: ContractTokenAmount::from(1u64),
                        release_time: Timestamp::from_timestamp_millis(1000),
                    },
                ),
            },
        ],
    };

    let update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("token.transfer".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&transfer_params)
                    .expect("Scheduled receiver lock transfer params"),
            },
        )
        .expect("Scheduled receiver lock transfer tokens to succeed");

    // Check that Alice now has 99 tokens and Bob has 1 token.
    let utxo_sets = get_utxo_sets(&chain, contract_address);
    let balances = get_balances(&chain, contract_address);

    let expected_utxo_created_alice = SpendingRestriction::NoRestriction(99.into());
    let expected_utxo_destroyed = SpendingRestriction::NoRestriction(100.into());
    let expected_utxo_created_bob = SpendingRestriction::ScheduleTransfer(ScheduleTransfer {
        amount: ContractTokenAmount::from(1u64),
        release_time: Timestamp::from_timestamp_millis(1000),
    });

    assert_eq!(utxo_sets.alice, [(1u64, expected_utxo_created_alice)]);
    assert_eq!(utxo_sets.bob, [(2u64, expected_utxo_created_bob)]);

    assert_eq!(
        balances.alice,
        TokenBalances {
            total_balance: 99u64.into(),
            at_disposal: 99u64.into(),
            locked: 0u64.into()
        }
    );
    assert_eq!(
        balances.bob,
        TokenBalances {
            total_balance: 1u64.into(),
            at_disposal: 0u64.into(),
            locked: 1u64.into()
        }
    );

    // Check that a destroy UTXO, a create UTOX, and a transfer event occurred.
    let events = deserialize_update_events(&update);
    assert_eq!(
        events,
        [
            TokenEvent::DestroyedUTXO(DestroyedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: 0u64,
                utxo: expected_utxo_destroyed,
                at: ALICE_ADDR,
            }),
            TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: 1u64,
                utxo: expected_utxo_created_alice,
                at: ALICE_ADDR,
            }),
            TokenEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
                token_id: TOKEN_ID,
                amount: TokenAmountU64(99),
                from: ALICE_ADDR,
                to: ALICE_ADDR,
            })),
            TokenEvent::CreatedUTXO(CreatedUTXOEvent {
                token_id: TOKEN_ID,
                utxo_index: 2u64,
                utxo: expected_utxo_created_bob,
                at: BOB_ADDR,
            }),
            TokenEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
                token_id: TOKEN_ID,
                amount: TokenAmountU64(1),
                from: ALICE_ADDR,
                to: BOB_ADDR,
            })),
        ]
    );
}

// /// Test that a transfer fails when the sender is neither an operator or the
// /// owner. In particular, Bob will attempt to transfer some of Alice's tokens to
// /// himself.
// #[test]
// fn test_unauthorized_sender() {
//     let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens();

//     // Construct a transfer of `TOKEN_ID_WCCD` from Alice to Bob, which will be
//     // submitted by Bob.
//     let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
//         from: ALICE_ADDR,
//         to: Receiver::Account(BOB),
//         token_id: TOKEN_ID_WCCD,
//         amount: TokenAmountU64(1),
//         data: AdditionalData::empty(),
//     }]);

//     // Notice that Bob is the sender/invoker.
//     let update = chain
//         .contract_update(
//             SIGNER,
//             BOB,
//             BOB_ADDR,
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount: Amount::zero(),
//                 receive_name: OwnedReceiveName::new_unchecked("cis2_wCCD.transfer".to_string()),
//                 address: contract_address,
//                 message: OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
//             },
//         )
//         .expect_err("Transfer tokens");

//     // Check that the correct error is returned.
//     let rv: ContractError = update
//         .parse_return_value()
//         .expect("ContractError return value");
//     assert_eq!(rv, ContractError::Unauthorized);
// }

// /// Test that an operator can make a transfer.
// #[test]
// fn test_operator_can_transfer() {
//     let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens();

//     // Add Bob as an operator for Alice.
//     let params = UpdateOperatorParams(vec![UpdateOperator {
//         update: OperatorUpdate::Add,
//         operator: BOB_ADDR,
//     }]);
//     chain
//         .contract_update(
//             SIGNER,
//             ALICE,
//             ALICE_ADDR,
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount: Amount::zero(),
//                 receive_name: OwnedReceiveName::new_unchecked(
//                     "cis2_wCCD.updateOperator".to_string(),
//                 ),
//                 address: contract_address,
//                 message: OwnedParameter::from_serial(&params).expect("UpdateOperator params"),
//             },
//         )
//         .expect("Update operator");

//     // Let Bob make a transfer to himself on behalf of Alice.
//     let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
//         from: ALICE_ADDR,
//         to: Receiver::Account(BOB),
//         token_id: TOKEN_ID_WCCD,
//         amount: TokenAmountU64(1),
//         data: AdditionalData::empty(),
//     }]);

//     chain
//         .contract_update(
//             SIGNER,
//             BOB,
//             BOB_ADDR,
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount: Amount::zero(),
//                 receive_name: OwnedReceiveName::new_unchecked("cis2_wCCD.transfer".to_string()),
//                 address: contract_address,
//                 message: OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
//             },
//         )
//         .expect("Transfer tokens");

//     // Check that Bob now has 1 wCCD and Alice has 99.
//     let balances = get_balances(&chain, contract_address);
//     assert_eq!(balances.0, [99.into(), 1.into()]);
// }

// Helpers:

/// Helper function that initializes the contract and mint 100 tokens to Alice.
fn initialize_contract_with_alice_tokens() -> (Chain, ContractAddress, ContractInvokeSuccess) {
    let (mut chain, init) = initialize_chain_and_contract();

    let wrap_params = MintParams {
        owner: Receiver::Account(ALICE),
        amount: ContractTokenAmount::from(100u64),
        data: AdditionalData::empty(),
    };

    // Mint 100 tokens to Alice.
    let update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("token.mint".to_string()),
                address: init.contract_address,
                message: OwnedParameter::from_serial(&wrap_params).expect("Mint params"),
            },
        )
        .expect("Mint tokens");
    (chain, init.contract_address, update)
}

/// Setup chain and contract.
///
/// Also creates the two accounts, Alice and Bob.
///
/// Alice is the owner of the contract.
fn initialize_chain_and_contract() -> (Chain, ContractInitSuccess) {
    let mut chain = Chain::new();

    // Create some accounts on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain
        .module_deploy_v1(SIGNER, ALICE, module)
        .expect("Deploy valid module");

    // Construct the initial parameters.
    let params = SetMetadataUrlParams {
        url: METADATA_URL.to_string(),
        hash: None,
    };

    // Initialize the auction contract.
    let init = chain
        .contract_init(
            SIGNER,
            ALICE,
            Energy::from(10000),
            InitContractPayload {
                amount: Amount::zero(),
                mod_ref: deployment.module_reference,
                init_name: OwnedContractName::new_unchecked("init_token".to_string()),
                param: OwnedParameter::from_serial(&params).expect("Init params"),
            },
        )
        .expect("Initialize contract");

    (chain, init)
}

struct AliceAndBobUTXOSets {
    alice: Vec<(u64, SpendingRestriction)>,
    bob: Vec<(u64, SpendingRestriction)>,
}

struct AliceAndBobTokenBalances {
    alice: TokenBalances,
    bob: TokenBalances,
}

/// Get the utxo sets for Alice and Bob.
fn get_utxo_sets(chain: &Chain, contract_address: ContractAddress) -> AliceAndBobUTXOSets {
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("token.view".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&ALICE_ADDR).expect("view params"),
            },
        )
        .expect("Invoke view");
    let alice_state: ViewState = invoke.parse_return_value().expect("View return value");

    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("token.view".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&BOB_ADDR).expect("view params"),
            },
        )
        .expect("Invoke view");
    let bob_state: ViewState = invoke.parse_return_value().expect("View return value");
    AliceAndBobUTXOSets {
        alice: alice_state.utxos,
        bob: bob_state.utxos,
    }
}

/// Get the balances for Alice and Bob.
fn get_balances(chain: &Chain, contract_address: ContractAddress) -> AliceAndBobTokenBalances {
    let param = ContractBalanceOfQueryParams {
        queries: vec![
            BalanceOfQuery {
                address: ALICE_ADDR,
                token_id: TOKEN_ID,
            },
            BalanceOfQuery {
                address: BOB_ADDR,
                token_id: TOKEN_ID,
            },
        ],
    };

    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("token.balanceOf".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&param).expect("BalanceOf params"),
            },
        )
        .expect("Invoke balanceOf");
    let state: Vec<TokenBalances> = invoke.parse_return_value().expect("BalanceOf return value");

    AliceAndBobTokenBalances {
        alice: state[0].clone(),
        bob: state[1].clone(),
    }
}

/// Deserialize the events from an update.
fn deserialize_update_events(update: &ContractInvokeSuccess) -> Vec<TokenEvent> {
    update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect()
}
