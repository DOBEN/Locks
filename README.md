## Prerequisites

[Cargo Concordium](https://docs.rs/crate/cargo-concordium/latest)

## Building the smart contract

```
cargo concordium build
```

## Running the tests

```
cargo concordium test --out concordium-out/module.wasm.v1
```

# Token with locking and schedule transfer features

## Schedule transfer Definition

A `schedule transfer` is the operation when Alice transfers tokens to Bob with a time lock and the following release behavior:
The balance is immediately subtracted from Alice's balance and added to Bob's balance but locked (meaning Bob has the funds
not at his disposal) until the timelock has passed.

For example: Timelock is 5 hours, amount transferred is 1 token, Alice's token balance is A, and Bob's token balance is B.

| Time                              | Block with timestamp x (including the TokenScheduleTransferTransaction) | Block with timestamp x + 5 hours |
|-----------------------------------|-------------------------------------------------------------------------|----------------------------------|
| **Alice Token Balance (at disposal)** | A - 1                                                               | A - 1                            |
| **Bob Token Balance (at disposal)** | B                                                                     | B + 1                            |
| **Bob Token Balance (locked)**    | 1                                                                       | 0                                |


## Schedule transfer Definition

A `lock` is the operation when Alice transfers tokens to Bob with a time lock and the following release behavior:
The balance is accounted for on Alice's balance but locked (meaning Alice has the funds not at her disposal) and when
the the timelock has passed the transfered token is accounted for on Bob's balance.

For example: Timelock is 5 hours, amount transferred is 1 token, Alice's token balance is A, and Bob's token balance is B.

| Time                              | Block with timestamp x (including the TokenScheduleTransferTransaction) | Block with timestamp x + 5 hours |
|-----------------------------------|-------------------------------------------------------------------------|----------------------------------|
| **Alice Token Balance (at disposal)** | A - 1                                                               | A - 1                            |
| **Alice Token Balance (locked)**      | 1                                                                   | 0                                |
| **Bob Token Balance (at disposal)**   | B                                                                   | B + 1                            |


# Motivation
Locking and schedule transfers are common financial operation and usually implemented in the web3 world via `escrow smart contracts`. E.g. Alice sends the funds to the `escrow smart contract`
and Bob withdraws the funds after the lock has passed. The funds are accounted for on the balance of the `escrow smart contracts` during the time of the lock.
This `escrow` setup has several drawbacks:
- Legal implication (licenses and registrations) for the people/business behind the `escrow smart contracts` since they are `in-control` of the users' funds (money-transferring business).
- Alice/Bob do not want yield-bearing tokens to be accounted for on an `escrow smart contracts` balance since Alice/Bob will loose revenue.
- Bob needs to send a second transaction to claim his funds from the `escrow`.

# Implemention of the time locks in the token smart contract
To avoid `escrow smart contracts`, the time locks are implemented as part of the token smart contract logic by adding the Bitcoin UTXO model
on top-of the Ethereum-style token account balance model. The token smart contract will track the locked/scheduled_transfer balances on the
account address that they are associated with. Even `smart contracts` can create `locks/schedule_transfers` with the funds on their balance.
