use std::collections::HashMap;
use std::fmt::Write;
use std::sync::Mutex;

use reqwest;
use clarity::vm::functions::principals::special_principal_construct;
use clarity::vm::types::{ASCIIData, CharType, PrincipalData, SequenceData};
use clarity::vm::Value::{Principal, Sequence};

use stacks::chainstate::stacks::db::blocks::MINIMUM_TX_FEE_RATE_PER_BYTE;
use stacks::chainstate::stacks::{
    db::blocks::MemPoolRejection, db::StacksChainState, StacksBlockHeader, StacksPrivateKey,
    StacksTransaction,
};
use stacks::chainstate::stacks::{TokenTransferMemo, TransactionContractCall, TransactionPayload};
use stacks::clarity_vm::clarity::ClarityConnection;
use stacks::codec::StacksMessageCodec;
use stacks::core::mempool::MAXIMUM_MEMPOOL_TX_CHAINING;
use stacks::core::PEER_VERSION_EPOCH_2_0;
use stacks::core::PEER_VERSION_EPOCH_2_05;
use stacks::core::PEER_VERSION_EPOCH_2_1;
use stacks::net::GetIsTraitImplementedResponse;
use stacks::net::{AccountEntryResponse, CallReadOnlyRequestBody, ContractSrcResponse};
use stacks::types::chainstate::{StacksAddress, VRFSeed};
use stacks::util::hash::Sha256Sum;
use stacks::util::hash::{hex_bytes, to_hex};
use stacks::vm::{
    analysis::{
        contract_interface_builder::{build_contract_interface, ContractInterface},
        mem_type_check,
    },
    database::ClaritySerializable,
    types::{QualifiedContractIdentifier, ResponseData, TupleData},
    Value,
};
use stacks::{burnchains::Address, vm::ClarityVersion};

use crate::config::InitialBalance;
use crate::helium::RunLoop;
use crate::tests::make_sponsored_stacks_transfer_on_testnet;
use stacks::core::StacksEpoch;
use stacks::core::StacksEpochId;
use stacks::vm::costs::ExecutionCost;
use stacks::vm::types::StacksAddressExtensions;

use stacks_common::types::chainstate::StacksBlockId;
use stacks_common::util::secp256k1::Secp256k1PrivateKey;

use super::{
    make_contract_call, make_contract_publish, make_stacks_transfer, to_addr, ADDR_4, SK_1, SK_2,
    SK_3,
};

const OTHER_CONTRACT: &'static str = "
  (define-data-var x uint u0)
  (define-public (f1)
    (ok (var-get x)))
  (define-public (f2 (val uint))
    (ok (var-set x val)))
";

const CALL_READ_CONTRACT: &'static str = "
  (define-public (public-no-write)
    (ok (contract-call? .other f1)))
  (define-public (public-write)
    (ok (contract-call? .other f2 u5)))
";

const GET_INFO_CONTRACT: &'static str = "
        (define-map block-data
          { height: uint }
          { stacks-hash: (buff 32),
            id-hash: (buff 32),
            btc-hash: (buff 32),
            vrf-seed: (buff 32),
            burn-block-time: uint,
            stacks-miner: principal })
        (define-private (test-1) (get-block-info? time u1))
        (define-private (test-2) (get-block-info? time block-height))
        (define-private (test-3) (get-block-info? time u100000))
        (define-private (test-4 (x uint)) (get-block-info? header-hash x))
        (define-private (test-5) (get-block-info? header-hash (- block-height u1)))
        (define-private (test-6) (get-block-info? burnchain-header-hash u1))
        (define-private (test-7) (get-block-info? vrf-seed u1))
        (define-private (test-8) (get-block-info? miner-address u1))
        (define-private (test-9) (get-block-info? miner-address block-height))
        (define-private (test-10) (get-block-info? miner-address u100000))
        (define-private (test-11) burn-block-height)

        (define-private (get-block-id-hash (height uint)) (unwrap-panic
          (get id-hash (map-get? block-data { height: height }))))

        ;; should always return true!
        ;;   evaluates 'block-height' at the block in question.
        ;;   NOTABLY, this would fail if the MARF couldn't figure out
        ;;    the height of the 'current chain tip'.
        (define-private (exotic-block-height (height uint))
          (is-eq (at-block (get-block-id-hash height) block-height)
                 height))
        (define-read-only (get-exotic-data-info (height uint))
          (unwrap-panic (map-get? block-data { height: height })))

        (define-read-only (get-exotic-data-info? (height uint))
          (unwrap-panic (map-get? block-data { height: height })))

        (define-private (exotic-data-checks (height uint))
          (let ((block-to-check (unwrap-panic (get-block-info? id-header-hash height)))
                (block-info (unwrap-panic (map-get? block-data { height: (- height u1) }))))
            (and (is-eq (print (unwrap-panic (at-block block-to-check (get-block-info? id-header-hash (- block-height u1)))))
                        (print (get id-hash block-info)))
                 (is-eq (print (unwrap-panic (at-block block-to-check (get-block-info? header-hash (- block-height u1)))))
                        (print (unwrap-panic (get-block-info? header-hash (- height u1))))
                        (print (get stacks-hash block-info)))
                 (is-eq (print (unwrap-panic (at-block block-to-check (get-block-info? vrf-seed (- block-height u1)))))
                        (print (unwrap-panic (get-block-info? vrf-seed (- height u1))))
                        (print (get vrf-seed block-info)))
                 (is-eq (print (unwrap-panic (at-block block-to-check (get-block-info? burnchain-header-hash (- block-height u1)))))
                        (print (unwrap-panic (get-block-info? burnchain-header-hash (- height u1))))
                        (print (get btc-hash block-info)))
                 (is-eq (print (unwrap-panic (at-block block-to-check (get-block-info? time (- block-height u1)))))
                        (print (unwrap-panic (get-block-info? time (- height u1))))
                        (print (get burn-block-time block-info)))
                 (is-eq (print (unwrap-panic (at-block block-to-check (get-block-info? miner-address (- block-height u1)))))
                        (print (unwrap-panic (get-block-info? miner-address (- height u1))))
                        (print (get stacks-miner block-info))))))

        (define-private (inner-update-info (height uint))
            (let ((value (tuple
              (stacks-hash (unwrap-panic (get-block-info? header-hash height)))
              (id-hash (unwrap-panic (get-block-info? id-header-hash height)))
              (btc-hash (unwrap-panic (get-block-info? burnchain-header-hash height)))
              (vrf-seed (unwrap-panic (get-block-info? vrf-seed height)))
              (burn-block-time (unwrap-panic (get-block-info? time height)))
              (stacks-miner (unwrap-panic (get-block-info? miner-address height))))))
             (ok (map-set block-data { height: height } value))))

        (define-public (update-info)
          (begin
            (unwrap-panic (inner-update-info (- block-height u2)))
            (inner-update-info (- block-height u1))))

        (define-trait trait-1 (
            (foo-exec (int) (response int int))))

        (define-trait trait-2 (
            (get-1 (uint) (response uint uint))
            (get-2 (uint) (response uint uint))))

        (define-trait trait-3 (
            (fn-1 (uint) (response uint uint))
            (fn-2 (uint) (response uint uint))))
       ";

const IMPL_TRAIT_CONTRACT: &'static str = "
        ;; explicit trait compliance for trait 1
        (impl-trait .get-info.trait-1)
        (define-private (test-height) burn-block-height)
        (define-public (foo-exec (a int)) (ok 1))

        ;; implicit trait compliance for trait-2
        (define-public (get-1 (x uint)) (ok u1))
        (define-public (get-2 (x uint)) (ok u1))

        ;; invalid trait compliance for trait-3
        (define-public (fn-1 (x uint)) (ok u1))
       ";

const MINING_POOL_CONTRACT: &'static str = r###"
;; (use-trait return-map-1 .map-trait-1.return-map-1)

(define-constant err-invalid (err u300))
(define-constant err-list-length-exceeded (err u101))
(define-constant err-already-asked-to-join (err u102))
(define-constant err-already-joined (err u103))
(define-constant err-not-in-miner-map (err u104))
(define-constant err-no-vote-permission (err u105))
(define-constant err-more-blocks-to-pass (err u106))
(define-constant err-no-pending-miners (err u107))
(define-constant err-already-voted (err u108))
(define-constant err-not-asked-to-join (err u109))
(define-constant err-cant-unwrap-check-miner (err u110))
(define-constant err-cant-unwrap-asked-to-join (err u111))
(define-constant err-cant-unwrap-block-info (err u112))
(define-constant err-currently-notifier (err u113))
(define-constant err-not-in-miner-map-miner-to-remove (err u114))
(define-constant err-already-proposed-for-removal (err u116))
(define-constant err-not-proposed-for-removal (err u117))
(define-constant err-cant-remove-when-alone-in-pool (err u118))
(define-constant err-cant-vote-himself (err u119))
(define-constant err-cant-change-notifier (err u120))
(define-constant err-already-proposed-for-notifier (err u121))
(define-constant err-not-proposed-for-removal-k-missing (err u122))
(define-constant err-not-proposed-for-notifier-k-missing (err u123))
(define-constant err-not-proposed-notifier (err u124))
(define-constant err-already-notifier (err u125))
(define-constant err-not-in-miner-map-proposed-notifier (err u126))
(define-constant err-vote-started-already (err u127))
(define-constant err-voting-still-active (err u128))
(define-constant err-not-voting-period (err u129))
(define-constant err-not-waiting (err u130))
(define-constant err-not-pending (err u131))
(define-constant err-no-join-block-data (err u132))
(define-constant err-not-voted (err u133))
(define-constant err-only-notifier (err u134))
(define-constant err-one-warning-per-block (err u135))
(define-constant err-block-height-invalid (err u136))
(define-constant err-unwrap-miner-index (err u999))
(define-constant err-insufficient-balance (err u1001))
(define-constant err-missing-balance (err u1002))
(define-constant err-already-distributed (err u1003))
(define-constant err-cant-unwrap-rewarded-block (err u1004))

(define-constant notifier-election-blocks-to-pass u30)
(define-constant blocks-to-pass u5)

(define-map balance principal uint)
(define-map claimed-rewards { block-number: uint } { claimed: bool })
(define-map add-lists-principal { address: principal } { values: (list 300 principal) })
(define-map map-is-miner { address: principal } { value: bool })
(define-map map-is-waiting { address: principal } { value: bool })
(define-map map-is-pending { address: principal } { value: bool })
(define-map map-is-proposed-for-removal { address: principal } { value: bool })
(define-map map-block-asked-to-join { address: principal } { value: uint })
(define-map map-block-proposed-to-remove { address: principal } { value: uint })
(define-map map-block-joined { address: principal } { block-height: uint })
(define-map map-balance-stx { address: principal } { value: uint })
(define-map map-balance-xBTC { address: principal } { value: uint })
(define-map auto-exchange { address: principal } { value: bool })
(define-map btc-address { address: principal } { btc-address: (string-ascii 40) })

(define-map map-votes-accept-join { address: principal } { value: uint })
(define-map map-votes-reject-join { address: principal } { value: uint })
(define-map map-votes-accept-removal { address: principal } { value: uint })
(define-map map-votes-reject-removal { address: principal } { value: uint })
(define-map map-join-request-voter { miner-to-vote: principal, voter: principal } { value: bool })
(define-map map-remove-request-voter { miner-to-vote: principal, voter: principal } { value: bool })
(define-map map-voted-update-notifier { miner-who-voted: principal } { miner-voted: principal })
(define-map map-votes-notifier { voted-notifier: principal } { votes-number: uint })
(define-map map-blacklist { address: principal } { value: bool })
(define-map map-total-withdraw { address: principal } { value: uint })
(define-map map-warnings { address: principal } { value: uint })

(define-data-var miners-list-len-at-reward-block uint u0)
(define-data-var notifier principal tx-sender)
(define-data-var waiting-list (list 300 principal) (list ))
(define-data-var miners-list (list 300 principal) (list (var-get notifier)))
(define-data-var pending-accept-list (list 300 principal) (list ))
(define-data-var proposed-removal-list (list 300 principal) (list ))
(define-data-var n uint u1)
(define-data-var k-percentage uint u67)
(define-data-var k uint u0)
(define-data-var k-critical uint u75)
(define-data-var waiting-list-miner-to-remove principal tx-sender) ;; use in remove-principal-miners-list
(define-data-var pending-accept-list-miner-to-remove principal tx-sender)
(define-data-var miners-list-miner-to-remove principal tx-sender)
(define-data-var proposed-removal-list-miner-to-remove principal tx-sender)
(define-data-var last-join-done uint u1)
(define-data-var miner-to-remove-votes-join principal tx-sender)
(define-data-var miner-to-remove-votes-remove principal tx-sender)
(define-data-var notifier-previous-entries-removed bool true)
(define-data-var notifier-vote-active bool false)
(define-data-var notifier-vote-start-block uint u0)
(define-data-var notifier-vote-end-block uint u0)
(define-data-var max-votes-notifier uint u0)
(define-data-var max-voted-proposed-notifier principal tx-sender)
(define-data-var reward uint u0)
(define-data-var total-rewarded uint u0)
(define-data-var blocks-won uint u0)


(map-set map-is-miner {address: tx-sender} {value: true})
(map-set map-block-asked-to-join {address: tx-sender} {value: u0})
(map-set balance tx-sender u0)
;; at new join -> block height - last-join-done >= 100 !

;; READ ONLY FE UTILS

;; waiting miners

(define-read-only (get-all-data-waiting-miners (waiting-miners-list (list 100 principal)))
(map get-data-waiting-miner waiting-miners-list))

(define-private (get-data-waiting-miner (miner principal))
(begin
  (asserts! (is-some (get value (map-get? map-is-waiting {address: miner}))) err-not-waiting)
  (ok
    {
      miner: miner,
      positive-votes:
        (if
          (is-some (get value (map-get? map-votes-accept-join {address: miner})))
          (unwrap-panic (get value (map-get? map-votes-accept-join {address: miner})))
          u0),
      negative-votes:
        (if
          (is-some (get value (map-get? map-votes-reject-join {address: miner})))
          (unwrap-panic (get value (map-get? map-votes-reject-join {address: miner})))
          u0),
      positive-threshold:
        (if
          (is-eq (unwrap-panic (get-k-at-block-asked-to-join miner)) u0)
          u1
          (unwrap-panic (get-k-at-block-asked-to-join miner))),
      negative-threshold:
        (if
          (is-eq (unwrap-panic (get-n-at-block-asked-to-join miner)) u1)
          u1
          (if
            (is-eq (unwrap-panic (get-n-at-block-asked-to-join miner)) u2)
            u2
            (+ (- (unwrap-panic (get-n-at-block-asked-to-join miner)) (unwrap-panic (get-k-at-block-asked-to-join miner))) u1))),
      was-blacklist: (if (is-some (get value (map-get? map-blacklist {address: miner}))) (unwrap-panic (get value (map-get? map-blacklist {address: miner}))) false)
    })))

;; proposed for removal miners

(define-read-only (get-all-data-miners-proposed-for-removal (removal-miners-list (list 100 principal)))
(map get-data-miner-proposed-for-removal removal-miners-list))

(define-private (get-data-miner-proposed-for-removal (miner principal))
(begin
  (asserts! (is-some (get value (map-get? map-is-proposed-for-removal {address: miner}))) err-not-pending)
  (ok
    {
      miner: miner,
      votes-for-removal:
        (if
          (is-some (get value (map-get? map-votes-accept-removal {address: miner})))
          (unwrap-panic (get value (map-get? map-votes-accept-removal {address: miner})))
          u0),
      votes-against-removal:
        (if
          (is-some (get value (map-get? map-votes-reject-removal {address: miner})))
          (unwrap-panic (get value (map-get? map-votes-reject-removal {address: miner})))
          u0),
      positive-threshold:
        (if
          (is-eq (unwrap-panic (get-k-at-block-proposed-removal miner)) u0)
          u1
          (unwrap-panic (get-k-at-block-proposed-removal miner))),
      negative-threshold:
        (if
          (is-eq (unwrap-panic (get-n-at-block-proposed-removal miner)) u2)
          u1
          (if (is-eq (unwrap-panic (get-n-at-block-proposed-removal miner)) u3)
            u2
            (+ (- (unwrap-panic (get-n-at-block-proposed-removal miner)) (unwrap-panic (get-k-at-block-proposed-removal miner))) u1)))
    })))

;; pending accept miners

(define-read-only (get-all-data-miners-pending-accept (pending-miners-list (list 100 principal)))
(map get-data-miner-pending-accept pending-miners-list))

(define-private (get-data-miner-pending-accept (miner principal))
(begin
  (asserts! (is-some (get value (map-get? map-is-pending {address: miner}))) err-not-pending)
  (ok
    {
      miner: miner,
      remaining-blocks-until-join: (get-remaining-blocks-until-join)
    })))

(define-read-only (get-remaining-blocks-until-join)
  (if (> blocks-to-pass (- block-height (var-get last-join-done)))
    (- blocks-to-pass (- block-height (var-get last-join-done)))
    u0
  )
)

;; blocks number as miner
(define-read-only (get-all-data-miners-blocks (local-miners-list (list 100 principal)))
(map get-data-miner-blocks local-miners-list))
(define-private (get-data-miner-blocks (miner principal))
(begin
  (asserts! (is-some (get value (map-get? map-is-miner {address: miner}))) err-not-in-miner-map)
  (asserts! (is-some (get block-height (map-get? map-block-joined {address: miner}))) err-no-join-block-data)
  (ok
    {
      miner: miner,
      blocks-as-miner: (- block-height (unwrap-panic (get block-height (map-get? map-block-joined {address: miner}))))
    })))

;; miners in pool

(define-read-only (get-all-data-miners-in-pool (local-miners-list (list 100 principal)))
(map get-data-miner-in-pool local-miners-list))

(define-private (get-data-miner-in-pool (miner principal))
(begin
  (asserts! (is-some (get value (map-get? map-is-miner {address: miner}))) err-not-in-miner-map)
  (asserts! (is-some (get block-height (map-get? map-block-joined {address: miner}))) err-no-join-block-data)
  (ok
    {
      miner: miner,
      blocks-as-miner: (- block-height (unwrap-panic (get block-height (map-get? map-block-joined {address: miner})))),
      was-blacklist: (if (is-some (get value (map-get? map-blacklist {address: miner}))) (unwrap-panic (get value (map-get? map-blacklist {address: miner}))) false),
      warnings: (if (is-some (get value (map-get? map-warnings {address: miner}))) (unwrap-panic (get value (map-get? map-warnings {address: miner}))) u0),
      balance: (if (is-some (get value (map-get? map-balance-stx {address: miner}))) (unwrap-panic (get value (map-get? map-balance-stx {address: miner}))) u0),
      total-withdrawals: (if (is-some (get value (map-get? map-total-withdraw {address: miner}))) (unwrap-panic (get value (map-get? map-total-withdraw {address: miner}))) u0)
    })))

;; notifier

(define-read-only (get-data-notifier-election-process)
{
  vote-status: (var-get notifier-vote-active),
  election-blocks-remaining:
    (if (<= (var-get notifier-vote-end-block) block-height)
    u0
    (- (var-get notifier-vote-end-block) block-height))})

(define-read-only (get-all-data-notifier-voter-miners (voter-miners-list (list 100 principal)))
(map get-data-notifier-voter-miner voter-miners-list))

(define-private (get-data-notifier-voter-miner (miner principal))
(begin
  (asserts! (is-some (get miner-voted (map-get? map-voted-update-notifier {miner-who-voted: miner}))) err-not-voted)
  (ok
    {
      miner: miner,
      voted-notifier:
      (unwrap-panic (get miner-voted (map-get? map-voted-update-notifier {miner-who-voted: miner})))
    })))

;; balances

(define-read-only (was-block-claimed (given-block-height uint))
  (if
    (is-none (get claimed (map-get? claimed-rewards {block-number: given-block-height})))
    false
    (if
      (unwrap-panic (get claimed (map-get? claimed-rewards {block-number: given-block-height})))
      true
      false)))

(define-read-only (get-all-data-balance-miners (local-miners-list (list 100 principal)))
(map get-data-balance-miner local-miners-list))

(define-private (get-data-balance-miner (miner principal))
(begin
  (asserts! (is-some (get value (map-get? map-is-miner {address: miner}))) err-not-in-miner-map)
  (ok
    {
      miner: miner,
      balance:
        (if
          (is-some (get value (map-get? map-balance-stx {address: miner})))
          (unwrap-panic (get value (map-get? map-balance-stx {address: miner})))
          u0)
    })))

;; BALANCES FLOW

;; read balance
(define-read-only (get-balance (address principal))
(map-get? balance address))

(define-read-only (get-miner-btc-address (miner-address principal))
  (map-get? btc-address {address: miner-address}))

(define-public (set-my-btc-address (new-btc-address  (string-ascii 40)))
  (ok (map-set btc-address {address: tx-sender} {btc-address: new-btc-address})))

;; deposit funds
(define-public (deposit-stx (amount uint))
(let ((sender tx-sender)
      (balance-sender (map-get? balance sender)))
  (try! (stx-transfer? amount tx-sender (as-contract tx-sender)))
  (if (is-none balance-sender)
    (ok (map-set balance sender amount))
    (ok (map-set balance sender (+ (unwrap! balance-sender err-missing-balance) amount))))))

;; withdraw funds
(define-public (withdraw-stx (amount uint))
(let ((receiver tx-sender))
  (asserts! (>= (unwrap! (map-get? balance receiver) err-missing-balance) amount) err-insufficient-balance)
  (try! (as-contract (stx-transfer? amount (as-contract tx-sender) receiver)))
  (if
    (is-some (get value (map-get? map-total-withdraw {address: receiver})))
    (map-set map-total-withdraw {address: receiver} {value: (+ (unwrap-panic (get value (map-get? map-total-withdraw {address: receiver}))) amount)})
    (map-set map-total-withdraw {address: receiver} {value: amount}))
  (ok (map-set balance receiver (- (unwrap! (map-get? balance receiver) err-missing-balance) amount)))))

;; exchange funds
(define-public (set-auto-exchange (new-value bool))
  (ok (map-set auto-exchange {address: tx-sender} {value: new-value})))

(define-read-only (get-auto-exchange (address principal))
  (map-get? auto-exchange {address: address}))

(define-public (reward-distribution (block-number uint))
(begin
  (asserts! (< block-number block-height) err-block-height-invalid) ;; +100  ?
  (asserts! (is-none (get claimed (map-get? claimed-rewards {block-number: block-number}))) err-already-distributed)
  (let ((miners-list-at-reward-block
          (if
            (is-eq block-number block-height)
            (var-get miners-list)
            (at-block (unwrap! (get-block-info? id-header-hash block-number) err-cant-unwrap-rewarded-block) (var-get miners-list))))
        (block-reward (get-reward-at-block block-number)))
    ;; (asserts! (is-eq (unwrap-panic (get claimer block-reward)) (as-contract tx-sender)) err-not-claimer)
    (map-set claimed-rewards {block-number: block-number} {claimed: true})
    (var-set miners-list-len-at-reward-block (len miners-list-at-reward-block))
    (var-set reward (unwrap-panic (get reward block-reward)))
    (var-set total-rewarded (+ (var-get total-rewarded) (var-get reward)))
    (var-set blocks-won (+ (var-get blocks-won) u1))
    (map distribute-reward-each-miner miners-list-at-reward-block)
    (ok true))))

(define-private (distribute-reward-each-miner (miner principal))
(map-set balance miner (+ (unwrap-panic (map-get? balance miner)) (/ (var-get reward) (var-get miners-list-len-at-reward-block)))))

;; JOINING FLOW

(define-public (ask-to-join (my-btc-address (string-ascii 40)))
(begin
  (asserts! (not (check-is-miner-now tx-sender)) err-already-joined)
  (asserts! (not (check-is-waiting-now tx-sender)) err-already-asked-to-join)
  (map-set map-block-asked-to-join {address: tx-sender} {value: block-height})
  (map-set btc-address {address: tx-sender} {btc-address: my-btc-address})
  (var-set waiting-list (unwrap-panic (as-max-len? (concat (var-get waiting-list) (list tx-sender)) u300)))
  (map-set map-is-waiting {address: tx-sender} {value: true})
  (ok true)))

(define-public (vote-positive-join-request (miner-to-vote principal))
(begin
  (asserts! (check-is-waiting-now miner-to-vote) err-not-asked-to-join) ;; map_is_waiting
    (asserts! (unwrap! (check-is-miner-when-requested-join miner-to-vote) err-cant-unwrap-check-miner) err-no-vote-permission)
    (asserts! (has-voted-join miner-to-vote) err-already-voted) ;; O(1)
    (map-set map-join-request-voter
      {miner-to-vote: miner-to-vote, voter: tx-sender}
      {value: true})
    (if (is-some (get value (map-get? map-votes-accept-join {address: miner-to-vote})))
      (map-set map-votes-accept-join {address: miner-to-vote} {value: (+ (unwrap-panic (get value (map-get? map-votes-accept-join {address: miner-to-vote}))) u1)})
      (map-set map-votes-accept-join {address: miner-to-vote} {value: u1}))
    (ok true)))

(define-public (vote-negative-join-request (miner-to-vote principal))
(begin
  (asserts! (check-is-waiting-now miner-to-vote) err-not-asked-to-join)
    (asserts! (unwrap! (check-is-miner-when-requested-join miner-to-vote) err-cant-unwrap-check-miner) err-no-vote-permission)
    (asserts! (has-voted-join miner-to-vote) err-already-voted)
    (map-set map-join-request-voter
      {miner-to-vote: miner-to-vote, voter: tx-sender}
      {value: true})
    (if (is-some (get value (map-get? map-votes-reject-join {address: miner-to-vote})))
      (map-set map-votes-reject-join {address: miner-to-vote} {value: (+ (unwrap-panic (get value (map-get? map-votes-reject-join {address: miner-to-vote}))) u1)})
      (map-set map-votes-reject-join {address: miner-to-vote} {value: u1}))
    (some
      (if (is-vote-rejected-join (unwrap-panic (get value (map-get? map-votes-reject-join {address: miner-to-vote}))) (unwrap-panic (get-k-at-block-asked-to-join miner-to-vote)) (unwrap-panic (get-n-at-block-asked-to-join miner-to-vote)))
        (reject-miner-in-pool miner-to-vote)
        false))
    (ok true)))

(define-private (accept-miner-in-pool (miner principal))
(begin
  (let ((pending-accept-result (as-max-len? (concat (var-get pending-accept-list) (list miner)) u300)))
  (asserts! (is-some pending-accept-result) err-list-length-exceeded) ;; O(1)
  (map-set map-warnings {address: miner} {value: u0})
  (map-set balance miner u0)
  (var-set miner-to-remove-votes-join miner)
  (var-set waiting-list (unwrap-panic (as-max-len? (unwrap-panic (remove-principal-waiting-list miner)) u300))) ;; O(N)
  (map-delete map-is-waiting {address: miner})
  (map-set map-is-pending {address: miner} {value: true})
  (clear-votes-map-join-vote miner)
  (ok (var-set pending-accept-list (unwrap-panic pending-accept-result))))))

(define-private (reject-miner-in-pool (miner principal))
(begin
  (let ((remove-result (unwrap-panic (remove-principal-waiting-list miner))))
    (var-set miner-to-remove-votes-join miner)
    (var-set waiting-list remove-result)
    (map-delete map-is-waiting {address: miner})
    (clear-votes-map-join-vote miner)
    true)))

(define-private (clear-votes-map-join-vote (miner principal))
(begin
  (map-delete map-votes-accept-join {address: (var-get miner-to-remove-votes-join)})
  (map-delete map-votes-reject-join {address: (var-get miner-to-remove-votes-join)})
  (map-delete map-block-asked-to-join {address: (var-get miner-to-remove-votes-join)})
  (map remove-map-record-join-vote (var-get miners-list))))

(define-private (remove-map-record-join-vote (miner principal))
(if (is-some (map-get? map-join-request-voter {miner-to-vote: (var-get miner-to-remove-votes-join), voter: miner}))
  (map-delete map-join-request-voter {miner-to-vote: (var-get miner-to-remove-votes-join), voter: miner})
  false))

(define-private (is-in-voters-list (miner principal) (voters-list (list 300 principal)))
(is-some (index-of? voters-list miner)))

(define-private (has-voted-join (miner principal))
(not (if (is-some (get value (map-get? map-join-request-voter {miner-to-vote: miner, voter: tx-sender})))
          (unwrap-panic (get value (map-get? map-join-request-voter {miner-to-vote: miner, voter: tx-sender})))
          false)))

(define-public (try-enter-pool)
(begin
  (asserts! (is-some (get value (map-get? map-votes-accept-join {address: tx-sender}))) err-not-asked-to-join)
  (if (is-vote-accepted (unwrap-panic (get value (map-get? map-votes-accept-join {address: tx-sender}))) (unwrap-panic (get-k-at-block-asked-to-join tx-sender)))
    (accept-miner-in-pool tx-sender)
    (ok false))))

(define-public (add-pending-miners-to-pool)
(begin
  (let ((len-pending-accept-list (len (var-get pending-accept-list))))
    (asserts! (not (is-eq len-pending-accept-list u0)) err-no-pending-miners)
    (asserts! (x-blocks-passed blocks-to-pass) err-more-blocks-to-pass)
    (map add-miner-to-pool (var-get pending-accept-list))
    (asserts! (is-some (as-max-len? (concat (var-get miners-list) (var-get pending-accept-list)) u300)) err-list-length-exceeded)
    (var-set miners-list (unwrap-panic (as-max-len? (concat (var-get miners-list) (var-get pending-accept-list)) u300)))
    (var-set n (+ (var-get n) len-pending-accept-list))
    (var-set pending-accept-list (list ))
    (var-set last-join-done block-height)
    (some (update-threshold))
    (ok true))))

(define-private (update-threshold)
(var-set k (/ (* (var-get k-percentage) (- (var-get n) u1)) u100)))

(define-private (add-miner-to-pool (miner principal))
(begin
  (map-delete map-is-pending {address: miner})
  (map-set map-is-miner {address: miner} {value: true})
  (map-set map-block-joined {address: miner} {block-height: block-height})
  (ok true)))

(define-private (x-blocks-passed (x uint))
(if (>= (- block-height (var-get last-join-done)) x)
  true
  false))

(define-private (get-k-at-block-asked-to-join (miner-to-vote principal))
(begin
  (asserts! (is-some (get value (map-get? map-block-asked-to-join {address: miner-to-vote}))) err-not-asked-to-join)
  (if
    (is-eq
      (unwrap-panic (get value (map-get? map-block-asked-to-join {address: miner-to-vote})))
      block-height)
    (ok (var-get k))
    (at-block
    (unwrap-panic
      (get-block-info? id-header-hash
        (unwrap-panic
          (get value
            (map-get? map-block-asked-to-join {address: miner-to-vote})))))
            (ok (var-get k))))))

(define-private (get-n-at-block-asked-to-join (miner-to-vote principal))
(begin
  (asserts! (is-some (get value (map-get? map-block-asked-to-join {address: miner-to-vote}))) err-not-asked-to-join)
  (if
    (is-eq
      (unwrap-panic (get value (map-get? map-block-asked-to-join {address: miner-to-vote}))) block-height)
    (ok (var-get n))
    (at-block
    (unwrap-panic
      (get-block-info? id-header-hash
        (unwrap-panic
          (get value
            (map-get? map-block-asked-to-join {address: miner-to-vote})))))
            (ok (var-get n))))))

;; LEAVING FLOW

(define-public (leave-pool)
(begin
  (asserts! (check-is-miner-now tx-sender) err-not-in-miner-map)
  (asserts! (not (is-eq (var-get notifier) tx-sender)) err-currently-notifier)
  (let ((remove-result (unwrap-panic (remove-principal-miners-list tx-sender)))
        (new-k-percentage (/ (* (var-get k) u100) (- (var-get n) u2))))
    (some (var-set miners-list remove-result))
    (var-set n (- (var-get n) u1))
    (map-set map-is-miner {address: tx-sender} {value: false})
    (if (>= new-k-percentage (var-get k-critical))
      (some (update-threshold))
      none)
    (ok true))))

;; REMOVING FLOW

(define-public (propose-removal (miner-to-remove principal))
(begin
  (asserts! (not (is-eq (var-get n) u1)) err-cant-remove-when-alone-in-pool)
  (asserts! (check-is-miner-now tx-sender) err-not-in-miner-map)
  (asserts! (check-is-miner-now miner-to-remove) err-not-in-miner-map-miner-to-remove)
  (asserts! (not (check-is-proposed-for-removal-now miner-to-remove)) err-already-proposed-for-removal)
  (map-set map-block-proposed-to-remove {address: miner-to-remove} {value: block-height})
  (map-set map-is-proposed-for-removal {address: miner-to-remove} {value: true})
  (var-set proposed-removal-list (unwrap! (as-max-len? (concat (var-get proposed-removal-list) (list miner-to-remove )) u300) err-list-length-exceeded))
  (ok true)))

(define-public (vote-positive-remove-request (miner-to-vote principal))
(begin
  (asserts! (not (is-eq tx-sender miner-to-vote)) err-cant-vote-himself)
  (asserts! (check-is-proposed-for-removal-now miner-to-vote) err-not-proposed-for-removal) ;; map_is_proposed_for_removal
  (asserts! (is-ok (get-k-at-block-proposed-removal miner-to-vote)) err-not-proposed-for-removal-k-missing)
    (asserts! (unwrap! (check-is-miner-when-requested-remove miner-to-vote) err-cant-unwrap-check-miner) err-no-vote-permission)
    (asserts! (has-voted-remove miner-to-vote) err-already-voted) ;; O(1)
    (map-set map-remove-request-voter
      {miner-to-vote: miner-to-vote, voter: tx-sender}
      {value: true})
    (if (is-some (get value (map-get? map-votes-accept-removal {address: miner-to-vote})))
      (map-set map-votes-accept-removal {address: miner-to-vote} {value: (+ (unwrap-panic (get value (map-get? map-votes-accept-removal  {address: miner-to-vote}))) u1)})
      (map-set map-votes-accept-removal {address: miner-to-vote} {value: u1}))
    (some
      (if (is-vote-accepted (unwrap-panic (get value (map-get? map-votes-accept-removal {address: miner-to-vote}))) (unwrap-panic (get-k-at-block-proposed-removal miner-to-vote)))
        (process-removal miner-to-vote)
        (ok false)))
    (ok true)))

(define-public (vote-negative-remove-request (miner-to-vote principal))
(begin
  (asserts! (not (is-eq tx-sender miner-to-vote)) err-cant-vote-himself)
  (asserts! (check-is-proposed-for-removal-now miner-to-vote) err-not-proposed-for-removal) ;; map_is_waiting
  (asserts! (is-ok (get-k-at-block-proposed-removal miner-to-vote)) err-not-proposed-for-removal-k-missing)
  (asserts! (unwrap! (check-is-miner-when-requested-remove miner-to-vote) err-cant-unwrap-check-miner) err-no-vote-permission)
  (asserts! (has-voted-remove miner-to-vote) err-already-voted) ;; O(1)
  (map-set map-remove-request-voter
    {miner-to-vote: miner-to-vote, voter: tx-sender}
    {value: true})
  (if (is-some (get value (map-get? map-votes-reject-removal {address: miner-to-vote})))
    (map-set map-votes-reject-removal {address: miner-to-vote} {value: (+ (unwrap-panic (get value (map-get? map-votes-reject-removal {address: miner-to-vote}))) u1)})
    (map-set map-votes-reject-removal {address: miner-to-vote} {value: u1}))
  (some
    (if (is-vote-rejected-remove (unwrap-panic (get value (map-get? map-votes-reject-removal {address: miner-to-vote}))) (unwrap-panic (get-k-at-block-proposed-removal miner-to-vote)) (unwrap-panic (get-n-at-block-proposed-removal miner-to-vote)))
      (reject-removal miner-to-vote)
      (ok false)))
  (ok true)))

(define-private (process-removal (miner principal))
(begin
  (let ((remove-result (unwrap-panic (remove-principal-miners-list miner)))
        (new-k-percentage (/ (* (var-get k) u100) (- (var-get n) u2))))
    (some (var-set miners-list remove-result))
    (var-set miner-to-remove-votes-remove miner)
    (var-set n (- (var-get n) u1))
    (map-delete map-is-miner {address: miner})
    (map-set map-blacklist {address: miner} {value: true})
    (unwrap! (remove-principal-proposed-removal-list miner) err-list-length-exceeded)
    (clear-votes-map-remove-vote miner)
    (if (>= new-k-percentage (var-get k-critical))
      (update-threshold)
      false)
    (ok true))))

(define-private (reject-removal (miner principal))
(begin
  (var-set miner-to-remove-votes-remove miner)
  (unwrap! (remove-principal-proposed-removal-list miner) err-list-length-exceeded)
  (clear-votes-map-remove-vote miner)
  (ok true)))

(define-private (has-voted-remove (miner principal))
(not (if (is-some (get value (map-get? map-remove-request-voter {miner-to-vote: miner, voter: tx-sender})))
          (unwrap-panic (get value (map-get? map-remove-request-voter {miner-to-vote: miner, voter: tx-sender})))
          false
  )))

(define-private (clear-votes-map-remove-vote (miner principal))
(begin
  (map-delete map-votes-accept-removal {address: (var-get miner-to-remove-votes-remove)})
  (map-delete map-votes-reject-removal {address: (var-get miner-to-remove-votes-remove)})
  (map-delete map-block-proposed-to-remove {address: (var-get miner-to-remove-votes-remove)})
  (map-delete map-is-proposed-for-removal {address: (var-get miner-to-remove-votes-remove)})
  (map remove-map-record-remove-vote (var-get miners-list))))

(define-private (remove-map-record-remove-vote (miner principal))
(if (is-some (map-get? map-remove-request-voter {miner-to-vote: (var-get miner-to-remove-votes-remove), voter: miner}))
  (map-delete map-remove-request-voter {miner-to-vote: (var-get miner-to-remove-votes-remove), voter: miner})
  false))

(define-private (get-k-at-block-proposed-removal (miner-to-vote principal))
(begin
  (asserts! (is-some (get value (map-get? map-block-proposed-to-remove {address: miner-to-vote}))) err-not-proposed-for-removal)
  (if
    (is-eq (unwrap-panic
      (get value (map-get? map-block-proposed-to-remove {address: miner-to-vote})))
      block-height)
    (ok (var-get k))
    (at-block
      (unwrap-panic
        (get-block-info? id-header-hash
          (unwrap-panic
            (get value
              (map-get? map-block-proposed-to-remove {address: miner-to-vote})))))
              (ok (var-get k))))))

(define-private (get-n-at-block-proposed-removal (miner-to-vote principal))
(begin
  (asserts! (is-some (get value (map-get? map-block-proposed-to-remove {address: miner-to-vote}))) err-not-proposed-for-removal)
  (if
    (is-eq (unwrap-panic
      (get value (map-get? map-block-proposed-to-remove {address: miner-to-vote})))
      block-height)
    (ok (var-get n))
    (at-block
      (unwrap-panic
        (get-block-info? id-header-hash
          (unwrap-panic
            (get value
              (map-get? map-block-proposed-to-remove {address: miner-to-vote})))))
              (ok (var-get n))))))

;; UPDATE NOTIFIER

(define-public (start-vote-notifier)
(begin
  (asserts! (not (var-get notifier-vote-active)) err-vote-started-already)
  (var-set notifier-vote-start-block block-height)
  (var-set notifier-vote-end-block (+ (var-get notifier-vote-start-block) notifier-election-blocks-to-pass))
  (var-set notifier-vote-active true)
  (if (var-get notifier-previous-entries-removed)
      (begin
        (ok (var-set notifier-previous-entries-removed false)))
      (end-vote-notifier))))

(define-public (end-vote-notifier)
(begin
  (asserts! (>= block-height (var-get notifier-vote-end-block)) err-voting-still-active)
  (get-max-votes-number-notifier)
  (if (> (var-get max-votes-notifier) (/ (var-get k) u2))
    (var-set notifier (var-get max-voted-proposed-notifier))
    false)
  (delete-all-notifier-entries)
  (var-set notifier-vote-active false)
  (ok true)))

(define-private (get-max-votes-number-notifier)
(map compare-votes-number-notifier (var-get miners-list)))

(define-private (compare-votes-number-notifier (proposed-notifier principal))
(if (is-some (get votes-number (map-get? map-votes-notifier {voted-notifier: proposed-notifier})))
(if (> (unwrap-panic (get votes-number (map-get? map-votes-notifier {voted-notifier: proposed-notifier}))) (var-get max-votes-notifier))
  (begin
    (var-set max-votes-notifier (unwrap-panic (get votes-number (map-get? map-votes-notifier {voted-notifier: proposed-notifier}))))
    (var-set max-voted-proposed-notifier proposed-notifier))
  (if (is-eq (unwrap-panic (get votes-number (map-get? map-votes-notifier {voted-notifier: proposed-notifier}))) (var-get max-votes-notifier))
    (if
      (<
        (unwrap-panic (get block-height (map-get? map-block-joined {address: proposed-notifier})))
        (unwrap-panic (get block-height (map-get? map-block-joined {address: (var-get max-voted-proposed-notifier)}))))
      (begin
          (var-set max-voted-proposed-notifier proposed-notifier))
      false)
  false))
  false))

(define-private (delete-all-notifier-entries)
(begin
  (var-set max-votes-notifier u0)
  (var-set max-voted-proposed-notifier (var-get notifier))
  (map delete-one-notifier-entry (var-get miners-list))
  (var-set notifier-previous-entries-removed true)))

(define-private (delete-one-notifier-entry (miner principal))
(begin
  (map-delete map-voted-update-notifier {miner-who-voted: miner})
  (map-delete map-votes-notifier {voted-notifier: miner})))

(define-public (vote-notifier (voted-notifier principal))
(begin
  (asserts! (and (is-some (get value (map-get? map-is-miner {address: voted-notifier}))) (unwrap-panic (get value (map-get? map-is-miner {address: voted-notifier})))) err-not-in-miner-map)
  (asserts! (and (is-some (get value (map-get? map-is-miner {address: tx-sender}))) (unwrap-panic (get value (map-get? map-is-miner {address: tx-sender})))) err-no-vote-permission)
  (asserts! (var-get notifier-vote-active) err-not-voting-period)
  (asserts! (not (is-eq tx-sender voted-notifier)) err-cant-vote-himself)
  (asserts! (< block-height (var-get notifier-vote-end-block)) err-not-voting-period)
  (asserts! (is-none (get miner-voted (map-get? map-voted-update-notifier {miner-who-voted: tx-sender}))) err-already-voted)
  (map-set map-voted-update-notifier {miner-who-voted: tx-sender} {miner-voted: voted-notifier})
  (if (is-none (get votes-number (map-get? map-votes-notifier {voted-notifier: voted-notifier})))
    (map-set map-votes-notifier {voted-notifier: voted-notifier} {votes-number: u1})
    (map-set map-votes-notifier {voted-notifier: voted-notifier} {votes-number: (+ (unwrap-panic (get votes-number (map-get? map-votes-notifier {voted-notifier: voted-notifier}))) u1)}))
  (try!
    (if (is-vote-accepted (+ (unwrap-panic (get votes-number (map-get? map-votes-notifier {voted-notifier: voted-notifier}))) u1) (var-get k))
    (begin
      (var-set notifier voted-notifier)
      (var-set notifier-vote-end-block block-height)
      (var-set notifier-vote-active false)
      (end-vote-notifier))
    (ok false)))
(ok true)))
;; WARNING FLOW

(define-public (warn-miner (miner principal))
(begin
(let ((incremented-value
      (if
        (is-some (get value (map-get? map-warnings {address: miner})))
        (+ (unwrap-panic (get value (map-get? map-warnings {address: miner}))) u1)
        u1)))
  (asserts! (is-eq tx-sender (var-get notifier)) err-only-notifier)
  (asserts!
    (not (and
      (is-none (at-block (unwrap! (get-block-info? id-header-hash (- block-height u1)) err-cant-unwrap-block-info) (get value (map-get? map-warnings {address: miner}))))
      (>= incremented-value u2)))
    err-one-warning-per-block)
  (asserts!
    (not
      (>=
        (-
          incremented-value
          (unwrap! (at-block (unwrap! (get-block-info? id-header-hash (- block-height u1)) err-cant-unwrap-block-info) (get value (map-get? map-warnings {address: miner}))) err-cant-unwrap-block-info))
        u2))
    err-one-warning-per-block)
    (ok
      (if
        (is-some (get value (map-get? map-warnings {address: miner})))
        (map-set map-warnings {address: miner} {value: (+ (unwrap-panic (get value (map-get? map-warnings {address: miner}))) u1)})
        (map-set map-warnings {address: miner} {value: u1}))))))

;; ELECTION FUNCTIONS

(define-private (is-vote-accepted (votes-number uint) (k-local uint))
(if
  (is-eq k-local u0) ;; k is 0 for n=1, n=2
    (>= votes-number u1)
    (>= votes-number k-local)))

(define-private (is-democratic-vote-accepted-notifier (votes-number uint) (k-local uint))
(if
  (is-eq k-local u0) ;; k is 0 for n=1, n=2
    (>= votes-number u1)
    (>= votes-number (/ k-local u2))))

(define-private (is-vote-rejected-join (votes-number uint) (k-local uint) (n-local uint))
(if
  (is-eq n-local u1)
  (>= votes-number u1)
  (if (is-eq n-local u2)
    (>= votes-number u2)
    (>= votes-number (+ (- n-local k-local) u1)))))


(define-private (is-vote-rejected-remove (votes-number uint) (k-local uint) (n-local uint))
(if
  (is-eq n-local u2)
  (>= votes-number u1)
  (if (is-eq n-local u3)
    (>= votes-number u2)
    (>= votes-number (+ (- n-local k-local) u1)))))

(define-private (is-vote-rejected-notifier (votes-number uint) (k-local uint) (n-local uint))
(if (is-eq n-local u2)
  (>= votes-number u1)
  (if (is-eq n-local u3)
    (>= votes-number u2)
    (>= votes-number (+ (- n-local k-local) u1)))))

;; LIST PROCESSING FUNCTIONS

(define-private (remove-principal-waiting-list (miner principal))
(begin
    (var-set waiting-list-miner-to-remove miner)
    (ok (filter is-principal-in-waiting-list (var-get waiting-list)))))

(define-private (remove-principal-pending-accept-list (miner principal))
(begin
    (var-set waiting-list-miner-to-remove miner)
    (ok (filter is-principal-in-pending-accept-list (var-get pending-accept-list)))))

(define-private (remove-principal-miners-list (miner principal))
(begin
  (var-set miners-list-miner-to-remove miner)
  (ok (filter is-principal-in-miners-list (var-get miners-list)))))

(define-private (remove-principal-proposed-removal-list (miner principal))
(begin
  (var-set proposed-removal-list-miner-to-remove miner)
  (ok (filter is-principal-in-proposed-removal-list (var-get proposed-removal-list)))))

;; MINER STATUS FUNCTIONS

(define-private (check-is-miner-when-requested-join (miner-to-vote principal))
(ok
  (if
    (is-some
      (if
        (is-eq
          (unwrap! (get value (map-get? map-block-asked-to-join {address: miner-to-vote})) err-cant-unwrap-asked-to-join)
          block-height)
        (get value (map-get? map-is-miner {address: tx-sender}))
        (at-block
          (unwrap!
            (get-block-info? id-header-hash
              (unwrap! (get value (map-get? map-block-asked-to-join {address: miner-to-vote})) err-cant-unwrap-asked-to-join))
          err-cant-unwrap-block-info)
          (get value (map-get? map-is-miner {address: tx-sender})))))
    (if
      (is-eq
        (unwrap!
          (get value (map-get? map-block-asked-to-join {address: miner-to-vote}))
        err-cant-unwrap-asked-to-join)
        block-height)
      (unwrap-panic (get value (map-get? map-is-miner {address: tx-sender})))
      (at-block
        (unwrap!
          (get-block-info? id-header-hash
            (unwrap-panic (get value (map-get? map-block-asked-to-join {address: miner-to-vote}))))
        err-cant-unwrap-block-info)
        (unwrap-panic (get value (map-get? map-is-miner {address: tx-sender})))))
  false)))

(define-private (check-is-miner-when-requested-remove (miner-to-vote principal))
(ok
  (if
    (is-some
      (if
        (is-eq
          (unwrap! (get value (map-get? map-block-proposed-to-remove {address: miner-to-vote})) err-cant-unwrap-asked-to-join)
          block-height)
        (get value (map-get? map-is-miner {address: tx-sender}))
        (at-block
          (unwrap!
            (get-block-info? id-header-hash
              (unwrap! (get value (map-get? map-block-proposed-to-remove {address: miner-to-vote})) err-cant-unwrap-asked-to-join))
          err-cant-unwrap-block-info)
          (get value (map-get? map-is-miner {address: tx-sender})))))
  (if
      (is-eq
        (unwrap!
          (get value (map-get? map-block-proposed-to-remove {address: miner-to-vote}))
        err-cant-unwrap-asked-to-join)
        block-height)
      (unwrap-panic (get value (map-get? map-is-miner {address: tx-sender})))
      (at-block
        (unwrap!
          (get-block-info? id-header-hash
            (unwrap-panic (get value (map-get? map-block-proposed-to-remove {address: miner-to-vote}))))
        err-cant-unwrap-block-info)
        (unwrap-panic (get value (map-get? map-is-miner {address: tx-sender})))))
  false)))

(define-read-only (check-is-miner-when-requested-join-tool-fn (miner-to-vote-address principal))
(get value (map-get? map-is-miner {address: tx-sender})))

(define-private (check-is-miner-now (miner principal))
(if (is-some (get value (map-get? map-is-miner {address: miner})))
  (unwrap-panic (get value (map-get? map-is-miner {address: miner})))
  false))

(define-private (check-is-proposed-for-removal-now (miner principal))
(if (is-some (get value (map-get? map-is-proposed-for-removal {address: miner})))
  (unwrap-panic (get value (map-get? map-is-proposed-for-removal {address: miner})))
  false))

(define-private (check-is-waiting-now (miner principal))
(if (is-some (get value (map-get? map-is-waiting {address: miner})))
  (unwrap-panic (get value (map-get? map-is-waiting {address: miner})))
  false))

(define-private (check-is-pending-now (miner principal))
(if (is-some (get value (map-get? map-is-pending {address: miner})))
  (unwrap-panic (get value (map-get? map-is-pending {address: miner})))
  false)
)

(define-private (get-reward-at-block (block-number uint))
(begin
  {reward: (get-block-info? block-reward block-number),
  claimer: (get-block-info? miner-address block-number)}))

(define-read-only (get-reward-at-block-read (block-number uint))
(begin
  {reward: (get-block-info? block-reward block-number),
  claimer: (get-block-info? miner-address block-number)
  }))

(define-read-only (get-address-status (address principal))
(if (check-is-miner-now address)
  (ok "is-miner")
  (if (check-is-waiting-now address)
    (ok "is-waiting")
    (if (check-is-pending-now address)
      (ok "is-pending")
      (ok "is-none")
    )
  )
))

;; READ-ONLY UTILS

;; (define-read-only (check-vote-accepted) ;; to check the vote status inside FE
;; (is-vote-accepted (unwrap-panic (get value (map-get? map-votes-accept-join {address: tx-sender})))))

(define-read-only (get-principals-list (address principal))
(map-get? add-lists-principal {address: tx-sender}))

(define-read-only (get-k)
(var-get k))

(define-read-only (get-notifier)
(var-get notifier))

(define-read-only (get-waiting-list)
(var-get waiting-list))

(define-read-only (get-miners-list)
(var-get miners-list))

(define-read-only (get-pending-accept-list)
(var-get pending-accept-list ))

(define-read-only (get-proposed-removal-list)
(var-get proposed-removal-list ))

(define-read-only (get-notifier-vote-status)
(var-get notifier-vote-active))

(define-read-only (get-notifier-vote-number (voted-notifier principal))
(get votes-number (map-get? map-votes-notifier {voted-notifier: voted-notifier})))

(define-read-only (get-max-voted-notifier)
(var-get max-voted-proposed-notifier))

(define-read-only (get-max-votes-notifier)
(var-get max-votes-notifier))

(define-read-only (get-current-block)
(ok block-height))

(define-private (is-principal-in-waiting-list (miner principal))
(not (is-eq
  (var-get waiting-list-miner-to-remove)
  miner)))

(define-private (is-principal-in-pending-accept-list (miner principal))
(not (is-eq
  (var-get pending-accept-list-miner-to-remove)
  miner)))

(define-private (is-principal-in-miners-list (miner principal))
(not (is-eq
  (var-get miners-list-miner-to-remove)
  miner)))

(define-private (is-principal-in-proposed-removal-list (miner principal))
(not (is-eq
  (var-get proposed-removal-list-miner-to-remove)
  miner)))
"###;

lazy_static! {
    static ref HTTP_BINDING: Mutex<Option<String>> = Mutex::new(None);
}

#[test]
fn integration_test_get_info() {
    let mut conf = super::new_test_conf();
    let spender_addr: StacksAddress = to_addr(&StacksPrivateKey::from_hex(SK_3).unwrap()).into();
    let principal_sk = StacksPrivateKey::from_hex(SK_2).unwrap();
    let contract_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    const SK_deployer: &str = "753b7cc01a1a2e86221266a154af739463fce51219d97e4f856cd7200c3bd2a601";
    let deployer_sk = StacksPrivateKey::from_hex(SK_deployer).unwrap();

    // let SK_wallet_list = ["7287ba251d44a4d3fd9276c88ce34c5c52a038955511cccaf77e61068649c17801",
    //     "530d9f61984c888536871c6573073bdfc0058896dc1adfe9a6a10dfacadc209101","d655b2523bcd65e34889725c73064feb17ceb796831c0e111ba1a552b0f31b3901",
    //     "f9d7206a47f14d2870c163ebab4bf3e70d18f5d14ce1031f3902fbbc894fe4c701","3eccc5dac8056590432db6a35d52b9896876a3d5cbdea53b72400bc9c2099fe801",
    //     "7036b29cb5e235e5fd9b09ae3e8eec4404e44906814d5d01cbca968a60ed4bfb01","b463f0df6c05d2f156393eee73f8016c5372caa0e9e29a901bb7171d90dc4f1401",
    //     "6a1a754ba863d7bab14adbbc3f8ebb090af9e871ace621d3e5ab634e1422885e01","2b2c2dd7ae64aa7880042a443f5a1e1a1b575cc0ef16d6c7e3bb8a9ce08bfe1d01",
    //     "47599fb4a8cfb07e2db61484c81459db81a5480e770b0de8cbe8de960834bf1701","2aa06d7311b9fa7849babc24fb34f6977b1ca87338b3450543bbc02b6606ff2001",
    //     "86e7d2e5d04d53cca863c3af6d38fcbcc235b69e50970671ea8afb12e6b2312701","6f8a12f241dbc589b5faa5beb35c884502c58563bb7d1628908093a6dd766caa01",
    //     "4640119e78260c3a6597acbd1d5cebdcbca8ba74e30c4b404d77021e5e85eb5301","dafee082a51836137343847410d8b4877797aaef954a351d96de275d2e2efed101",
    //     "d7a7f8c63768c935d330c8e093114c66e4acc9a02aafbc93da8ad413f38ae62801","a359498c4108ed535a6c585c9646a73c536cdf9542a9842c80c2ee91d513e30501",
    //     "ed191fc37f95d3f86d74b0d1aa72fa41bbf648a73eda862164bc4f55ab90a37a01","debb268578dcf55c7beb30b2d50402df0e7679e4d155791e5ac3454ec519f6e601",
    //     "db9a4604505b938cb0c521a1c4c19d0e903d1cfb655944639305bab2381e806201","2dacbeca60f646fd111fe59ab517847e62a883a65c8b7f47bb685f48de0d7adf01",
    //     "1c9b2d5315538de804ff70cc93f263a47d094dcb19f4795fc635b44292e85fbb01","477b7925df1f3f666b23444cff9b3fc5993732d707e8ccb90d63e7e0f9343c3c01",
    //     "5ce97bb6f6a60cb1a04412ba2faf0444900355046d31cc1f200129248a700d9001","ab7698183bc68a323da1a997941025a64612b8c3b71179a4f8de81a17abc621801"];
    // let mut wallet_list_sk = [];
    //
    // SK_wallet_list.iter().map(|value| {
    //     wallet_list_sk.push(value.to_string());
    // }).count();

    let SK_wallet_dictionary = HashMap::from([
        ("1","7287ba251d44a4d3fd9276c88ce34c5c52a038955511cccaf77e61068649c17801"),
        ("2","530d9f61984c888536871c6573073bdfc0058896dc1adfe9a6a10dfacadc209101"),
        ("3","d655b2523bcd65e34889725c73064feb17ceb796831c0e111ba1a552b0f31b3901"),
        ("4","f9d7206a47f14d2870c163ebab4bf3e70d18f5d14ce1031f3902fbbc894fe4c701"),
        ("5","3eccc5dac8056590432db6a35d52b9896876a3d5cbdea53b72400bc9c2099fe801"),
        ("6","7036b29cb5e235e5fd9b09ae3e8eec4404e44906814d5d01cbca968a60ed4bfb01"),
        ("7","b463f0df6c05d2f156393eee73f8016c5372caa0e9e29a901bb7171d90dc4f1401"),
        ("8","6a1a754ba863d7bab14adbbc3f8ebb090af9e871ace621d3e5ab634e1422885e01"),
        ("9","2b2c2dd7ae64aa7880042a443f5a1e1a1b575cc0ef16d6c7e3bb8a9ce08bfe1d01"),
        ("10","47599fb4a8cfb07e2db61484c81459db81a5480e770b0de8cbe8de960834bf1701"),
        ("11","2aa06d7311b9fa7849babc24fb34f6977b1ca87338b3450543bbc02b6606ff2001"),
        ("12","86e7d2e5d04d53cca863c3af6d38fcbcc235b69e50970671ea8afb12e6b2312701"),
        ("13","6f8a12f241dbc589b5faa5beb35c884502c58563bb7d1628908093a6dd766caa01"),
        ("14","4640119e78260c3a6597acbd1d5cebdcbca8ba74e30c4b404d77021e5e85eb5301"),
        ("15","dafee082a51836137343847410d8b4877797aaef954a351d96de275d2e2efed101"),
        ("16","d7a7f8c63768c935d330c8e093114c66e4acc9a02aafbc93da8ad413f38ae62801"),
        ("17","a359498c4108ed535a6c585c9646a73c536cdf9542a9842c80c2ee91d513e30501"),
        ("18","ed191fc37f95d3f86d74b0d1aa72fa41bbf648a73eda862164bc4f55ab90a37a01"),
        ("19","debb268578dcf55c7beb30b2d50402df0e7679e4d155791e5ac3454ec519f6e601"),
        ("20","db9a4604505b938cb0c521a1c4c19d0e903d1cfb655944639305bab2381e806201"),
        ("21","2dacbeca60f646fd111fe59ab517847e62a883a65c8b7f47bb685f48de0d7adf01"),
        ("22","1c9b2d5315538de804ff70cc93f263a47d094dcb19f4795fc635b44292e85fbb01"),
        ("23","477b7925df1f3f666b23444cff9b3fc5993732d707e8ccb90d63e7e0f9343c3c01"),
        ("24","5ce97bb6f6a60cb1a04412ba2faf0444900355046d31cc1f200129248a700d9001"),
        ("25","ab7698183bc68a323da1a997941025a64612b8c3b71179a4f8de81a17abc621801")
    ]);
    let wallet_dictionary_sk = SK_wallet_dictionary
        .iter()
        .map(|(&k, &v)| (k, StacksPrivateKey::from_hex(v).unwrap()))
        .collect::<HashMap<_, _>>();

    wallet_dictionary_sk.iter().for_each(|(&k, &v)| {
        conf.initial_balances.push(InitialBalance {
            address: to_addr(&v).into(),
            amount: 1000,
        })
    });

    conf.initial_balances.push(InitialBalance {
        address: to_addr(&deployer_sk).into(),
        amount: 1000,
    });


    conf.burnchain.commit_anchor_block_within = 5000;
    conf.miner.min_tx_fee = 0;
    conf.miner.first_attempt_time_ms = i64::max_value() as u64;
    conf.miner.subsequent_attempt_time_ms = i64::max_value() as u64;

    let num_rounds = 18;

    let rpc_bind = conf.node.rpc_bind.clone();
    let mut run_loop = RunLoop::new(conf);

    {
        let mut http_opt = HTTP_BINDING.lock().unwrap();
        http_opt.replace(format!("http://{}", &rpc_bind));
    }

    // r1 deployer start it
    // r2 other 15 ask to join
    // r3 deployer votes them
    // r4 try-enter pool
    run_loop
        .callbacks
        .on_new_tenure(|round, _burnchain_tip, chain_tip, tenure| {
            let mut chainstate_copy = tenure.open_chainstate();
            let sortdb = tenure.open_fake_sortdb();


            let principal_sk_local = StacksPrivateKey::from_hex(SK_2).unwrap();
            let contract_sk_local = StacksPrivateKey::from_hex(SK_1).unwrap();
            const SK_deployer_local: &str = "753b7cc01a1a2e86221266a154af739463fce51219d97e4f856cd7200c3bd2a601";
            let deployer_sk_local = StacksPrivateKey::from_hex(SK_deployer).unwrap();

            let SK_wallet_dictionary_local = HashMap::from([
                ("1","7287ba251d44a4d3fd9276c88ce34c5c52a038955511cccaf77e61068649c17801"),
                ("2","530d9f61984c888536871c6573073bdfc0058896dc1adfe9a6a10dfacadc209101"),
                ("3","d655b2523bcd65e34889725c73064feb17ceb796831c0e111ba1a552b0f31b3901"),
                ("4","f9d7206a47f14d2870c163ebab4bf3e70d18f5d14ce1031f3902fbbc894fe4c701"),
                ("5","3eccc5dac8056590432db6a35d52b9896876a3d5cbdea53b72400bc9c2099fe801"),
                ("6","7036b29cb5e235e5fd9b09ae3e8eec4404e44906814d5d01cbca968a60ed4bfb01"),
                ("7","b463f0df6c05d2f156393eee73f8016c5372caa0e9e29a901bb7171d90dc4f1401"),
                ("8","6a1a754ba863d7bab14adbbc3f8ebb090af9e871ace621d3e5ab634e1422885e01"),
                ("9","2b2c2dd7ae64aa7880042a443f5a1e1a1b575cc0ef16d6c7e3bb8a9ce08bfe1d01"),
                ("10","47599fb4a8cfb07e2db61484c81459db81a5480e770b0de8cbe8de960834bf1701"),
                ("11","2aa06d7311b9fa7849babc24fb34f6977b1ca87338b3450543bbc02b6606ff2001"),
                ("12","86e7d2e5d04d53cca863c3af6d38fcbcc235b69e50970671ea8afb12e6b2312701"),
                ("13","6f8a12f241dbc589b5faa5beb35c884502c58563bb7d1628908093a6dd766caa01"),
                ("14","4640119e78260c3a6597acbd1d5cebdcbca8ba74e30c4b404d77021e5e85eb5301"),
                ("15","dafee082a51836137343847410d8b4877797aaef954a351d96de275d2e2efed101"),
                ("16","d7a7f8c63768c935d330c8e093114c66e4acc9a02aafbc93da8ad413f38ae62801"),
                ("17","a359498c4108ed535a6c585c9646a73c536cdf9542a9842c80c2ee91d513e30501"),
                ("18","ed191fc37f95d3f86d74b0d1aa72fa41bbf648a73eda862164bc4f55ab90a37a01"),
                ("19","debb268578dcf55c7beb30b2d50402df0e7679e4d155791e5ac3454ec519f6e601"),
                ("20","db9a4604505b938cb0c521a1c4c19d0e903d1cfb655944639305bab2381e806201"),
                ("21","2dacbeca60f646fd111fe59ab517847e62a883a65c8b7f47bb685f48de0d7adf01"),
                ("22","1c9b2d5315538de804ff70cc93f263a47d094dcb19f4795fc635b44292e85fbb01"),
                ("23","477b7925df1f3f666b23444cff9b3fc5993732d707e8ccb90d63e7e0f9343c3c01"),
                ("24","5ce97bb6f6a60cb1a04412ba2faf0444900355046d31cc1f200129248a700d9001"),
                ("25","ab7698183bc68a323da1a997941025a64612b8c3b71179a4f8de81a17abc621801")
            ]);

            let wallet_dictionary_sk_local = SK_wallet_dictionary_local
                .iter()
                .map(|(&k, &v)| (k, StacksPrivateKey::from_hex(v).unwrap()))
                .collect::<HashMap<_, _>>();

            let contract_sk = StacksPrivateKey::from_hex(SK_deployer).unwrap();
            let header_hash = chain_tip.block.block_hash();
            let consensus_hash = chain_tip.metadata.consensus_hash;

            if round == 1 {
                // block-height = 2
                eprintln!("Tenure in 1 started!");
                let publish_tx =
                    make_contract_publish(&deployer_sk_local, 0, 10, "mining-pool", MINING_POOL_CONTRACT);
                println!("tx publish {:?}", publish_tx);
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        publish_tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();

                // store this for later, because we can't just do it in a refcell or any outer
                // variable because this is a function pointer type, and thus can't access anything
                // outside its scope :(
                let tmppath = "/tmp/integration_test_mining-pool";
                let old_tip = StacksBlockId::new(&consensus_hash, &header_hash);
                use std::fs;
                use std::io::Write;
                if fs::metadata(&tmppath).is_ok() {
                    fs::remove_file(&tmppath).unwrap();
                }
                let mut f = fs::File::create(&tmppath).unwrap();
                f.write_all(&old_tip.serialize_to_vec()).unwrap();
            } else if round == 2 {
                // r2 other 5 ask to join
                // r3 deployer votes them
                // r4 try-enter pool

                // block-height = 3
                (1..7).for_each(|i| {
                    let v = i.to_string();
                    let tx = make_contract_call(
                        &wallet_dictionary_sk_local[v.as_str()],
                        0,
                        10,
                        &to_addr(&deployer_sk_local),
                        "mining-pool",
                        "ask-to-join",
                        &[Value::from(ASCIIData {
                            data: format!("aaaaaa{}", v.as_str()).to_string().into_bytes(),
                        })]
                    );

                    eprintln!("ask-to-join submitted");
                    tenure
                        .mem_pool
                        .submit_raw(
                            &mut chainstate_copy,
                            &sortdb,
                            &consensus_hash,
                            &header_hash,
                            tx,
                            &ExecutionCost::max_value(),
                            &StacksEpochId::Epoch21,
                        )
                        .unwrap();

                });
            } else if round == 3 {
                // r3 deployer votes them
                // r4 try-enter pool

                // block-height = 4
                (1..5).for_each(|i| {
                    let v = i.to_string();
                    let tx = make_contract_call(
                        &deployer_sk_local,
                         i,
                        10,
                        &to_addr(&deployer_sk_local),
                        "mining-pool",
                        "vote-positive-join-request",
                        &[Value::Principal(PrincipalData::from(
                            PrincipalData::parse_standard_principal(
                                &to_addr(&wallet_dictionary_sk_local[v.as_str()]).to_string()).unwrap()))]
                    );

                    eprintln!("vote-positive submitted");
                    tenure
                        .mem_pool
                        .submit_raw(
                            &mut chainstate_copy,
                            &sortdb,
                            &consensus_hash,
                            &header_hash,
                            tx,
                            &ExecutionCost::max_value(),
                            &StacksEpochId::Epoch21,
                        )
                        .unwrap();
                });

                // block-height = 4
                (5..7).for_each(|i| {
                    let v = i.to_string();
                    let tx = make_contract_call(
                        &deployer_sk_local,
                        i,
                        10,
                        &to_addr(&deployer_sk_local),
                        "mining-pool",
                        "vote-negative-join-request",
                        &[Value::Principal(PrincipalData::from(
                            PrincipalData::parse_standard_principal(
                                &to_addr(&wallet_dictionary_sk_local[v.as_str()]).to_string()).unwrap()))]
                    );

                    eprintln!("vote-negative submitted");
                    tenure
                        .mem_pool
                        .submit_raw(
                            &mut chainstate_copy,
                            &sortdb,
                            &consensus_hash,
                            &header_hash,
                            tx,
                            &ExecutionCost::max_value(),
                            &StacksEpochId::Epoch21,
                        )
                        .unwrap();
                });

            } else if round == 4 {
                // r4 try-enter pool

                // block-height = 5
                (1..5).for_each(|i| {
                    let v = i.to_string();
                    let tx = make_contract_call(
                        &wallet_dictionary_sk_local[v.as_str()],
                        1,
                        10,
                        &to_addr(&deployer_sk_local),
                        "mining-pool",
                        "try-enter-pool",
                        &[]
                    );

                    eprintln!("try-enter submitted");
                    tenure
                        .mem_pool
                        .submit_raw(
                            &mut chainstate_copy,
                            &sortdb,
                            &consensus_hash,
                            &header_hash,
                            tx,
                            &ExecutionCost::max_value(),
                            &StacksEpochId::Epoch21,
                        )
                        .unwrap();
                });

                // this 2 will fail
                // block-height = 5
                (5..7).for_each(|i| {
                    let v = i.to_string();
                    let tx = make_contract_call(
                        &wallet_dictionary_sk_local[v.as_str()],
                        1,
                        10,
                        &to_addr(&deployer_sk_local),
                        "mining-pool",
                        "try-enter-pool",
                        &[]
                    );

                    eprintln!("try-enter submitted and will fail");
                    tenure
                        .mem_pool
                        .submit_raw(
                            &mut chainstate_copy,
                            &sortdb,
                            &consensus_hash,
                            &header_hash,
                            tx,
                            &ExecutionCost::max_value(),
                            &StacksEpochId::Epoch21,
                        )
                        .unwrap();
                });

            }
            // pass some blocks
            // at round 6
            // add pending miners to list
            else if round == 6 {

                // block-height = 7
                let tx = make_contract_call(
                    &wallet_dictionary_sk_local["24"],
                    0,
                    10,
                    &to_addr(&deployer_sk_local),
                    "mining-pool",
                    "add-pending-miners-to-pool",
                    &[]
                );


                eprintln!("add-pending-miners submitted");
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();
            } else if round == 7 {
                // r2 other 15 ask to join
                // r3 deployer votes them
                // r4 try-enter pool

                // block-height = 8
                (5..7).for_each(|i| {
                    let v = i.to_string();
                    let tx = make_contract_call(
                        &wallet_dictionary_sk_local[v.as_str()],
                        2,
                        10,
                        &to_addr(&deployer_sk_local),
                        "mining-pool",
                        "ask-to-join",
                        &[Value::from(ASCIIData {
                            data: format!("aaaaaa{}", v.as_str()).to_string().into_bytes(),
                        })]
                    );

                    eprintln!("ask-to-join submitted");
                    tenure
                        .mem_pool
                        .submit_raw(
                            &mut chainstate_copy,
                            &sortdb,
                            &consensus_hash,
                            &header_hash,
                            tx,
                            &ExecutionCost::max_value(),
                            &StacksEpochId::Epoch21,
                        )
                        .unwrap();
                });
            } else if round == 8 {
                // r8 - 2 vote positive wallet_6 and 4 vote negative wallet_7
                //

                (1..5).for_each(|i| {
                    let v = i.to_string();
                    let tx = make_contract_call(
                        &wallet_dictionary_sk_local[v.as_str()],
                        2,
                        10,
                        &to_addr(&deployer_sk_local),
                        "mining-pool",
                        "vote-negative-join-request",
                        &[Value::Principal(PrincipalData::from(
                            PrincipalData::parse_standard_principal(
                                &to_addr(&wallet_dictionary_sk_local["6"]).to_string()).unwrap()))]
                    );

                    eprintln!("vote-negative submitted");
                    tenure
                        .mem_pool
                        .submit_raw(
                            &mut chainstate_copy,
                            &sortdb,
                            &consensus_hash,
                            &header_hash,
                            tx,
                            &ExecutionCost::max_value(),
                            &StacksEpochId::Epoch21,
                        )
                        .unwrap();
                });

                // block-height = 9
                (1..3).for_each(|i| {
                    let v = i.to_string();
                    let tx = make_contract_call(
                        &wallet_dictionary_sk_local[v.as_str()],
                        3,
                        10,
                        &to_addr(&deployer_sk_local),
                        "mining-pool",
                        "vote-positive-join-request",
                        &[Value::Principal(PrincipalData::from(
                            PrincipalData::parse_standard_principal(
                                &to_addr(&wallet_dictionary_sk_local["5"]).to_string()).unwrap()))]
                    );

                    eprintln!("vote-positive submitted");
                    tenure
                        .mem_pool
                        .submit_raw(
                            &mut chainstate_copy,
                            &sortdb,
                            &consensus_hash,
                            &header_hash,
                            tx,
                            &ExecutionCost::max_value(),
                            &StacksEpochId::Epoch21,
                        )
                        .unwrap();
                });


            } else if round == 9 {
                // try enter pool w5 and w6
                // w5 succeeds and w6 fails
                // block-height = 10
                (5..7).for_each(|i| {
                    let v = i.to_string();
                    let tx = make_contract_call(
                        &wallet_dictionary_sk_local[v.as_str()],
                        3,
                        10,
                        &to_addr(&deployer_sk_local),
                        "mining-pool",
                        "try-enter-pool",
                        &[]
                    );

                    eprintln!("try-enter submitted");
                    tenure
                        .mem_pool
                        .submit_raw(
                            &mut chainstate_copy,
                            &sortdb,
                            &consensus_hash,
                            &header_hash,
                            tx,
                            &ExecutionCost::max_value(),
                            &StacksEpochId::Epoch21,
                        )
                        .unwrap();
                });
            } else if round == 10 {
                // start vote notifier
                // block-height = 11

                let tx = make_contract_call(
                    &wallet_dictionary_sk_local["24"],
                    1,
                    10,
                    &to_addr(&deployer_sk_local),
                    "mining-pool",
                    "start-vote-notifier",
                    &[]
                );

                eprintln!("start-vote-notifier submitted");
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();
            }
            // leave function
            else if round == 11 {
                // start vote notifier
                // block-height = 12

                let tx = make_contract_call(
                    &wallet_dictionary_sk_local["3"],
                    3,
                    10,
                    &to_addr(&deployer_sk_local),
                    "mining-pool",
                    "leave-pool",
                    &[]
                );

                eprintln!("leave-pool with w3 submitted");
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();
            }
            // removal
            else if round == 12 {
                // block-height = 13

                let tx = make_contract_call(
                    &wallet_dictionary_sk_local["1"],
                    4,
                    10,
                    &to_addr(&deployer_sk_local),
                    "mining-pool",
                    "propose-removal",
                    &[Value::Principal(PrincipalData::from(
                        PrincipalData::parse_standard_principal(
                            &to_addr(&wallet_dictionary_sk_local["4"]).to_string()).unwrap()))]
                );

                eprintln!("propose-removal by w1 for w4 submitted");
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();
            }

            else if round == 13 {
                // deployer votes negative remove request
                // w1 and w2 votes positive

                // block-height = 14

                let tx = make_contract_call(
                    &deployer_sk_local,
                    7,
                    10,
                    &to_addr(&deployer_sk_local),
                    "mining-pool",
                    "vote-negative-remove-request",
                    &[Value::Principal(PrincipalData::from(
                        PrincipalData::parse_standard_principal(
                            &to_addr(&wallet_dictionary_sk_local["4"]).to_string()).unwrap()))]
                );

                eprintln!("vote-negative-remove submitted");
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();


                let tx = make_contract_call(
                    &wallet_dictionary_sk_local["1"],
                    5,
                    10,
                    &to_addr(&deployer_sk_local),
                    "mining-pool",
                    "vote-positive-join-request",
                    &[Value::Principal(PrincipalData::from(
                        PrincipalData::parse_standard_principal(
                            &to_addr(&wallet_dictionary_sk_local["4"]).to_string()).unwrap()))]
                );

                eprintln!("vote-positive by w1 to w4 submitted");
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();


                let tx = make_contract_call(
                    &wallet_dictionary_sk_local["2"],
                    4,
                    10,
                    &to_addr(&deployer_sk_local),
                    "mining-pool",
                    "vote-positive-join-request",
                    &[Value::Principal(PrincipalData::from(
                        PrincipalData::parse_standard_principal(
                            &to_addr(&wallet_dictionary_sk_local["4"]).to_string()).unwrap()))]
                );

                eprintln!("vote-positive by w2 to w4 submitted");
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();
            }
            else if round == 14 {
                // vote notifier
                // block height 15

                // w1 votes for w2
                // deployer and w2 votes for w1
                // => w1 new notifier

                    let tx = make_contract_call(
                        &wallet_dictionary_sk_local["1"],
                        7,
                        10,
                        &to_addr(&deployer_sk_local),
                        "mining-pool",
                        "vote-notifier",
                        &[Value::Principal(PrincipalData::from(
                            PrincipalData::parse_standard_principal(
                                &to_addr(&wallet_dictionary_sk_local["2"]).to_string()).unwrap()))]
                    );

                    eprintln!("vote-notifier by w1 to w2 submitted");
                    tenure
                        .mem_pool
                        .submit_raw(
                            &mut chainstate_copy,
                            &sortdb,
                            &consensus_hash,
                            &header_hash,
                            tx,
                            &ExecutionCost::max_value(),
                            &StacksEpochId::Epoch21,
                        )
                        .unwrap();


                let tx = make_contract_call(
                    &deployer_sk_local,
                    8,
                    10,
                    &to_addr(&deployer_sk_local),
                    "mining-pool",
                    "vote-notifier",
                    &[Value::Principal(PrincipalData::from(
                        PrincipalData::parse_standard_principal(
                            &to_addr(&wallet_dictionary_sk_local["1"]).to_string()).unwrap()))]
                );

                eprintln!("vote-notifier by deployer to w1 submitted");
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();


                let tx = make_contract_call(
                    &wallet_dictionary_sk_local["2"],
                    5,
                    10,
                    &to_addr(&deployer_sk_local),
                    "mining-pool",
                    "vote-notifier",
                    &[Value::Principal(PrincipalData::from(
                        PrincipalData::parse_standard_principal(
                            &to_addr(&wallet_dictionary_sk_local["1"]).to_string()).unwrap()))]
                );

                eprintln!("vote-notifier by w2 to w1 submitted");
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();
            }
            // warn miner w1 by w4
            else if round == 15 {
                // start vote notifier
                // block-height = 16

                let tx = make_contract_call(
                    &wallet_dictionary_sk_local["1"],
                    8,
                    10,
                    &to_addr(&deployer_sk_local),
                    "mining-pool",
                    "warn-miner",
                    &[Value::Principal(PrincipalData::from(
                        PrincipalData::parse_standard_principal(
                            &to_addr(&wallet_dictionary_sk_local["2"]).to_string()).unwrap()))]
                );

                eprintln!("warn-miner w2 by the notifier new notifier w1 submitted");
                tenure
                    .mem_pool
                    .submit_raw(
                        &mut chainstate_copy,
                        &sortdb,
                        &consensus_hash,
                        &header_hash,
                        tx,
                        &ExecutionCost::max_value(),
                        &StacksEpochId::Epoch21,
                    )
                    .unwrap();
            }

            return;
        });

    run_loop.callbacks.on_new_stacks_chain_state(|round, _burnchain_tip, chain_tip, chain_state, burn_dbconn| {
        let contract_addr = to_addr(&StacksPrivateKey::from_hex(SK_1).unwrap());
        let contract_identifier =
            QualifiedContractIdentifier::parse(&format!("{}.{}", &contract_addr, "get-info")).unwrap();
        let impl_trait_contract_identifier =
            QualifiedContractIdentifier::parse(&format!("{}.{}", &contract_addr, "impl-trait-contract")).unwrap();

        let http_origin = {
            HTTP_BINDING.lock().unwrap().clone().unwrap()
        };

        //

        // match round {
        //     1 => {
        //         // - Chain length should be 2.
        //         let blocks = StacksChainState::list_blocks(&chain_state.db()).unwrap();
        //         assert!(chain_tip.metadata.stacks_block_height == 2);
        //
        //         // Block #1 should have 5 txs
        //         assert_eq!(chain_tip.block.txs.len(), 5);
        //
        //         let parent = chain_tip.block.header.parent_block;
        //         let bhh = &chain_tip.metadata.index_block_hash();
        //         eprintln!("Current Block: {}       Parent Block: {}", bhh, parent);
        //         let parent_val = Value::buff_from(parent.as_bytes().to_vec()).unwrap();
        //
        //         // find header metadata
        //         let mut headers = vec![];
        //         for block in blocks.iter() {
        //             let header = StacksChainState::get_anchored_block_header_info(chain_state.db(), &block.0, &block.1).unwrap().unwrap();
        //             eprintln!("{}/{}: {:?}", &block.0, &block.1, &header);
        //             headers.push(header);
        //         }
        //
        //         let _tip_header_info = headers.last().unwrap();
        //
        //         // find miner metadata
        //         let mut miners = vec![];
        //         for block in blocks.iter() {
        //             let miner = StacksChainState::get_miner_info(chain_state.db(), &block.0, &block.1).unwrap().unwrap();
        //             miners.push(miner);
        //         }
        //
        //         let _tip_miner = miners.last().unwrap();
        //
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "block-height"),
        //             Value::UInt(2));
        //
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn,bhh, &contract_identifier, "(test-1)"),
        //             Value::some(Value::UInt(headers[0].burn_header_timestamp as u128)).unwrap());
        //
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "(test-2)"),
        //             Value::none());
        //
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "(test-3)"),
        //             Value::none());
        //
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "(test-4 u1)"),
        //             Value::some(parent_val.clone()).unwrap());
        //
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "(test-5)"),
        //             Value::some(parent_val).unwrap());
        //
        //         // test-6 and test-7 return the block at height 1's VRF-seed,
        //         //   which in this integration test, should be blocks[0]
        //         let last_tip = blocks[0];
        //         eprintln!("Last block info: stacks: {}, burn: {}", last_tip.1, last_tip.0);
        //         let last_block = StacksChainState::load_block(&chain_state.blocks_path, &last_tip.0, &last_tip.1).unwrap().unwrap();
        //         assert_eq!(parent, last_block.header.block_hash());
        //
        //         let last_vrf_seed = VRFSeed::from_proof(&last_block.header.proof).as_bytes().to_vec();
        //         let last_burn_header = headers[0].burn_header_hash.as_bytes().to_vec();
        //
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "(test-6)"),
        //             Value::some(Value::buff_from(last_burn_header).unwrap()).unwrap());
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "(test-7)"),
        //             Value::some(Value::buff_from(last_vrf_seed).unwrap()).unwrap());
        //
        //         // verify that we can get the block miner
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "(test-8)"),
        //             Value::some(Value::Principal(miners[0].address.to_account_principal())).unwrap());
        //
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "(test-9)"),
        //             Value::none());
        //
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "(test-10)"),
        //             Value::none());
        //
        //         // verify we can read the burn block height
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &contract_identifier, "(test-11)"),
        //             Value::UInt(2));
        //
        //     },
        //     2 => {
        //         // Chain height should be 3
        //         let bhh = &chain_tip.metadata.index_block_hash();
        //         assert_eq!(
        //             chain_state.clarity_eval_read_only(
        //                 burn_dbconn, bhh, &impl_trait_contract_identifier, "(test-height)"),
        //             Value::UInt(3));
        //     }
        //     4 => {
        //         let bhh = &chain_tip.metadata.index_block_hash();
        //
        //         assert_eq!(Value::Bool(true), chain_state.clarity_eval_read_only(
        //             burn_dbconn, bhh, &contract_identifier, "(exotic-block-height u2)"));
        //         assert_eq!(Value::Bool(true), chain_state.clarity_eval_read_only(
        //             burn_dbconn, bhh, &contract_identifier, "(exotic-block-height u3)"));
        //         assert_eq!(Value::Bool(true), chain_state.clarity_eval_read_only(
        //             burn_dbconn, bhh, &contract_identifier, "(exotic-block-height u4)"));
        //
        //         assert_eq!(Value::Bool(true), chain_state.clarity_eval_read_only(
        //             burn_dbconn, bhh, &contract_identifier, "(exotic-data-checks u3)"));
        //         assert_eq!(Value::Bool(true), chain_state.clarity_eval_read_only(
        //             burn_dbconn, bhh, &contract_identifier, "(exotic-data-checks u4)"));
        //
        //         let client = reqwest::blocking::Client::new();
        //         let path = format!("{}/v2/map_entry/{}/{}/{}",
        //                            &http_origin, &contract_addr, "get-info", "block-data");
        //
        //         let key: Value = TupleData::from_data(vec![("height".into(), Value::UInt(3))])
        //             .unwrap().into();
        //
        //         eprintln!("Test: POST {}", path);
        //         let res = client.post(&path)
        //             .json(&key.serialize())
        //             .send()
        //             .unwrap().json::<HashMap<String, String>>().unwrap();
        //         let result_data = Value::try_deserialize_hex_untyped(&res["data"][2..]).unwrap();
        //         let expected_data = chain_state.clarity_eval_read_only(burn_dbconn, bhh, &contract_identifier,
        //                                                                "(some (get-exotic-data-info u3))");
        //         assert!(res.get("proof").is_some());
        //
        //         assert_eq!(result_data, expected_data);
        //
        //         let key: Value = TupleData::from_data(vec![("height".into(), Value::UInt(100))])
        //             .unwrap().into();
        //
        //         eprintln!("Test: POST {}", path);
        //         let res = client.post(&path)
        //             .json(&key.serialize())
        //             .send()
        //             .unwrap().json::<HashMap<String, String>>().unwrap();
        //         let result_data = Value::try_deserialize_hex_untyped(&res["data"][2..]).unwrap();
        //         assert_eq!(result_data, Value::none());
        //
        //         let sender_addr = to_addr(&StacksPrivateKey::from_hex(SK_3).unwrap());
        //
        //         // now, let's use a query string to get data without a proof
        //         let path = format!("{}/v2/map_entry/{}/{}/{}?proof=0",
        //                            &http_origin, &contract_addr, "get-info", "block-data");
        //
        //         let key: Value = TupleData::from_data(vec![("height".into(), Value::UInt(3))])
        //             .unwrap().into();
        //
        //         eprintln!("Test: POST {}", path);
        //         let res = client.post(&path)
        //             .json(&key.serialize())
        //             .send()
        //             .unwrap().json::<HashMap<String, String>>().unwrap();
        //
        //         assert!(res.get("proof").is_none());
        //         let result_data = Value::try_deserialize_hex_untyped(&res["data"][2..]).unwrap();
        //         let expected_data = chain_state.clarity_eval_read_only(burn_dbconn, bhh, &contract_identifier,
        //                                                                "(some (get-exotic-data-info u3))");
        //         eprintln!("{}", serde_json::to_string(&res).unwrap());
        //
        //         assert_eq!(result_data, expected_data);
        //
        //         // now, let's use a query string to get data _with_ a proof
        //         let path = format!("{}/v2/map_entry/{}/{}/{}?proof=1",
        //                            &http_origin, &contract_addr, "get-info", "block-data");
        //
        //         let key: Value = TupleData::from_data(vec![("height".into(), Value::UInt(3))])
        //             .unwrap().into();
        //
        //         eprintln!("Test: POST {}", path);
        //         let res = client.post(&path)
        //             .json(&key.serialize())
        //             .send()
        //             .unwrap().json::<HashMap<String, String>>().unwrap();
        //
        //         assert!(res.get("proof").is_some());
        //         let result_data = Value::try_deserialize_hex_untyped(&res["data"][2..]).unwrap();
        //         let expected_data = chain_state.clarity_eval_read_only(burn_dbconn, bhh, &contract_identifier,
        //                                                                "(some (get-exotic-data-info u3))");
        //         eprintln!("{}", serde_json::to_string(&res).unwrap());
        //
        //         assert_eq!(result_data, expected_data);
        //
        //         // account with a nonce entry + a balance entry
        //         let path = format!("{}/v2/accounts/{}",
        //                            &http_origin, &sender_addr);
        //         eprintln!("Test: GET {}", path);
        //         let res = client.get(&path).send().unwrap().json::<AccountEntryResponse>().unwrap();
        //         assert_eq!(u128::from_str_radix(&res.balance[2..], 16).unwrap(), 99860);
        //         assert_eq!(res.nonce, 4);
        //         assert!(res.nonce_proof.is_some());
        //         assert!(res.balance_proof.is_some());
        //
        //         // account with a nonce entry but not a balance entry
        //         let path = format!("{}/v2/accounts/{}",
        //                            &http_origin, &contract_addr);
        //         eprintln!("Test: GET {}", path);
        //         let res = client.get(&path).send().unwrap().json::<AccountEntryResponse>().unwrap();
        //         assert_eq!(u128::from_str_radix(&res.balance[2..], 16).unwrap(), 960);
        //         assert_eq!(res.nonce, 4);
        //         assert!(res.nonce_proof.is_some());
        //         assert!(res.balance_proof.is_some());
        //
        //         // account with a balance entry but not a nonce entry
        //         let path = format!("{}/v2/accounts/{}",
        //                            &http_origin, ADDR_4);
        //         eprintln!("Test: GET {}", path);
        //         let res = client.get(&path).send().unwrap().json::<AccountEntryResponse>().unwrap();
        //         assert_eq!(u128::from_str_radix(&res.balance[2..], 16).unwrap(), 400);
        //         assert_eq!(res.nonce, 0);
        //         assert!(res.nonce_proof.is_some());
        //         assert!(res.balance_proof.is_some());
        //
        //         // account with neither!
        //         let path = format!("{}/v2/accounts/{}.get-info",
        //                            &http_origin, &contract_addr);
        //         eprintln!("Test: GET {}", path);
        //         let res = client.get(&path).send().unwrap().json::<AccountEntryResponse>().unwrap();
        //         assert_eq!(u128::from_str_radix(&res.balance[2..], 16).unwrap(), 0);
        //         assert_eq!(res.nonce, 0);
        //         assert!(res.nonce_proof.is_some());
        //         assert!(res.balance_proof.is_some());
        //
        //         let path = format!("{}/v2/accounts/{}?proof=0",
        //                            &http_origin, ADDR_4);
        //         eprintln!("Test: GET {}", path);
        //         let res = client.get(&path).send().unwrap().json::<AccountEntryResponse>().unwrap();
        //         assert_eq!(u128::from_str_radix(&res.balance[2..], 16).unwrap(), 400);
        //         assert_eq!(res.nonce, 0);
        //         assert!(res.nonce_proof.is_none());
        //         assert!(res.balance_proof.is_none());
        //
        //         let path = format!("{}/v2/accounts/{}?proof=1",
        //                            &http_origin, ADDR_4);
        //         eprintln!("Test: GET {}", path);
        //         let res = client.get(&path).send().unwrap().json::<AccountEntryResponse>().unwrap();
        //         assert_eq!(u128::from_str_radix(&res.balance[2..], 16).unwrap(), 400);
        //         assert_eq!(res.nonce, 0);
        //         assert!(res.nonce_proof.is_some());
        //         assert!(res.balance_proof.is_some());
        //
        //         // let's try getting the transfer cost
        //         let path = format!("{}/v2/fees/transfer", &http_origin);
        //         eprintln!("Test: GET {}", path);
        //         let res = client.get(&path).send().unwrap().json::<u64>().unwrap();
        //         assert!(res > 0);
        //
        //         // let's get a contract ABI
        //
        //         let path = format!("{}/v2/contracts/interface/{}/{}", &http_origin, &contract_addr, "get-info");
        //         eprintln!("Test: GET {}", path);
        //         let res = client.get(&path).send().unwrap().json::<ContractInterface>().unwrap();
        //
        //         let contract_analysis = mem_type_check(GET_INFO_CONTRACT, ClarityVersion::Clarity2, StacksEpochId::Epoch21).unwrap().1;
        //         let expected_interface = build_contract_interface(&contract_analysis);
        //
        //         eprintln!("{}", serde_json::to_string(&expected_interface).unwrap());
        //
        //         assert_eq!(res, expected_interface);
        //
        //         // a missing one?
        //
        //         let path = format!("{}/v2/contracts/interface/{}/{}", &http_origin, &contract_addr, "not-there");
        //         eprintln!("Test: GET {}", path);
        //         assert_eq!(client.get(&path).send().unwrap().status(), 404);
        //
        //         // let's get a contract SRC
        //
        //         let path = format!("{}/v2/contracts/source/{}/{}", &http_origin, &contract_addr, "get-info");
        //         eprintln!("Test: GET {}", path);
        //         let res = client.get(&path).send().unwrap().json::<ContractSrcResponse>().unwrap();
        //
        //         assert_eq!(res.source, GET_INFO_CONTRACT);
        //         assert_eq!(res.publish_height, 2);
        //         assert!(res.marf_proof.is_some());
        //
        //
        //         let path = format!("{}/v2/contracts/source/{}/{}?proof=0", &http_origin, &contract_addr, "get-info");
        //         eprintln!("Test: GET {}", path);
        //         let res = client.get(&path).send().unwrap().json::<ContractSrcResponse>().unwrap();
        //
        //         assert_eq!(res.source, GET_INFO_CONTRACT);
        //         assert_eq!(res.publish_height, 2);
        //         assert!(res.marf_proof.is_none());
        //
        //         // a missing one?
        //
        //         let path = format!("{}/v2/contracts/source/{}/{}", &http_origin, &contract_addr, "not-there");
        //         eprintln!("Test: GET {}", path);
        //         assert_eq!(client.get(&path).send().unwrap().status(), 404);
        //
        //
        //         // how about a read-only function call!
        //         let path = format!("{}/v2/contracts/call-read/{}/{}/{}", &http_origin, &contract_addr, "get-info", "get-exotic-data-info");
        //         eprintln!("Test: POST {}", path);
        //
        //         let body = CallReadOnlyRequestBody {
        //             sender: "'SP139Q3N9RXCJCD1XVA4N5RYWQ5K9XQ0T9PKQ8EE5".into(),
        //             sponsor: None,
        //             arguments: vec![Value::UInt(3).serialize()]
        //         };
        //
        //         let res = client.post(&path)
        //             .json(&body)
        //             .send()
        //             .unwrap().json::<serde_json::Value>().unwrap();
        //         assert!(res.get("cause").is_none());
        //         assert!(res["okay"].as_bool().unwrap());
        //
        //         let result_data = Value::try_deserialize_hex_untyped(&res["result"].as_str().unwrap()[2..]).unwrap();
        //         let expected_data = chain_state.clarity_eval_read_only(burn_dbconn, bhh, &contract_identifier,
        //                                                                "(get-exotic-data-info u3)");
        //         assert_eq!(result_data, expected_data);
        //
        //         // how about a non read-only function call which does not modify anything
        //         let path = format!("{}/v2/contracts/call-read/{}/{}/{}", &http_origin, &contract_addr, "main", "public-no-write");
        //         eprintln!("Test: POST {}", path);
        //
        //         let body = CallReadOnlyRequestBody {
        //             sender: "'SP139Q3N9RXCJCD1XVA4N5RYWQ5K9XQ0T9PKQ8EE5".into(),
        //             sponsor: None,
        //             arguments: vec![]
        //         };
        //
        //         let res = client.post(&path)
        //             .json(&body)
        //             .send()
        //             .unwrap().json::<serde_json::Value>().unwrap();
        //         assert!(res.get("cause").is_none());
        //         assert!(res["okay"].as_bool().unwrap());
        //
        //         let result_data = Value::try_deserialize_hex_untyped(&res["result"].as_str().unwrap()[2..]).unwrap();
        //         let expected_data = Value::Response(ResponseData {
        //             committed: true,
        //             data: Box::new(Value::Response(ResponseData {
        //                 committed: true,
        //                 data: Box::new(Value::UInt(0))
        //             }))
        //         });
        //         assert_eq!(result_data, expected_data);
        //
        //         // how about a non read-only function call which does modify something and should fail
        //         let path = format!("{}/v2/contracts/call-read/{}/{}/{}", &http_origin, &contract_addr, "main", "public-write");
        //         eprintln!("Test: POST {}", path);
        //
        //         let body = CallReadOnlyRequestBody {
        //             sender: "'SP139Q3N9RXCJCD1XVA4N5RYWQ5K9XQ0T9PKQ8EE5".into(),
        //             sponsor: None,
        //             arguments: vec![]
        //         };
        //
        //         let res = client.post(&path)
        //             .json(&body)
        //             .send()
        //             .unwrap().json::<serde_json::Value>().unwrap();
        //         assert!(res.get("cause").is_some());
        //         assert!(!res["okay"].as_bool().unwrap());
        //         assert!(res["cause"].as_str().unwrap().contains("NotReadOnly"));
        //
        //         // let's try a call with a url-encoded string.
        //         let path = format!("{}/v2/contracts/call-read/{}/{}/{}", &http_origin, &contract_addr, "get-info",
        //                            "get-exotic-data-info%3F");
        //         eprintln!("Test: POST {}", path);
        //
        //         let body = CallReadOnlyRequestBody {
        //             sender: "'SP139Q3N9RXCJCD1XVA4N5RYWQ5K9XQ0T9PKQ8EE5".into(),
        //             sponsor: None,
        //             arguments: vec![Value::UInt(3).serialize()]
        //         };
        //
        //         let res = client.post(&path)
        //             .json(&body)
        //             .send()
        //             .unwrap()
        //             .json::<serde_json::Value>().unwrap();
        //         assert!(res.get("cause").is_none());
        //         assert!(res["okay"].as_bool().unwrap());
        //
        //         let result_data = Value::try_deserialize_hex_untyped(&res["result"].as_str().unwrap()[2..]).unwrap();
        //         let expected_data = chain_state.clarity_eval_read_only(burn_dbconn, bhh, &contract_identifier,
        //                                                                "(get-exotic-data-info? u3)");
        //         assert_eq!(result_data, expected_data);
        //
        //         // let's have a runtime error!
        //         let path = format!("{}/v2/contracts/call-read/{}/{}/{}", &http_origin, &contract_addr, "get-info", "get-exotic-data-info");
        //         eprintln!("Test: POST {}", path);
        //
        //         let body = CallReadOnlyRequestBody {
        //             sender: "'SP139Q3N9RXCJCD1XVA4N5RYWQ5K9XQ0T9PKQ8EE5".into(),
        //             sponsor: None,
        //             arguments: vec![Value::UInt(100).serialize()]
        //         };
        //
        //         let res = client.post(&path)
        //             .json(&body)
        //             .send()
        //             .unwrap().json::<serde_json::Value>().unwrap();
        //
        //         assert!(res.get("result").is_none());
        //         assert!(!res["okay"].as_bool().unwrap());
        //         assert!(res["cause"].as_str().unwrap().contains("UnwrapFailure"));
        //
        //         // let's have a runtime error!
        //         let path = format!("{}/v2/contracts/call-read/{}/{}/{}", &http_origin, &contract_addr, "get-info", "update-info");
        //         eprintln!("Test: POST {}", path);
        //
        //         let body = CallReadOnlyRequestBody {
        //             sender: "'SP139Q3N9RXCJCD1XVA4N5RYWQ5K9XQ0T9PKQ8EE5".into(),
        //             sponsor: None,
        //             arguments: vec![]
        //         };
        //
        //         let res = client.post(&path)
        //             .json(&body)
        //             .send()
        //             .unwrap().json::<serde_json::Value>().unwrap();
        //
        //         eprintln!("{:#?}", res["cause"].as_str().unwrap());
        //         assert!(res.get("result").is_none());
        //         assert!(!res["okay"].as_bool().unwrap());
        //         assert!(res["cause"].as_str().unwrap().contains("NotReadOnly"));
        //
        //         // let's submit a valid transaction!
        //         let spender_sk = StacksPrivateKey::from_hex(SK_3).unwrap();
        //         let path = format!("{}/v2/transactions", &http_origin);
        //         eprintln!("Test: POST {} (valid)", path);
        //
        //         // tx_xfer is 180 bytes long
        //         let tx_xfer = make_stacks_transfer(&spender_sk, round.into(), 200,
        //                                            &StacksAddress::from_string(ADDR_4).unwrap().into(), 123);
        //
        //         let res: String = client.post(&path)
        //             .header("Content-Type", "application/octet-stream")
        //             .body(tx_xfer.clone())
        //             .send()
        //             .unwrap()
        //             .json()
        //             .unwrap();
        //
        //         assert_eq!(res, format!("{}", StacksTransaction::consensus_deserialize(&mut &tx_xfer[..]).unwrap().txid()));
        //
        //         // let's test a posttransaction call that fails to deserialize,
        //         let tx_hex = "80800000000400f942874ce525e87f21bbe8c121b12fac831d02f4000000000000000000000000000003e80001031734446f0870af42bb0cafad27f405e5d9eba441375eada8607a802b875fbb7ba7c4da3474f2bfd76851fb6314a48fe98b57440b8ccec6c9b8362c843a89f303020000000001047465737400000007282b2031203129";
        //         let tx_xfer_invalid = hex_bytes(tx_hex).unwrap();
        //
        //         let res = client.post(&path)
        //             .header("Content-Type", "application/octet-stream")
        //             .body(tx_xfer_invalid.clone())
        //             .send()
        //             .unwrap().json::<serde_json::Value>().unwrap();
        //
        //         eprintln!("{}", res);
        //         assert_eq!(res.get("error").unwrap().as_str().unwrap(), "transaction rejected");
        //         assert!(res.get("reason").is_some());
        //
        //         // let's submit an invalid transaction!
        //         let path = format!("{}/v2/transactions", &http_origin);
        //         eprintln!("Test: POST {} (invalid)", path);
        //
        //         // tx_xfer_invalid is 180 bytes long
        //         let tx_xfer_invalid = make_stacks_transfer(&spender_sk, (round + 30).into(), 200,     // bad nonce
        //                                                    &StacksAddress::from_string(ADDR_4).unwrap().into(), 456);
        //
        //         let tx_xfer_invalid_tx = StacksTransaction::consensus_deserialize(&mut &tx_xfer_invalid[..]).unwrap();
        //
        //         let res = client.post(&path)
        //             .header("Content-Type", "application/octet-stream")
        //             .body(tx_xfer_invalid.clone())
        //             .send()
        //             .unwrap()
        //             .json::<serde_json::Value>()
        //             .unwrap();
        //
        //         eprintln!("{}", res);
        //         assert_eq!(res.get("txid").unwrap().as_str().unwrap(), format!("{}", tx_xfer_invalid_tx.txid()));
        //         assert_eq!(res.get("error").unwrap().as_str().unwrap(), "transaction rejected");
        //         assert!(res.get("reason").is_some());
        //
        //         // testing /v2/trait/<contract info>/<trait info>
        //         // trait does not exist
        //         let path = format!("{}/v2/traits/{}/{}/{}/{}/{}", &http_origin, &contract_addr, "get-info", &contract_addr, "get-info", "dummy-trait");
        //         eprintln!("Test: GET {}", path);
        //         assert_eq!(client.get(&path).send().unwrap().status(), 404);
        //
        //         // explicit trait compliance
        //         let path = format!("{}/v2/traits/{}/{}/{}/{}/{}", &http_origin, &contract_addr, "impl-trait-contract", &contract_addr, "get-info",  "trait-1");
        //         let res = client.get(&path).send().unwrap().json::<GetIsTraitImplementedResponse>().unwrap();
        //         eprintln!("Test: GET {}", path);
        //         assert!(res.is_implemented);
        //
        //         // No trait found
        //         let path = format!("{}/v2/traits/{}/{}/{}/{}/{}", &http_origin, &contract_addr, "impl-trait-contract", &contract_addr, "get-info", "trait-4");
        //         eprintln!("Test: GET {}", path);
        //         assert_eq!(client.get(&path).send().unwrap().status(), 404);
        //
        //         // implicit trait compliance
        //         let path = format!("{}/v2/traits/{}/{}/{}/{}/{}", &http_origin, &contract_addr, "impl-trait-contract", &contract_addr, "get-info", "trait-2");
        //         let res = client.get(&path).send().unwrap().json::<GetIsTraitImplementedResponse>().unwrap();
        //         eprintln!("Test: GET {}", path);
        //         assert!(res.is_implemented);
        //
        //
        //         // invalid trait compliance
        //         let path = format!("{}/v2/traits/{}/{}/{}/{}/{}", &http_origin, &contract_addr, "impl-trait-contract", &contract_addr, "get-info", "trait-3");
        //         let res = client.get(&path).send().unwrap().json::<GetIsTraitImplementedResponse>().unwrap();
        //         eprintln!("Test: GET {}", path);
        //         assert!(!res.is_implemented);
        //
        //         // test query parameters for v2/trait endpoint
        //         // evaluate check for explicit compliance against the chain tip of the first block (contract DNE at that block)
        //
        //         // Recover the stored tip
        //         let tmppath = "/tmp/integration_test_get_info-old-tip";
        //         use std::fs;
        //         use std::io::Read;
        //         let mut f = fs::File::open(&tmppath).unwrap();
        //         let mut buf = vec![];
        //         f.read_to_end(&mut buf).unwrap();
        //         let old_tip = StacksBlockId::consensus_deserialize(&mut &buf[..]).unwrap();
        //
        //         let path = format!("{}/v2/traits/{}/{}/{}/{}/{}?tip={}", &http_origin, &contract_addr, "impl-trait-contract", &contract_addr, "get-info",  "trait-1", &old_tip);
        //
        //         let res = client.get(&path).send().unwrap();
        //         eprintln!("Test: GET {}", path);
        //         assert_eq!(res.text().unwrap(), "No contract analysis found or trait definition not found");
        //
        //         // evaluate check for explicit compliance where tip is the chain tip of the first block (contract DNE at that block), but tip is "latest"
        //         let path = format!("{}/v2/traits/{}/{}/{}/{}/{}?tip=latest", &http_origin, &contract_addr, "impl-trait-contract", &contract_addr, "get-info",  "trait-1");
        //         let res = client.get(&path).send().unwrap().json::<GetIsTraitImplementedResponse>().unwrap();
        //         eprintln!("Test: GET {}", path);
        //         assert!(res.is_implemented);
        //
        //         // perform some tests of the fee rate interface
        //         let path = format!("{}/v2/fees/transaction", &http_origin);
        //
        //         let tx_payload =
        //             TransactionPayload::TokenTransfer(contract_addr.clone().into(), 10_000_000, TokenTransferMemo([0; 34]));
        //
        //         let payload_data = tx_payload.serialize_to_vec();
        //         let payload_hex = format!("0x{}", to_hex(&payload_data));
        //
        //         eprintln!("Test: POST {}", path);
        //
        //         let body = json!({ "transaction_payload": payload_hex.clone() });
        //
        //         let res = client.post(&path)
        //             .json(&body)
        //             .send()
        //             .expect("Should be able to post")
        //             .json::<serde_json::Value>()
        //             .expect("Failed to parse result into JSON");
        //
        //         eprintln!("{}", res);
        //
        //         // destruct the json result
        //         //  estimated_cost for transfers should be 0 -- their cost is just in their length
        //         let estimated_cost = res.get("estimated_cost").expect("Response should have estimated_cost field");
        //         assert_eq!(estimated_cost.get("read_count").unwrap().as_u64().unwrap(), 0);
        //         assert_eq!(estimated_cost.get("read_length").unwrap().as_u64().unwrap(), 0);
        //         assert_eq!(estimated_cost.get("write_count").unwrap().as_u64().unwrap(), 0);
        //         assert_eq!(estimated_cost.get("write_length").unwrap().as_u64().unwrap(), 0);
        //         assert_eq!(estimated_cost.get("runtime").unwrap().as_u64().unwrap(), 0);
        //
        //         // the estimated scalar should still be non-zero, because the length of the tx goes into this field.
        //         assert!(res.get("estimated_cost_scalar").unwrap().as_u64().unwrap() > 0);
        //
        //         let estimations = res.get("estimations").expect("Should have an estimations field")
        //             .as_array()
        //             .expect("Fees should be array");
        //
        //         let estimated_fee_rates: Vec<_> = estimations
        //             .iter()
        //             .map(|x| x.get("fee_rate").expect("Should have fee_rate field"))
        //             .collect();
        //         let estimated_fees: Vec<_> = estimations
        //             .iter()
        //             .map(|x| x.get("fee").expect("Should have fee field"))
        //             .collect();
        //
        //         assert!(estimated_fee_rates.len() == 3, "Fee rates should be length 3 array");
        //         assert!(estimated_fees.len() == 3, "Fees should be length 3 array");
        //
        //         let tx_payload = TransactionPayload::from(TransactionContractCall {
        //             address: contract_addr.clone(),
        //             contract_name: "get-info".into(),
        //             function_name: "update-info".into(),
        //             function_args: vec![],
        //         });
        //
        //         let payload_data = tx_payload.serialize_to_vec();
        //         let payload_hex = to_hex(&payload_data);
        //
        //         eprintln!("Test: POST {}", path);
        //
        //         let body = json!({ "transaction_payload": payload_hex.clone() });
        //
        //         let res = client.post(&path)
        //             .json(&body)
        //             .send()
        //             .expect("Should be able to post")
        //             .json::<serde_json::Value>()
        //             .expect("Failed to parse result into JSON");
        //
        //         eprintln!("{}", res);
        //
        //         // destruct the json result
        //         //  estimated_cost for transfers should be non-zero
        //         let estimated_cost = res.get("estimated_cost").expect("Response should have estimated_cost field");
        //         assert!(estimated_cost.get("read_count").unwrap().as_u64().unwrap() > 0);
        //         assert!(estimated_cost.get("read_length").unwrap().as_u64().unwrap() > 0);
        //         assert!(estimated_cost.get("write_count").unwrap().as_u64().unwrap() > 0);
        //         assert!(estimated_cost.get("write_length").unwrap().as_u64().unwrap() > 0);
        //         assert!(estimated_cost.get("runtime").unwrap().as_u64().unwrap() > 0);
        //
        //         let estimated_cost_scalar = res.get("estimated_cost_scalar").unwrap().as_u64().unwrap();
        //         assert!(estimated_cost_scalar > 0);
        //
        //         let estimations = res.get("estimations").expect("Should have an estimations field")
        //             .as_array()
        //             .expect("Fees should be array");
        //
        //         let estimated_fee_rates: Vec<_> = estimations
        //             .iter()
        //             .map(|x| x.get("fee_rate").expect("Should have fee_rate field"))
        //             .collect();
        //         let estimated_fees: Vec<_> = estimations
        //             .iter()
        //             .map(|x| x.get("fee").expect("Should have fee field"))
        //             .collect();
        //
        //         assert!(estimated_fee_rates.len() == 3, "Fee rates should be length 3 array");
        //         assert!(estimated_fees.len() == 3, "Fees should be length 3 array");
        //
        //         let tx_payload = TransactionPayload::from(TransactionContractCall {
        //             address: contract_addr.clone(),
        //             contract_name: "get-info".into(),
        //             function_name: "update-info".into(),
        //             function_args: vec![],
        //         });
        //
        //         let payload_data = tx_payload.serialize_to_vec();
        //         let payload_hex = to_hex(&payload_data);
        //
        //         let estimated_len = 1550;
        //         let body = json!({ "transaction_payload": payload_hex.clone(), "estimated_len": estimated_len });
        //         info!("POST body\n {}", body);
        //
        //         let res = client.post(&path)
        //             .json(&body)
        //             .send()
        //             .expect("Should be able to post")
        //             .json::<serde_json::Value>()
        //             .expect("Failed to parse result into JSON");
        //
        //         info!("{}", res);
        //
        //         // destruct the json result
        //         //  estimated_cost for transfers should be non-zero
        //         let estimated_cost = res.get("estimated_cost").expect("Response should have estimated_cost field");
        //         assert!(estimated_cost.get("read_count").unwrap().as_u64().unwrap() > 0);
        //         assert!(estimated_cost.get("read_length").unwrap().as_u64().unwrap() > 0);
        //         assert!(estimated_cost.get("write_count").unwrap().as_u64().unwrap() > 0);
        //         assert!(estimated_cost.get("write_length").unwrap().as_u64().unwrap() > 0);
        //         assert!(estimated_cost.get("runtime").unwrap().as_u64().unwrap() > 0);
        //
        //         let new_estimated_cost_scalar = res.get("estimated_cost_scalar").unwrap().as_u64().unwrap();
        //         assert!(estimated_cost_scalar > 0);
        //         assert!(new_estimated_cost_scalar > estimated_cost_scalar, "New scalar estimate should be higher because of the tx length increase");
        //
        //         let new_estimations = res.get("estimations").expect("Should have an estimations field")
        //             .as_array()
        //             .expect("Fees should be array");
        //
        //         let new_estimated_fees: Vec<_> = new_estimations
        //             .iter()
        //             .map(|x| x.get("fee").expect("Should have fee field"))
        //             .collect();
        //
        //         let minimum_relay_fee = estimated_len * MINIMUM_TX_FEE_RATE_PER_BYTE;
        //
        //         assert!(new_estimated_fees[2].as_u64().unwrap() >= estimated_fees[2].as_u64().unwrap(),
        //                 "Supplying an estimated tx length should increase the estimated fees");
        //         assert!(new_estimated_fees[0].as_u64().unwrap() >= estimated_fees[0].as_u64().unwrap(),
        //                 "Supplying an estimated tx length should increase the estimated fees");
        //         assert!(new_estimated_fees[1].as_u64().unwrap() >= estimated_fees[1].as_u64().unwrap(),
        //                 "Supplying an estimated tx length should increase the estimated fees");
        //         for estimate in new_estimated_fees.iter() {
        //             assert!(estimate.as_u64().unwrap() >= minimum_relay_fee,
        //                     "The estimated fees must always be greater than minimum_relay_fee");
        //         }
        //     },
        //     _ => {},
        // }
    });

    run_loop.start(num_rounds).unwrap();
}