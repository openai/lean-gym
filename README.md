# lean-gym

This repository lets you interact with Lean through a REPL.
See [Formal Mathematics Statement Curriculum Learning](https://arxiv.org/abs/2202.01344)
for a presentation of `lean-gym`.

## Setup

```bash
# Download pre-built binaries and build the project (targeting mathlib).
bash ./scripts/setup.sh
```

## Usage

```bash
lean --run src/repl.lean
```

Starts a fresh REPL. Once started, the REPL accepts the following commands:

- `init_search`: takes a declaration name as well as a list of open namespaces
to initialize a search at the given declaration opening the provided namespaces,
and returning the initial tactic state (along with a fresh `search_id` and
`tactic_state_id`).
- `run_tac`: takes a `search_id`, a `tactic_state_id` and a tactic to apply at
the tactic state denoted by the provided ids.
- `clear_search`: takes a `search_id` to clear all state related to a search.

The commands can be interleaved freely enabling the parallelization of multiple
proof searches against the same REPL.

```
$ lean --run src/repl.lean

["init_search", ["int.prime.dvd_mul", ""]]
{"error":null,"proof_steps":[],"search_id":"0","tactic_state":"⊢ ∀ {m n : ℤ} {p : ℕ}, nat.prime p → ↑p ∣ m * n → p ∣ m.nat_abs ∨ p ∣ n.nat_abs","tactic_state_id":"0"}

["run_tac",["0","0","intros"]]
{"error":null,"proof_steps":[],"search_id":"0","tactic_state":"m n : ℤ,\np : ℕ,\nhp : nat.prime p,\nh : ↑p ∣ m * n\n⊢ p ∣ m.nat_abs ∨ p ∣ n.nat_abs","tactic_state_id":"1"}

["run_tac",["0","1","apply (nat.prime.dvd_mul hp).mp"]]
{"error":null,"proof_steps":[],"search_id":"0","tactic_state":"m n : ℤ,\np : ℕ,\nhp : nat.prime p,\nh : ↑p ∣ m * n\n⊢ p ∣ m.nat_abs * n.nat_abs","tactic_state_id":"2"}

["run_tac",["0","2","rw ← int.nat_abs_mul"]]
{"error":null,"proof_steps":[],"search_id":"0","tactic_state":"m n : ℤ,\np : ℕ,\nhp : nat.prime p,\nh : ↑p ∣ m * n\n⊢ p ∣ (m * n).nat_abs","tactic_state_id":"3"}

["run_tac",["0","3","exact int.coe_nat_dvd_left.mp h"]]
{"error":null,"proof_steps":[],"search_id":"0","tactic_state":"no goals","tactic_state_id":"4"}
```

## Declaration names

Declaration names and open namespaces are available in the `data/` directory to be used with the
`init_search` command.

## Notes

The REPL is subject to crashes in rare cases. Empirically such crash happens no
more than ~0.01% of the time.

When a tactic state is reached with no left goals, some custom logic is run to check that the
resulting proof's type matches the top level goal type and does not rely on `sorry`. We also check
for the presence of `undefined` in the proof term. As an example, the following MiniF2F proofs will
safely fail with error `proof_validation_failed`.

```
["init_search", ["mathd_algebra_35", ""]]
["run_tac", ["0", "0", "intros"]]
["run_tac", ["0", "1", "sorry"]]
```

```
["init_search", ["induction_divisibility_3divnto3m2n", ""]]
["run_tac", ["0", "0", "intros"]]
["run_tac", ["0", "1", "rw [add_comm]"]]
["run_tac", ["0", "2", "have h3 : 1 * (n + 1) ≤ (n + 1)"]]
["run_tac", ["0", "3", "rw one_mul"]]
["run_tac", ["0", "4", "apply dvd_trans"]]
["run_tac", ["0", "5", "swap"]]
["run_tac", ["0", "6", "simp []"]]
```

```
["init_search", ["mathd_numbertheory_13", ""]]
["run_tac", ["0", "0", "intros u v hu hv hsum"]]
["run_tac", ["0", "1", "intro h"]]
["run_tac", ["0", "2", "contrapose h"]]
["run_tac", ["0", "3", "intro hn"]]
["run_tac", ["0", "4", "exact not_lt_of_lt hn undefined"]]
```
