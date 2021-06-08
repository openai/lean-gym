# lean-gym

This repository lets you interact with Lean through a REPL. It builds and
depends on [lean-gptf](https://github.com/jesse-michael-han/lean-gptf).

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

["init_search", ["intermediate_field.adjoin.range_algebra_map_subset", "intermediate_field finite_dimensional polynomial"]]
{"error":null,"search_id":"0","tactic_state":"⊢ ∀ (F : Type u_1) [_inst_1 : field F] {E : Type u_2} [_inst_2 : field E] [_inst_3 : algebra F E] (S : set E),\tset.range ⇑(algebra_map F E) ⊆ ↑(intermediate_field.adjoin F S)","tactic_state_id":"0"}

["init_search", ["int.prime.dvd_mul", ""]]
{"error":null,"search_id":"1","tactic_state":"⊢ ∀ {m n : ℤ} {p : ℕ}, nat.prime p → ↑p ∣ m * n → p ∣ m.nat_abs ∨ p ∣ n.nat_abs","tactic_state_id":"0"}

["run_tac",["0","0","intros"]]
{"error":null,"search_id":"0","tactic_state":"F : Type u_1,\t_inst_1 : field F,\tE : Type u_2,\t_inst_2 : field E,\t_inst_3 : algebra F E,\tS : set E\t⊢ set.range ⇑(algebra_map F E) ⊆ ↑(intermediate_field.adjoin F S)","tactic_state_id":"1"}

["run_tac",["1","0","intros"]]
{"error":null,"search_id":"1","tactic_state":"m n : ℤ,\tp : ℕ,\thp : nat.prime p,\th : ↑p ∣ m * n\t⊢ p ∣ m.nat_abs ∨ p ∣ n.nat_abs","tactic_state_id":"1"}

["run_tac",["1","1","apply (nat.prime.dvd_mul hp).mp"]]
{"error":null,"search_id":"1","tactic_state":"m n : ℤ,\tp : ℕ,\thp : nat.prime p,\th : ↑p ∣ m * n\t⊢ p ∣ m.nat_abs * n.nat_abs","tactic_state_id":"2"}

["run_tac",["1","2","rw ← int.nat_abs_mul"]]
{"error":null,"search_id":"1","tactic_state":"m n : ℤ,\tp : ℕ,\thp : nat.prime p,\th : ↑p ∣ m * n\t⊢ p ∣ (m * n).nat_abs","tactic_state_id":"3"}

["run_tac",["1","3","simp"]]
{"error":"run_tac_failed: pos=(some ⟨1, 2⟩) msg=simplify tactic failed to simplify","search_id":null,"tactic_state":null,"tactic_state_id":null}

["run_tac",["1","5","exact int.coe_nat_dvd_left.mp h"]]
{"error":"unknown_id: search_id=1 tactic_state_id=5","search_id":null,"tactic_state":null,"tactic_state_id":null}

["run_tac",["1","3","exact int.coe_nat_dvd_left.mp h"]]
{"error":null,"search_id":"1","tactic_state":"no goals","tactic_state_id":"4"}

["clear_search",["1"]]
{"error":null,"search_id":"1","tactic_state":null,"tactic_state_id":null}

["run_tac",["0","1","intros x hx,"]]
{"error":null,"search_id":"0","tactic_state":"F : Type u_1,\t_inst_1 : field F,\tE : Type u_2,\t_inst_2 : field E,\t_inst_3 : algebra F E,\tS : set E,\tx : E,\thx : x ∈ set.range ⇑(algebra_map F E)\t⊢ x ∈ ↑(intermediate_field.adjoin F S)","tactic_state_id":"2"}

["run_tac",["0","2","cases hx with f hf"]]
{"error":null,"search_id":"0","tactic_state":"F : Type u_1,\t_inst_1 : field F,\tE : Type u_2,\t_inst_2 : field E,\t_inst_3 : algebra F E,\tS : set E,\tx : E,\tf : F,\thf : ⇑(algebra_map F E) f = x\t⊢ x ∈ ↑(intermediate_field.adjoin F S)","tactic_state_id":"3"}

["run_tac",["0","3","rw ← hf"]]
{"error":null,"search_id":"0","tactic_state":"F : Type u_1,\t_inst_1 : field F,\tE : Type u_2,\t_inst_2 : field E,\t_inst_3 : algebra F E,\tS : set E,\tx : E,\tf : F,\thf : ⇑(algebra_map F E) f = x\t⊢ ⇑(algebra_map F E) f ∈ ↑(intermediate_field.adjoin F S)","tactic_state_id":"4"}

["run_tac",["0","4","exact adjoin.algebra_map_mem F S f"]]
{"error":null,"search_id":"0","tactic_state":"no goals","tactic_state_id":"5"}

["clear_search",["0"]]
{"error":null,"search_id":"0","tactic_state":null,"tactic_state_id":null}
```

## Declaration names

Declaration names and open namespaces as recorded by
[lean_proof_recording](https://github.com/jasonrute/lean-proof-recording-public)
are available in the `data/` directory to be used with the `init_search`
command.

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