# lean-gym

This repository lets you interact with Lean through a REPL. This repository heavily builds and
depends on [lean-gptf](https://github.com/jesse-michael-han/lean-gptf).

## Setup

```bash
# download pre-built binaries and build the project
bash ./scripts/setup.sh
```

## Usage

```bash
lean --run src/repl.lean
```

Starts a fresh REPL, returning an empty response object once it is ready.

Once started, the REPL accepts the following commands:
- `init_search`: takes a declaration name as well as a list of open namespaces
to initialize a search at the given declaration, returning the initial tactic
state (along with a fresh `search_id` and `tactic_state_id`).
- `run_tac`: takes a `search_id`, a `tactic_state_id` and a tactic to apply at
the tactic state denoted by the provided ids.
- `clear_search`: takes a `search_id` to clear all state related to a search.

```
$ lean --run src/repl.lean
{"error":null,"sid":null,"tactic_state":null,"tsid":null}
["init_search", ["intermediate_field.adjoin.range_algebra_map_subset", "intermediate_field finite_dimensional polynomial"]]
{"error":null,"sid":"0","tactic_state":"⊢ ∀ (F : Type u_1) [_inst_1 : field F] {E : Type u_2} [_inst_2 : field E] [_inst_3 : algebra F E] (S : set E),\tset.range ⇑(algebra_map F E) ⊆ ↑(intermediate_field.adjoin F S)","tsid":"0"}
["init_search", ["int.prime.dvd_mul", ""]]
{"error":null,"sid":"1","tactic_state":"⊢ ∀ {m n : ℤ} {p : ℕ}, nat.prime p → ↑p ∣ m * n → p ∣ m.nat_abs ∨ p ∣ n.nat_abs","tsid":"0"}
["run_tac",["0","0","intros"]]
{"error":null,"sid":"0","tactic_state":"F : Type u_1,\t_inst_1 : field F,\tE : Type u_2,\t_inst_2 : field E,\t_inst_3 : algebra F E,\tS : set E\t⊢ set.range ⇑(algebra_map F E) ⊆ ↑(intermediate_field.adjoin F S)","tsid":"1"}
["run_tac",["1","0","intros"]]
{"error":null,"sid":"1","tactic_state":"m n : ℤ,\tp : ℕ,\thp : nat.prime p,\th : ↑p ∣ m * n\t⊢ p ∣ m.nat_abs ∨ p ∣ n.nat_abs","tsid":"1"}
["run_tac",["1","1","apply (nat.prime.dvd_mul hp).mp"]]
{"error":null,"sid":"1","tactic_state":"m n : ℤ,\tp : ℕ,\thp : nat.prime p,\th : ↑p ∣ m * n\t⊢ p ∣ m.nat_abs * n.nat_abs","tsid":"2"}
["run_tac",["1","2","rw ← int.nat_abs_mul"]]
{"error":null,"sid":"1","tactic_state":"m n : ℤ,\tp : ℕ,\thp : nat.prime p,\th : ↑p ∣ m * n\t⊢ p ∣ (m * n).nat_abs","tsid":"3"}
["run_tac",["1","3","simp"]]
{"error":"run_tac_failed: pos=(some ⟨1, 2⟩) msg=simplify tactic failed to simplify","sid":null,"tactic_state":null,"tsid":null}
["run_tac",["1","5","exact int.coe_nat_dvd_left.mp h"]]
{"error":"unknown_id: sid=1 tsid=5","sid":null,"tactic_state":null,"tsid":null}
["run_tac",["1","3","exact int.coe_nat_dvd_left.mp h"]]
{"error":null,"sid":"1","tactic_state":"no goals","tsid":"4"}
["run_tac",["0","1","intros x hx,"]]
{"error":null,"sid":"0","tactic_state":"F : Type u_1,\t_inst_1 : field F,\tE : Type u_2,\t_inst_2 : field E,\t_inst_3 : algebra F E,\tS : set E,\tx : E,\thx : x ∈ set.range ⇑(algebra_map F E)\t⊢ x ∈ ↑(intermediate_field.adjoin F S)","tsid":"2"}
["run_tac",["0","2","cases hx with f hf"]]
{"error":null,"sid":"0","tactic_state":"F : Type u_1,\t_inst_1 : field F,\tE : Type u_2,\t_inst_2 : field E,\t_inst_3 : algebra F E,\tS : set E,\tx : E,\tf : F,\thf : ⇑(algebra_map F E) f = x\t⊢ x ∈ ↑(intermediate_field.adjoin F S)","tsid":"3"}
["run_tac",["0","3","rw ← hf"]]
{"error":null,"sid":"0","tactic_state":"F : Type u_1,\t_inst_1 : field F,\tE : Type u_2,\t_inst_2 : field E,\t_inst_3 : algebra F E,\tS : set E,\tx : E,\tf : F,\thf : ⇑(algebra_map F E) f = x\t⊢ ⇑(algebra_map F E) f ∈ ↑(intermediate_field.adjoin F S)","tsid":"4"}
["run_tac",["0","4","exact adjoin.algebra_map_mem F S f"]]
{"error":null,"sid":"0","tactic_state":"no goals","tsid":"5"}
```

## Declaration names

Declaration names and open namespaces as recorded by
[lean_proof_recording](https://github.com/jasonrute/lean-proof-recording-public)
are available in the `data/` directory to be used with the `init_search`
command.