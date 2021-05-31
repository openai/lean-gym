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
lean --run src/repl.lean \
    intermediate_field.adjoin.range_algebra_map_subset \
    "intermediate_field intermediate_field finite_dimensional polynomial"
```

Starts the REPL setting the environment and tactic state at declaration
`intermediate_field.adjoin.range_algebra_map_subset` opening the namespaces
passed as second argument.

Once started a `REPLState: string -> tactic_state` is maintained storing all the
tactic states visited. The `REPLState` is initialized with the initial tactic
state which is returned at initialization:

```
$ lean --run src/repl.lean nat.prime_iff_prime_int ""
{"error":null,id:"919387232","tactic_state":"⊢ ∀ {p : ℕ}, nat.prime p ↔ prime ↑p"}
```

The `run_tac` command applies a tactic string to the tactic state denoted by the
provided identifier. A new tactic state (with identifier) is returned on succes,
an error message otherwise.

```
$ lean --run src/repl.lean int.prime.dvd_mul ""      
{"error":null,"id":"2137499499","tactic_state":"⊢ ∀ {m n : ℤ} {p : ℕ}, nat.prime p → ↑p ∣ m * n → p ∣ m.nat_abs ∨ p ∣ n.nat_abs"}
["run_tac", "2137499499", "intros"]
{"error":null,"id":"6701217918","tactic_state":"m n : ℤ,\tp : ℕ,\thp : nat.prime p,\th : ↑p ∣ m * n\t⊢ p ∣ m.nat_abs ∨ p ∣ n.nat_abs"}
["run_tac", "6701217918", "apply (nat.prime.dvd_mul hp).mp"]
{"error":null,"id":"7348884859","tactic_state":"m n : ℤ,\tp : ℕ,\thp : nat.prime p,\th : ↑p ∣ m * n\t⊢ p ∣ m.nat_abs * n.nat_abs"}
["run_tac", "7348884859", "rw ← int.nat_abs_mul"]
{"error":null,"id":"8420007981","tactic_state":"m n : ℤ,\tp : ℕ,\thp : nat.prime p,\th : ↑p ∣ m * n\t⊢ p ∣ (m * n).nat_abs"}
["run_tac", "8420007981", "simp"]
{"error":"run_tac_failed: pos=(some ⟨1, 2⟩) msg=simplify tactic failed to simplify","id":null,"tactic_state":null}
["run_tac", "8420007981", "exact int.coe_nat_dvd_left.mp h"]
{"error":null,"id":"0","tactic_state":"no goals"}
```

## Declaration names

Declaration names and open namespaces as recorded by [lean_proof_recording](https://github.com/jasonrute/lean-proof-recording-public) are available in the `data/` directory.