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
[success] 919387232
⊢ ∀ {p : ℕ}, nat.prime p ↔ prime ↑p
[end]
```

The `run_tac` command applies a tactic string to the tactic state denoted by the
provided identifier. A new tactic state (with identifier) is returned on succes,
an error message otherwise.

```
$ lean --run src/repl.lean int.prime.dvd_mul ""      
[success] 1258804314
⊢ ∀ {m n : ℤ} {p : ℕ}, nat.prime p → ↑p ∣ m * n → p ∣ m.nat_abs ∨ p ∣ n.nat_abs
[end]

["run_tac", "1258804314", "intros"]
[success] 4630108822
m n : ℤ,
p : ℕ,
hp : nat.prime p,
h : ↑p ∣ m * n
⊢ p ∣ m.nat_abs ∨ p ∣ n.nat_abs
[end]

["run_tac", "4630108822", "apply (nat.prime.dvd_mul hp).mp"]
[success] 5032220362
m n : ℤ,
p : ℕ,
hp : nat.prime p,
h : ↑p ∣ m * n
⊢ p ∣ m.nat_abs * n.nat_abs
[end]

["run_tac", "5032220362", "rw ← int.nat_abs_mul"]
[success] 5026170610
m n : ℤ,
p : ℕ,
hp : nat.prime p,
h : ↑p ∣ m * n
⊢ p ∣ (m * n).nat_abs
[end]

["run_tac", "5026170610", "simp"]
[error] run_tac_failed: pos=(some ⟨1, 2⟩) msg=simplify tactic failed to simplify
[end]

["run_tac", "5026170610", "exact int.coe_nat_dvd_left.mp h"]
[success] 0
no goals
[end]

```
