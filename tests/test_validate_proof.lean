import util.tactic
import basic.conjecture_tactics

meta def should_fail
  (u v : ℕ+)
  (h₀ : 100 ∣ (14*u - 46))
  (h₁ : 100 ∣ (14*v - 46))
  (h₂ : u < 50)
  (h₃ : v < 100)
  (h₄ : 50 < v) :
  ((u + v):ℕ) / 2 = 64 :=
begin
  revert h₄,
  contrapose h₃,
  intro hn,
  exact not_lt_of_lt hn undefined,
end

meta def should_succeed : true := by trivial

/--
 Tests the  register_conjecture_pf tactic 
-/
meta def test_register_conjecture_pf : tactic unit := do { 
  let pf_term : expr := `(trivial),
  ts ← tactic.read, 
  ⟨nm ,new_ts⟩ ← register_conjecture_pf pf_term ts,
  tactic.write new_ts, 
  env ← tactic.get_env, 
  env.get nm *> tactic.trace "register_conjecture OK"  -- succeeds iff `nm` is inside `env` 
  }

/--
 Tests the close_old_ts_top_goal_using_conjecture tactic
-/
meta def test_close_old_ts_top_goal_using_conjecture (pf_term : expr) : tactic unit  := do {
⟨ts_old, ts_narrowed⟩ ← add_conjecture "h" "false",
tactic.write ts_old, -- ts_old has two goals ⊢false and ⊢true

⟨nm ,new_ts⟩ ← register_conjecture_pf pf_term ts_narrowed,
final_ts ← close_old_ts_top_goal_using_conjecture ts_old nm  new_ts,
tactic.write final_ts,
tactic.get_goal *> tactic.trace "close_old_ts_top_goal_using_conjecture OK"  -- succeeds if new tactic state only has one goal
}

namespace dummy_ns
/--
  Meant to test all conjecture tactics  proves that 0 = 1 -> 0 = 2 by conjecturing that 0 = 1 -> false and then using false.elim
-/
  meta def test_all_conjecture_tactics: tactic unit := do {
    ⟨ts_old, ts_narrowed⟩ ← add_conjecture "h" "0 = 1 -> false",

    let pf_term : expr := `(λ h, @nat.no_confusion false 0 1 h) ,
    ⟨nm ,new_ts⟩ ← register_conjecture_pf pf_term ts_narrowed,

    final_ts ← close_old_ts_top_goal_using_conjecture ts_old nm  new_ts,
    tactic.write final_ts,
    pure ()
  }

  lemma dummy_lemma : (0 = 1) → (0 = 2) :=
  begin
    test_all_conjecture_tactics,
    intro h',
    exact false.elim (h h'),
  end

end dummy_ns

meta def main : io unit := io.run_tactic'' $ do {
  (tactic.guard_undefined `(undefined : ℕ) <|> tactic.trace "OK"),
  (tactic.guard_sorry `(sorry : ℕ) <|> tactic.trace "OK"),
  (validate_decl `should_fail) <|> tactic.trace "OK",
  validate_decl `should_succeed *> tactic.trace "OK"
}



