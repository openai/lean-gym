/-
Copyright (c) 2022 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Daniel Selsam

Simple, barebones heuristic proof-minimization.
-/
import util.io
import data.list.basic
import util.tactic
import tactic.gptf.utils.util

meta def io.run_tac {α : Type} (ts : tactic_state) (tac : tactic α) : io α :=
  io.run_tactic'' (do tactic.write ts, tac)

meta def expr.mvar_id : expr → name
| (expr.mvar unique _ _) := unique
| _ := `error.not_an_mvar

meta def build_proof_trace (ts₀ : tactic_state) (steps : list (string × tactic_state)) : list (tactic_state × string × tactic_state) :=
  list.reverse $ prod.snd $ @list.foldl (tactic_state × list (tactic_state × string × tactic_state)) 
    (string × tactic_state) 
    (λ ⟨ts_prev, new_steps⟩ ⟨action, ts_next⟩, (ts_next, new_steps.cons (ts_prev, action, ts_next))) 
    (ts₀, []) 
    steps 

/--
Consider the following proof:
```
have h1 : ... := ...,
have h2 : ... h1 ... := ...,
have h3 : ... h1 ... := ...,
have h4 : ... h2 ... := ...,
exact h3
```
Here `h2` and `h4` can be safely removed. 

We detect removable `have`s by proceeding in reverse order.
For a given `have` statement, we can tell if it appears in the resulting proof
by checking the proof term in the metavariable context of the final tactic state.
-/

meta def strip_unused_haves (ts_final : tactic_state) (steps : list (tactic_state × string × tactic_state)) : io (list (tactic_state × string × tactic_state)) := do {
  ⟨bad_idx, bad_idx_num_goals⟩ ← steps.enum.reverse.mfirst (λ ⟨idx, ⟨ts1, action, ts2⟩⟩, do {
    if action.to_list.take 5 = "have ".to_list then do {
      gs1 ← io.run_tac ts1 tactic.get_goals,
      gs2 ← io.run_tac ts2 tactic.get_goals,
      if gs1.length + 1 = gs2.length ∧ gs1.drop 1 = gs2.drop 2 then do {
        -- `have` step without proof
        let goal_with_assumption := gs2.nth_le 1 sorry,
        assumption ← io.run_tac ts2 (do tactic.set_goals [goal_with_assumption], hs ← tactic.local_context, pure (hs.last sorry)),
        proof_of_goal_with_assumption ← io.run_tac ts_final (tactic.instantiate_mvars goal_with_assumption),
        if not (expr.occurs assumption proof_of_goal_with_assumption) then 
          pure (idx, gs1.length)
        else io.fail "`have` step is used"
      } 
      else io.fail "blah"
    }
    else
      io.fail "no haves"
    }
  ),

  num_goals_per_step : list ℕ ← steps.mmap (λ ⟨ts1, action, ts2⟩, io.run_tac ts1 (do gs ← tactic.get_goals, pure gs.length)),
  let resume_idx : ℕ := num_goals_per_step.enum.find_index (λ idx__num_goals, idx__num_goals.fst > bad_idx ∧ idx__num_goals.snd = bad_idx_num_goals),
  pure (steps.take bad_idx ++ steps.drop resume_idx)
}

meta def shrink_proof_aux : list (tactic_state × string × tactic_state) → io (list (tactic_state × string × tactic_state)) 
| [] := io.fail "shrink_proof called on empty proof"
| steps := do
  let ts_final := (steps.last sorry).snd.snd,
  io.run_tac ts_final tactic.done,
  ⟨fewer_steps, success⟩ ← io.catch (do steps ← strip_unused_haves ts_final steps, pure (steps, tt)) (λ e, pure (steps, ff)),
  if success then shrink_proof_aux fewer_steps else pure fewer_steps
  
meta def shrink_proof (ts₀ : tactic_state) (steps : list (string × tactic_state)) : io (list (tactic_state × string × tactic_state)) :=
  shrink_proof_aux (build_proof_trace ts₀ steps)
