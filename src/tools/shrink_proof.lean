/-
Copyright (c) 2022 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Daniel Selsam

Simple, barebones heuristic proof-minimization.
-/
import util.io
import data.list.basic
import util.tactic

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
  ⟨bad_idx, resume_goals⟩ ← steps.enum.reverse.mfirst (λ ⟨idx, ⟨ts1, action, ts2⟩⟩, do {
    if action.to_list.take 5 = "have ".to_list then do {
      gs1 ← io.run_tac ts1 tactic.get_goals,
      gs2 ← io.run_tac ts2 tactic.get_goals,
      (goal_with_assumption, all_in_one) ← do {
        -- `have` step with proof provided
        if gs1.length = gs2.length ∧ gs1.drop 1 = gs2.drop 1 then pure (gs2.head, tt) 
        -- `have` step without proof provided
        else if gs1.length + 1 = gs2.length ∧ gs1.drop 1 = gs2.drop 2 then pure (gs2.nth_le 1 sorry, ff)
        -- something weird, e.g. `have h : <prop>; swap`
        else io.fail "weird `have`"
      },
      assumption ← io.run_tac ts2 $ do { 
        tactic.set_goals [goal_with_assumption], 
        hs ← tactic.local_context, 
        if hs_nnil : hs ≠ [] then pure (hs.last hs_nnil) else tactic.fail "weird `have`"
      },
      proof_of_goal_with_assumption ← io.run_tac ts_final (tactic.instantiate_mvars goal_with_assumption),
      if not (expr.occurs assumption proof_of_goal_with_assumption) then pure (idx, if all_in_one then gs2 else gs2.drop 1) else io.fail "`have` step is used"
    } else
      io.fail "not a `have` step"
    }
  ),

  goals_per_step : list (list expr) ← steps.mmap (λ ⟨ts1, action, ts2⟩, io.run_tac ts1 tactic.get_goals),
  let resume_idx : ℕ := goals_per_step.enum.find_index (λ idx__goals, idx__goals.fst > bad_idx ∧ idx__goals.snd = resume_goals),
  if resume_idx = steps.length then io.fail "weird `have`, possible swap" else pure (steps.take bad_idx ++ steps.drop resume_idx)
}

meta def rerun_proof (ts_orig : tactic_state) : tactic_state → list string → io (list (tactic_state × string × tactic_state))
| ts1 [] := io.run_tac ts_orig (do {
  -- confirm that the proof has finished
  [g] ← tactic.get_goals,
  tgt ← tactic.infer_type g,
  tactic.write ts1,
  pf ← tactic.get_assignment g >>= tactic.instantiate_mvars,
  validate_proof tgt pf <|> (tactic.trace "failed to validate" >> tactic.fail "failed to validate"),
  pure []
})
| ts1 (action::actions) := do 
  result_with_string ← io.run_tac ts1 (get_tac_and_capture_result action 5000),
  match result_with_string with
  -- The tactic application was successful.
  | interaction_monad.result.success _ ts2 := do {
    rest ← rerun_proof ts2 actions,
    pure $ (ts1, action, ts2) :: rest
  }
  | _ := io.fail "failed to rerun proof"
  end

meta def shrink_proof : list (tactic_state × string × tactic_state) → io (list (tactic_state × string × tactic_state)) 
| [] := io.fail "shrink_proof called on empty proof"
| steps@(step::rest) := do
  let ts_final := (steps.last sorry).snd.snd,
  io.run_tac ts_final tactic.done,
  ⟨fewer_steps, success⟩ ← io.catch (do steps ← strip_unused_haves ts_final steps, pure (steps, tt)) (λ e, pure (steps, ff)),
  let ts_start := step.fst,
  if success then do {
    io.catch (do {
      steps ← rerun_proof ts_start ts_start $ fewer_steps.map (λ ⟨_, action, _⟩, action),
      shrink_proof steps
    }) (λ e, pure steps)
  }
  else
    pure steps

