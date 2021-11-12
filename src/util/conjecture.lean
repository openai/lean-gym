/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Kudzo Ahegbebu, Jesse Michael Han
Helper tactics for conjecturing
-/
import tactic
import tactic.gptf.basic

/--
Does bad things. Accepts a conjecture and just adds it to the tactic state without proof
-/
meta def assume_conjecture (conj_str: string): tactic tactic_state := do {
  conj_name ← tactic.get_unused_name "h",
  let tac_str := format! "have {conj_name} : {conj_str}",
  result ← get_tac_and_capture_result tac_str.to_string 5000,
  return_result ← (match result with 
    | interaction_monad.result.success _ ts' := do {
      ts_final ← do {
        tactic.write ts',
        (g1 :: gs) ← tactic.get_goals,
        tactic.set_goals gs,
        tactic.read
      },
      pure ts_final
    }
    | interaction_monad.result.exception fn pos ts' := do {
      let thunk := fn.get_or_else (λ _, format! "exception"),
      tactic.fail format! "{thunk ()}"
    }
  end),
  tactic.write return_result,
  tactic.revert_target_deps,
  ts ← tactic.read,
  pure ts
}
/--
  Given a conjecture name and string, returns old tactic state, narrowed tactic state
-/
meta def add_conjecture (conj_str : string) : tactic (tactic_state × tactic_state) := do {
  ts_old ← tactic.read,
  conj_name ← tactic.get_unused_name "h",
  let tac_str := format! "have {conj_name} : {conj_str}",
  result ← get_tac_and_capture_result tac_str.to_string 5000,
  return_result ← (match result with
  | interaction_monad.result.success _ ts' := do {
  ts_narrowed ← do {
    tactic.write ts',
    g ← list.head <$> tactic.get_goals,
    tactic.set_goals [g],
    tactic.revert_target_deps,
    tactic.read
  },
  pure $ prod.mk ts' ts_narrowed
}
  | interaction_monad.result.exception fn pos ts' := do {
    let thunk := fn.get_or_else (λ _, format! "exception"),
    tactic.fail format! "{thunk ()}"
  }
  end),

  tactic.write ts_old,
  pure return_result
} 