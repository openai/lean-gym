/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Kudzo Ahegbebu, Jesse Michael Han

Helper tactics for conjecturing
-/

import tactic
import tactic.gptf.basic
import util.tactic
/--
  Given a conjecture name and string, returns old tactic state, narrowed tactic state
-/
meta def add_conjecture (nm_str : string) (conj_str : string) : tactic (tactic_state × tactic_state) := do {
  ts_old ← tactic.read,
  let tac_str := format! "have {nm_str} : {conj_str}",
  result ← get_tac_and_capture_result tac_str.to_string 5000,
  return_result ← (match result with
  | interaction_monad.result.success _ ts' := do {
  ts_narrowed ← do {
    tactic.write ts',
    g ← list.head <$> tactic.get_goals,
    tactic.set_goals [g],
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

/--  
  return value ⟨nm, ts⟩ satisfies that `nm` is the name of a new declaration whose value is the proof `conj_pf` of the conjecture and that `ts` contains an environment which has `nm` registered as a declaration.
-/

meta def register_conjecture_pf (conj_pf : expr) (narrowed_ts : tactic_state) : tactic (name × tactic_state) := do {
  tp ← tactic.infer_type conj_pf,
  env ← tactic.get_env,
  new_name ←tactic.get_unused_name,
  let decl := (declaration.defn new_name (expr.collect_univ_params conj_pf) tp conj_pf reducibility_hints.opaque ff),
  res ← tactic.capture' (env.add decl $> ()),
  modified_ts ← (match res with 
  | interaction_monad.result.success _ ts' := do {
    tactic.write ts',
    decl_env ← env.add decl,
    tactic.set_env decl_env, 
    tactic.read
  }
  | interaction_monad.result.exception fn _ _ := do {
    let thunk := fn.get_or_else (λ _, format! "exception"),
    tactic.fail format! "{thunk ()}"
  }
  end),
  pure $ prod.mk decl.to_name modified_ts
}

/--
  `close_old_ts_top_goal_using_conjecture` should take the old_ts emitted by `tac₁`, looks up the declaration `nm` in `new_ts`'s environment, and uses it to prove the open conjecture which is the top-level goal of `old_ts`, and then returns `old_ts` after this modification. this represents the rest of the proof search after the conjecture been "re-injected".
-/
meta def close_old_ts_top_goal_using_conjecture (old_ts : tactic_state) (nm : name) (new_ts : tactic_state) : tactic tactic_state := do {
  -- Look up decl in new ts env
  tactic.write new_ts,
  modified_env ← tactic.get_env, 
  d ← modified_env.get nm,

  -- Use decl to close goal of old_ts
  tactic.write old_ts,
  result ← tactic.capture' $ pure d.value >>= tactic.exact,
  new_ts ← ( match result with 
  | interaction_monad.result.success _ ts' := do { 
    tactic.write ts',
    tactic.read
    }
  | interaction_monad.result.exception fn _ _ := do {
    let thunk := fn.get_or_else (λ _, format! "exception"),
    tactic.fail format! "{thunk ()}"
  } end),
  return new_ts
}
