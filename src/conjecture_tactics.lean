
import tactic
import tactic.gptf.basic
import util.tactic

namespace tactic.interactive
/--
  returns old tactic state, narrowed tactic state
-/
meta def tac₁ (nm_str : string) (conj_str : string) : tactic (tactic_state × tactic_state) := do {
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

-- Generates names for conjectures given a decl name
meta def name_conj (old : name) (new : option name := none) : tactic name :=
  match new with
  | none :=
    match old.components.reverse with
    | last :: most := (do let last := last.to_string,
                         tactic.get_unused_name $ mk_str_name old.get_prefix last ++ "_conjecture")
    | nil          := undefined
    end
  | (some new) := return (mk_str_name old.get_prefix new.to_string)
end


/--  
  return value ⟨nm, ts⟩ satisfies that `nm` is the name of a new declaration whose value is the proof `conj_pf` of the conjecture and that `ts` contains an environment which has `nm` registered as a declaration.
-/
meta def tac₂ (conj_pf : expr) (narrowed_ts : tactic_state) : tactic (name × tactic_state) := do {
  tp ← tactic.infer_type conj_pf,
  env ← tactic.get_env,
  -- TODO (Kudzo) decl should accept new name from name_conj
  let decl := (declaration.defn `_ (expr.collect_univ_params conj_pf) tp conj_pf reducibility_hints.opaque ff),
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
  `tac₃` should take the old_ts emitted by `tac₁`, looks up the declaration `nm` in `new_ts`'s environment, and uses it to prove the open conjecture which is the top-level goal of `old_ts`, and then returns `old_ts` after this modification. this represents the rest of the proof search after the conjecture been "re-injected".
-/
meta def tac₃ (old_ts : tactic_state) (nm : name) (new_ts : tactic_state) : tactic tactic_state := do {
  -- Look up decl in new ts env
  old_gs ← tactic.get_goals,
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

-- meta def test_tact₂ : tactic unit :=  do {
--   let pf_term : expr := `(trivial),
--   ts ← tactic.read,
--   ⟨nm, new_ts⟩ ← tac₂, pf_term ts,
--   tactic.write new_ts,
--   env ← tactic.get_env,
--   decl ← env.get nm,
--   pure ()
--   }

end tactic.interactive

-- e.g.
run_cmd (do {
  ⟨ts_old, ts_narrowed⟩ ←  tactic.interactive.tac₁ "h" "false",
  tactic.trace ts_old,
  tactic.trace "\n----\n",
  tactic.trace ts_narrowed,
  new_name ← tactic.interactive.name_conj "test_name" none,
  tactic.trace new_name
})