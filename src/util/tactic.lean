/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Stanislas Polu, Jesse Michael Han

Helper functions to work with the tactic monad.
-/
import tactic
import tactic.core
import util.io
import system.io
import basic.control
import util.util

section run_with_state'

namespace interaction_monad
open interaction_monad.result
meta def run_with_state' {σ₁ σ₂ : Type} {α : Type*} (state : σ₁) (tac : interaction_monad σ₁ α) : interaction_monad σ₂ α :=
λ s, match (tac state) with
     | (success val _) := success val s
     | (exception fn pos _) := exception fn pos s
     end
end interaction_monad
end run_with_state'

namespace tactic

open interaction_monad interaction_monad.result

/- capture but backtrack the state -/
meta def capture' {α} (t : tactic α) : tactic (tactic_result α) :=
λ s, match t s with
| (success r s') := success (success r s') s
| (exception f p s') := success (exception f p s') s
end

meta def set_goal_to (goal : expr) : tactic unit :=
mk_meta_var goal >>= set_goals ∘ pure

meta def guard_sorry (e : expr) : tactic unit := guard $ bnot e.contains_sorry

meta def guard_undefined (e : expr) : tactic unit := guard $ bnot e.contains_undefined

end tactic

section validate

meta def kernel_type_check (pf : expr) : tactic unit := do {
  tp ← tactic.infer_type pf,
  env ← tactic.get_env,
  let decl := (declaration.defn `_ (expr.collect_univ_params pf) tp pf reducibility_hints.opaque ff),
  res ← tactic.capture' (env.add decl $> ()),
  match res with
  | (interaction_monad.result.success _ _) := pure ()
  | (interaction_monad.result.exception msg _ _) := let msg := msg.get_or_else (λ _, ("" : format)) in
    tactic.fail format! "kernel type check failed:\n---\n{msg ()}\n---\n"
  end
}

meta def validate_proof (tgt: expr) (pf: expr) : tactic unit := do {
    env ← tactic.get_env,
    pf ← pure $ env.unfold_untrusted_macros pf,
    pft ← tactic.infer_type pf,
    tactic.type_check pf tactic.transparency.all,
    guard (bnot pf.has_meta_var) <|> do {
      tactic.fail format! "proof contains metavariables"
    },
    tactic.guard_sorry pf <|> do {
      tactic.fail format! "proof contains `sorry`"
    },
    tactic.guard_undefined pf <|> do {
      tactic.fail format! "proof contains `undefined`"
    },
    tactic.is_def_eq tgt pft <|> do {
      tgt_fmt ← tactic.pp tgt,
      pft_fmt ← tactic.pp pft,
      tactic.fail format! "proof type mismatch: {tgt_fmt} != {pft_fmt}"
    },
    kernel_type_check pf
}

meta def validate_decl (nm : name) : tactic unit := do {
  env ← tactic.get_env,
  d ← env.get nm,
  validate_proof d.type d.value
}

end validate

section add_open_namespace

meta def add_open_namespace : name → tactic unit := λ nm, do
env ← tactic.get_env, tactic.set_env (env.execute_open nm)

meta def add_open_namespaces (nms : list name) : tactic unit :=
nms.mmap' add_open_namespace

end add_open_namespace

section full_names

namespace tactic

meta def enable_full_names : tactic unit := do {
  set_bool_option `pp.full_names true
}

meta def with_full_names {α} (tac : tactic α) : tactic α :=
tactic.save_options $ enable_full_names *> tac

end tactic

meta def tactic_state.fully_qualified (ts : tactic_state) : tactic tactic_state := do {
  ts₀ ← tactic.read,
  tactic.write ts,
  result_ts ← tactic.with_full_names $ tactic.read,
  tactic.write ts₀,
  pure result_ts
}

meta def tactic_state.fully_qualified_string (ts : tactic_state) : tactic string := do {
  ts₀ ← tactic.read,
  tactic.write ts,
  result ← tactic.with_full_names $ (tactic.read >>= λ ts, pure ts.to_format.to_string),
  tactic.write ts₀,
  pure result
}

end full_names

section tactic_state
open interaction_monad.result
setup_tactic_parser

meta def num_goals' : tactic_state → option ℕ :=
λ ts, match tactic.num_goals ts with | (success val _) := pure val | _ := none end

-- TODO(jesse): this is a hack. might be better to do this in python
meta def consume_with_parser {α} (p : lean.parser α) : string → io string := λ inp, do {
  io.run_tactic'' $ do
    prod.snd <$> lean.parser.run (with_input p inp)
}

-- TODO(jesse): performance
meta def consume_spaces : string → string
| arg@⟨[]⟩ := arg
| arg@⟨(x::xs)⟩ := if x = ' ' then consume_spaces ⟨xs⟩ else arg

-- WARNING: this is a hack
meta def remove_indents_with_split (c : char := '\t'): string → string := λ str,
let strs := str.split (= '\t') in
string.intercalate (⟨['\t']⟩ : string) (consume_spaces <$> strs)

meta def postprocess_tactic_state : tactic_state → tactic string := λ ts, do
  let main : tactic string := do {
    let ts_str := "\\\"".intercalate (ts.to_format.to_string.split (= '"')),
    tabbed_ts_str ← do {
      if (num_goals' ts).get_or_else 0 ≤ 1
      then pure $ ts_str.replace_char '\n' '\t'
      else tactic.unsafe_run_io $ (λ x, string.replace_char x '\n' '\t')
             <$> (consume_with_parser small_nat >=>
               consume_with_parser ident) ts_str},
    pure $ remove_indents_with_split '\t' tabbed_ts_str
  },
  main <|> (let msg := "[postprocess_tactic_state] WARNING: POSTPROCESSING FAILED" in
    tactic.trace msg *> tactic.fail msg)

end tactic_state


section parse_tac

setup_tactic_parser

open tactic

/-- Run the given parser on the given string input. -/
meta def run_on_input {α} (p : lean.parser α) (s : string) : tactic α :=
lean.parser.run $ do
  get_state >>= λ ps, of_tactic $ do
    tactic.set_env ps.env,
    -- eval_trace format!"[parse_itactic_reflected] TRYING TO PARSE {itactic_string}",
    prod.fst <$> (@interaction_monad.run_with_state' parser_state _ _ ps $ with_input p s)

/-- Parse a reflected interactive tactic from a string.
    The result can be evaluated to a `tactic unit` by using
    `eval_expr (tactic unit)`. -/
meta def parse_itactic_reflected (tactic_string : string) : tactic expr := do
let itactic_string := "{ " ++ tactic_string ++  " }",
r ← run_on_input parser.itactic_reflected itactic_string,
pure $ reflected_value.expr r

/-- Parse an interactive tactic from a string. -/
meta def parse_itactic (tactic_string : string) : tactic (tactic string) :=
do
  rtac ← parse_itactic_reflected tactic_string,
  u ← eval_expr (tactic unit) rtac,
  pure (u *> pure tactic_string)


meta def get_tac_and_capture_result (next_candidate : string) (timeout : ℕ := 5000) : tactic (tactic_result _) := do {
  tac ← do {
    env ← tactic.get_env,
    tac ← parse_itactic next_candidate,
    tactic.set_env env,
    pure tac
  },
  result ← tactic.capture' (tactic.try_for_time timeout $ tactic.try_for 200000 tac), -- if `tac` fails, exception is captured here
  pure result
}

end parse_tac

section misc

meta def tactic.is_theorem (nm : name) : tactic bool := do {
  env ← tactic.get_env,
  declaration.is_theorem <$> env.get nm
}

end misc
