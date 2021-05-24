import tactic
import tactic.core
import util.io
import system.io
import basic.control

open tactic

namespace tactic

meta def set_goal_to (goal : expr) : tactic unit :=
mk_meta_var goal >>= set_goals ∘ pure

/-- Creates an empty tactic state. -/
meta def mk_tactic_state : tactic tactic_state :=
tactic.unsafe_run_io $ io.run_tactic' $ tactic.exact `(trivial) *> tactic.read

end tactic


section

setup_tactic_parser

meta def get_ts_with_main_goal (tgt : expr) : tactic tactic_state := do {
  ts₀ ← tactic.read,
  tactic.mk_tactic_state >>= tactic.write,
  tactic.set_goal_to tgt,
  ts ← tactic.read,
  tactic.write ts₀,
  pure ts
}

/-- creates tactic_state_data as if we were proving the declaration
 (currently only theorems are supported) with name `decl_nm`. -/
meta def get_ts_at_decl (decl_nm : name) : tactic tactic_state := do {
  env ← tactic.get_env,
  decl ← env.get decl_nm,
  get_ts_with_main_goal decl.type
}

end



section set_env_at_decl

meta def get_env_at_decl (decl_nm : name) : tactic environment := do {
  env ← tactic.get_env,
  lean_file ← env.decl_olean decl_nm,
  pure $ environment.for_decl_of_imported_module lean_file decl_nm
}

meta def set_env_at_decl (decl_nm : name) : tactic unit := do {
    env ← get_env_at_decl decl_nm,
    tactic.set_env_core env,
    skip
}

end set_env_at_decl


section add_open_namespace

meta def add_open_namespace : name → tactic unit := λ nm, do
env ← tactic.get_env, tactic.set_env (env.execute_open nm)

meta def add_open_namespaces (nms : list name) : tactic unit :=
nms.mmap' add_open_namespace

end add_open_namespace


section parse_eval_tac

setup_tactic_parser
open tactic

meta def parse_eval_tac
  (ps : parser_state)
  (tactic_string : string)
  : tactic (tactic unit × format) := do {
  let itactic_string := "{" ++ tactic_string ++ "}",
  texpr ← (reflected_value.expr ∘ prod.fst) <$>
    (interaction_monad.run_with_state' ps $ with_input parser.itactic_reflected itactic_string),
  prod.mk <$> (eval_expr (tactic unit) texpr) <*> has_to_tactic_format.to_tactic_format texpr
}

end parse_eval_tac


section hashing

meta def tactic_hash : tactic ℕ := do {                                                                 
  gs ← tactic.get_goals,                                                                                
  hs ← gs.mmap $ λ g, do {                                                                              
    tactic.set_goal_to g,                                                                               
    es ← (::) <$> tactic.target <*> tactic.local_context,                                               
    pure $ es.foldl (λ acc e, acc + e.hash) 0},                                                         
  pure $ hs.sum                                                                                         
}         

end hashing