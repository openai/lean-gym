import tactic
import tactic.core
import util.io
import system.io

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

meta def enable_full_names : tactic unit := do {                                               
  set_bool_option `pp.full_names true                                                                  
}                                                                                                      
                                                                                                       
meta def with_full_names {α} (tac : tactic α) : tactic α :=                                    
tactic.save_options $ enable_full_names *> tac   

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

open interaction_monad.result
meta def run (tac : tactic unit) : tactic (interaction_monad.result tactic_state unit) := do {
  σ ← get_state,
  match tac σ with
  | r@(success _ new_state) := interaction_monad.set_state new_state *> pure r
  | r@(exception fn pos new_state) := pure r
  end
}

-- meta instance has_format_result {α σ} [has_to_format σ] [has_to_format α] : has_to_format (interaction_monad.result σ α) := ⟨by mk_to_format `interaction_monad.result⟩ -- ayyy

meta instance has_to_format_tactic_result {α : Type*} [has_to_format α] : has_to_format (interaction_monad.result tactic_state α) :=
⟨λ r,
  match r with
  | (success val new_state) := format!"SUCCESS!\nNEW_STATE: {new_state}\nVAL: {val}"
  | (exception fn pos old_state) := do {
    let msg := (fn.get_or_else (λ _, format.of_string "n/a")) (),
    format!"EXCEPTION!\nMSG: {msg}\nPOS: {pos}\nOLD_STATE: {old_state}"
  }
  end
⟩

meta instance has_to_tactic_format_tactic_result {α : Type*} [has_to_format α] : has_to_tactic_format (interaction_monad.result tactic_state α) :=
⟨λ σ, pure $ has_to_format.to_format σ⟩

end tactic



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