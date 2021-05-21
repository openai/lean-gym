import tactic

open tactic

namespace tactic

meta def set_goal_to (goal : expr) : tactic unit :=
mk_meta_var goal >>= set_goals ∘ pure

end tactic


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