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

namespace expr

meta def app_symbol_is (e : expr) (nm : name) : bool :=
match e.get_app_fn with
| (expr.const n _) := n = nm
| _ := ff
end

meta def contains_undefined (e : expr) : bool :=
e.fold ff $ λ e' _ b, if e.app_symbol_is `undefined then tt else b

end expr


namespace tactic

meta def set_goal_to (goal : expr) : tactic unit :=
mk_meta_var goal >>= set_goals ∘ pure

meta def guard_sorry (e : expr) : tactic unit := guard e.contains_sorry

meta def guard_undefined (e : expr) : tactic unit := guard e.contains_undefined

end tactic


section validate

meta def validate_proof (tgt: expr) (pf: expr) : tactic unit := do {
    guard (bnot pf.has_meta_var),
    tactic.guard_sorry pf,
    tactic.guard_undefined pf,
    tactic.type_check pf,
    pft ← tactic.infer_type pf,
    -- tactic.trace format!"PF: {pf}",
    -- tactic.trace format!"PFT: {pft}",
    -- tactic.trace format!"TGT: {tgt}",
    tactic.is_def_eq tgt pft
}

end validate

section add_open_namespace

meta def add_open_namespace : name → tactic unit := λ nm, do
env ← tactic.get_env, tactic.set_env (env.execute_open nm)

meta def add_open_namespaces (nms : list name) : tactic unit :=
nms.mmap' add_open_namespace

end add_open_namespace


section hashing

meta def tactic_hash : tactic ℕ := do {
  gs ← tactic.get_goals,
  hs ← gs.mmap $ λ g, do {
    tactic.set_goals [g],
    es ← (::) <$> tactic.target <*> tactic.local_context,
    es.mfoldl (λ acc e, (+) acc <$> expr.hash <$> tactic.head_zeta e) 0
  },
  pure $ hs.sum
}

end hashing


section misc

meta def tactic.is_theorem (nm : name) : tactic bool := do {
  env ← tactic.get_env,
  declaration.is_theorem <$> env.get nm
}

end misc
