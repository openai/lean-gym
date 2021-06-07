/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Stanislas Polu

Helper functions to work with the tactic monad.
-/
import tactic
import tactic.core
import util.io
import system.io
import basic.control

open tactic

namespace tactic

meta def set_goal_to (goal : expr) : tactic unit :=
mk_meta_var goal >>= set_goals ∘ pure

meta def guard_sorry : expr → tactic unit := λ e, do {
  contains_sorry_flag ← e.mfold ff (λ e' _ acc, if acc then pure acc else pure $ bor acc $ e'.is_sorry.is_some),
  guard $ bnot contains_sorry_flag
}

end tactic


section validate

meta def validate_proof (g: expr) (pf: expr) : tactic unit := do {
    guard (bnot pf.has_meta_var),
    tactic.guard_sorry pf,
    tactic.type_check pf,
    pft ← tactic.infer_type pf,
    tgt ← tactic.infer_type g,
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