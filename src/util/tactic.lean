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

end tactic


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
    pure $ es.foldl (λ acc e, acc + e.reduce_let.hash) 0
  },
  pure $ hs.sum
}

end hashing


section option
meta def option.to_tactic {α} (x : option α ) (exception_msg : string := "[option.to_tactic] failed") : tactic α :=
match x with
| (some val) := pure val
| none := tactic.fail exception_msg
end

-- run_cmd ((none : option ℕ).to_tactic "FAILURE") -- errors with "FAILURE"
-- run_cmd ((some 42 : option ℕ).to_tactic >>= tactic.trace) -- 42
end option

section misc

meta def tactic.is_theorem (nm : name) : tactic bool := do {
  env ← tactic.get_env,
  declaration.is_theorem <$> env.get nm
}

end misc
