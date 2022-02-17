/-
Copyright (c) 2022 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Daniel Selsam

Simple "squeezing" finishing.
-/
import util.io
import data.list.basic
import util.tactic

meta def try_finish_tactics : list (tactic unit × string) := [
  (`[trivial], "trivial"),
  (`[refl], "refl"),
  (`[exact dec_trivial], "exact dec_trivial"),
  (`[assumption], "assumption"),
  (`[simp], "simp"),
  (`[dsimp], "dsimp"),
  (`[norm_num], "norm_num"),
  (`[ring], "ring"),
  (`[simp [*]], "simp [*]"),
  (`[linarith], "linarith")
]

meta def try_finish (ts : tactic_state) (timeout : nat := 1000) : io (option (string × tactic_state)) :=
  (try_finish_tactics.mfirst $ λ ⟨tac, tacString⟩, io.run_tac ts $ do {
    gs1 ← tactic.get_goals,
    tactic.try_for_time timeout $ tactic.try_for 200000 (tactic.solve1 tac),
    ts2 ← get,
    pure (tacString, ts2)
  }) <|> pure none
