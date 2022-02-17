/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Stanislas Polu

Helper functions to work with the io monad.
-/

import system.io

section io
open interaction_monad interaction_monad.result
namespace io

/-- verion of io.run_tactic' which does not suppress the exception msg -/
meta def run_tactic'' {α} (tac :tactic α) : io α := do {
  io.run_tactic $ do {
    result ← tactic.capture tac,
    match result with
    | (success val _) := pure val
    | (exception m_fmt _ _) := do {
      let fmt_msg := (m_fmt.get_or_else (λ _, format!"n/a")) (),
      let msg := format!"[fatal] {fmt_msg}",
      tactic.trace msg,
      tactic.fail msg
    }
    end
  }
}

meta def run_tactic''' {α} (tac :tactic α) : io α := do {
  io.run_tactic $ do {
    result ← tactic.capture tac,
    match result with
    | (success val _) := pure val
    | (exception m_fmt _ _) := do {
      let fmt_msg := (m_fmt.get_or_else (λ _, format!"n/a")) (),
      let msg := format!"[fatal] {fmt_msg}",
      tactic.fail msg
    }
    end
  }
}

meta def fail' {α} (fmt : format) : io α := io.fail $ format.to_string fmt

meta def put_str_ln' : Π (fmt : format), io unit := io.put_str_ln ∘ format.to_string

meta def run_tac {α : Type} (ts : tactic_state) (tac : tactic α) : io α :=
  run_tactic''' (do tactic.write ts, tac)

end io
end io

-- convenience function for command-line argument parsing
meta def list.nth_except {α} : list α → ℕ → string → io α := λ xs pos msg,
  match (xs.nth pos) with
  | (some result) := pure result
  | none := do
    io.fail' format!"must supply {msg} as argument {pos}"
  end


