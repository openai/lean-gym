import system.io
import tactic.gptf.utils.util

-- convenience function for command-line argument parsing
meta def list.nth_except {α} : list α → ℕ → string → io α := λ xs pos msg,
  match (xs.nth pos) with
  | (some result) := pure result
  | none := do
    io.fail' format!"must supply {msg} as argument {pos}"
  end