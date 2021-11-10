import util.tactic

meta def should_fail
  (u v : ℕ+)
  (h₀ : 100 ∣ (14*u - 46))
  (h₁ : 100 ∣ (14*v - 46))
  (h₂ : u < 50)
  (h₃ : v < 100)
  (h₄ : 50 < v) :
  ((u + v):ℕ) / 2 = 64 :=
begin
  revert h₄,
  contrapose h₃,
  intro hn,
  exact not_lt_of_lt hn undefined,
end

meta def should_succeed : true := by trivial


meta def main : io unit := io.run_tactic'' $ do {
  (tactic.guard_undefined `(undefined : ℕ) <|> tactic.trace "OK"),
  (tactic.guard_sorry `(sorry : ℕ) <|> tactic.trace "OK"),
  (validate_decl `should_fail) <|> tactic.trace "OK",
  validate_decl `should_succeed *> tactic.trace "OK"
}
