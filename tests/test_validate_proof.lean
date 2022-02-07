import util.tactic
import data.real.basic

meta def should_fail_1
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

meta def should_fail_2
  (p q : ℝ → ℝ)
  (h₀ : ∀ x, p x = 2 - x^2)
  (h₁ : ∀ x≠0, q x = 6 / x) :
  p (q 2) = -7 :=
begin
  sorry,
end

-- meta def should_fail_3
--   (n : ℕ) :
--   3 ∣ n^3 + 2 * n :=
-- begin
--   rw [add_comm],
--   have h3 : 1 * (n + 1) ≤ (n + 1),
--   rw one_mul,
--   apply dvd_trans,
--   swap,
--   simp [],
-- end

meta def should_succeed_1 : true := by trivial

meta def should_succeed_2
  (p q : ℝ → ℝ)
  (h₀ : ∀ x, p x = 2 - x^2)
  (h₁ : ∀ x≠0, q x = 6 / x) :
  p (q 2) = -7 :=
begin
  rw [h₀, h₁],
  ring,
  linarith,
end


meta def main : io unit := io.run_tactic'' $ do {
  (tactic.guard_undefined `(undefined : ℕ) <|> tactic.trace "OK"),
  (tactic.guard_sorry `(sorry : ℕ) <|> tactic.trace "OK"),

  (validate_decl `should_fail_1) <|> tactic.trace "OK",
  (validate_decl `should_fail_2) <|> tactic.trace "OK",
  -- (validate_decl `should_fail_3) <|> tactic.trace "OK",
  validate_decl `should_succeed_1 *> tactic.trace "OK",
  validate_decl `should_succeed_2 *> tactic.trace "OK"
}