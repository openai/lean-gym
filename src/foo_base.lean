import data.real.basic
import util.tactic

theorem usa_mo_2003_p5 : Π
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c),
  (2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) + (2 * b + c + a)^2 / (2 * b^2 + (c + a)^2) + (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) ≤ 8 :=
begin
  async {ring},
end

run_cmd validate_decl `usa_mo_2003_p5 -- fails as expected
