
section string

section json

section has_to_json
universe u

meta class has_to_json (α : Type u) : Type (u+1) :=
(to_json : α → json)

meta class has_to_tactic_json (α : Type u) : Type (u+1) :=
(to_tactic_json : α → tactic json)

meta class has_from_json (α : Type u) : Type (u+1) :=
(from_json : json → tactic α)

end has_to_json

end json

namespace string

def replace_char : string → char → char → string
| ⟨cs⟩ c₁ c₂ := ⟨cs.map (λ c, if c = c₁ then c₂ else c)⟩

end string

end string
namespace expr

meta def app_symbol_is (e : expr) (nm : name) : bool :=
match e.get_app_fn with
| (expr.const n _) := n = nm
| _ := ff
end

meta def contains_undefined (e : expr) : bool :=
e.fold ff $ λ e' _ b, if e'.app_symbol_is `undefined then tt else b

end expr

section iterate_until

meta def iterate_until_aux
  {m} [monad m] [alternative m] {α}
  (tac :  m α) (stop : α → m bool) (fuel_exhausted_callback : m α)
  : Π (fuel : ℕ), m α
| 0 := do {result ← tac, mcond (stop result) (pure result) fuel_exhausted_callback}
| (n+1) := do { result ← tac, mcond (stop result) (pure result) (iterate_until_aux n)}

meta def iterate_until
  {m} [monad m] [alternative m] {α}
  (tac : m α) (stop : α → m bool) (fuel := 100000)
  (fuel_exhausted_callback : m α := alternative.failure)
  : m α
  :=
iterate_until_aux tac stop fuel_exhausted_callback fuel

end iterate_until