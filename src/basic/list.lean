/- Author: E.W.Ayers © 2019.
Copied from the lean-tpe projcet: https://github.com/jesse-michael-han/lean-tpe-public

Some additional helpers for working with lists.
I suspect that I have duplicated some functionality here.
-/
import data.list basic.control

universe u

namespace list

variables {α β : Type u} {T : Type u → Type u}

def mmapi_core [applicative T] (f : nat → α → T β) : nat → list α → T (list β)
| n [] := pure []
| n (h :: t) := pure (::) <*> f n h <*> mmapi_core (n+1) t

def mmapi  [applicative T] (f : nat → α → T β) : list α → T (list β) :=
mmapi_core f 0

def mpicki_core [alternative T] (p : nat → α  → T β) : nat → list α → T β
| i [] := failure
| i (h :: t) := p i h <|> mpicki_core (i+1) t

def mpicki [alternative T] (p : nat → α → T β) : list α → T β := mpicki_core p 0

def picki (p : nat → α  → option β) : list α → option β := mpicki p

def mpick [alternative T] (p : α → T β) : list α → T β := mpicki_core (λ _, p) 0

def pick (p : α → option β) : list α → option β := mpick p

/-- Returns true if at least one item returns true under `p`.-/
def m_some {T : Type → Type u} [monad T] (p : α → T bool) : list α → T bool
| [] := pure ff
| (h :: t) := do b ← p h, if b then pure tt else m_some t

def m_all {T : Type → Type u}  [monad T] (p : α → T bool) : list α → T bool
| l := bnot <$> (m_some (λ x, bnot <$> p x) l)

def find_with_index_core (p : α → Prop) [decidable_pred p] : nat → list α → option (α × nat)
| i [] := none
| i (h :: t) := if p h then some ⟨h,i⟩ else find_with_index_core (i+1) t

def mfind_with_index (p : α → Prop) [decidable_pred p] : list α → option (α × nat) :=
find_with_index_core p 0

private def partition_sum_fold : α ⊕ β → list α × list β → list α × list β
| (sum.inl a) (as,bs) := (a::as,bs)
| (sum.inr b) (as,bs) := (as,b::bs)

def partition_sum : list (α ⊕ β) → list α × list β
| l := foldr partition_sum_fold ([],[]) l

def ohead : list α → option α
| [] := none
| (h :: t) := some h

def olast : list α → option α
| [x] := some x
| [] := none
| (h :: t) := olast t

/-- Find the maximum according to the given function. -/
def max_by (f : α → int) (l : list α) : option α :=
prod.fst <$> foldl (λ (acc : option(α×ℤ)) x, let m := f x in option.cases_on acc (some ⟨x,m⟩) (λ ⟨_,m'⟩, if m < m' then acc else some ⟨x,m⟩)) none l

def min_by (f : α → int) (l : list α) : option α := max_by (has_neg.neg ∘ f) l

def achoose [alternative T] (f : α → T β) : list α → T (list β)
| [] := pure []
| (h :: t) :=  ((pure cons <*> f h) <|> pure id) <*> achoose t

def apick [monad T] [alternative T] (f : α → T β) : list α → T β
| [] := failure
| (h :: t) := f h <|> (pure (punit.star) >>= λ _, apick t)

def mchoose [applicative T] (f : α → T (option β)) : list α → T (list β)
| [] := pure []
| (h :: t) := pure (@option.rec β (λ _, list β → list β) id cons) <*> f h <*> mchoose t

/-- Same as filter but explicitly takes a boolean.-/
def bfilter : (α → bool) → list α → list α
| f a := filter (λ x, f x) a

def bfind : (α → bool) → list α → option α
| f a := find (λ x, f x) a

def bfind_index (f : α → bool) : list α → option nat
| [] := none
| (h :: t) := if f h then some 0 else nat.succ <$> bfind_index t

/-- `subtract x y` is some `z` when `∃ z, x = y ++ z` -/
def subtract [decidable_eq α]: (list α) → (list α) → option (list α)
| a [] := some a -- [] ++ a = a
| [] _ := none   -- (h::t) ++ _ ≠ []
-- if t₂ ++ z = t₁ then (h₁ :: t₁) ++ z = (h₁ :: t₂)
| (h₁ :: t₁) (h₂ :: t₂) := if h₁ = h₂ then subtract t₁ t₂ else none

def opartition (f : α → option β) : list α → list β × list α :=
foldr (λ x, option.rec_on (f x) (prod.map id $ cons x) $ λ b, prod.map (cons b) id) ([],[])

def apartition [alternative T] (f : α → T β) : list α → T (list β × list α)
| [] := pure $ ([],[])
| (h::rest) :=
    pure (λ (o : option β) p, option.rec_on o (prod.map id (cons h) p) (λ b, prod.map (cons b) id p))
    <*> ((some <$> f h) <|> pure none)
    <*> apartition rest

def eq_by (e : α → α → bool) : list α → list α → bool
| [] [] := tt
| [] (_ :: _) := ff
| (_ :: _) [] := ff
| (a₁ :: l₁) (a₂ :: l₂) := e a₁ a₂ ∧ eq_by l₁ l₂

def collect {β} (f : α → list β) : list α → list β
| l := bind l f

def mcollect {T} [monad T] (f : α → T (list β)) : list α → T (list β)
|l := mfoldl (λ acc x, (++ acc) <$> f x) [] l

def msome {T} [monad T] {α} (f : α → T bool) : list α → T bool
|[] := pure ff
|(h::t) := f h >>= λ x, if x then pure tt else msome t

/-- `skip n l` returns `l` with the first `n` elements removed. If `n > l.length` it returns the empty list  -/
def skip {α} : ℕ → list α → list α
|0 l := l
|(n+1) [] := []
|(n+1) (h::t) := skip n t

meta def get_equivalence_classes {T : Type → Type} [monad T] {α : Type} (rel : α → α → T bool) : list α → T(list (list α))
| l := do
  x ←  mfoldl (λ table h, do
          pr : option ((α × list α) × nat) ← @mpicki _ _ (T ∘ option) _ (λ i e,
            ((do
              b ← rel (prod.fst e) h,
              pure $ if b then some (e,i) else none
            ) : T (option _))
          ) table,
          pure $ match pr with
          | none := (h,[h]) :: table
          | (some ⟨x,i⟩) := table.update_nth i $ prod.map id (cons h) x
          end
    ) [] $ l,
   pure $ reverse $ map (reverse ∘ prod.snd) $ x

/-- Perform the given pair reduction to neighbours in the list until you can't anymore. -/
meta def pair_rewrite {m : Type u → Type} [monad m] [alternative m] (rr : α → α → m (α)) : list α → m (list α)
| [] := pure []
| [x] := pure [x]
| (x :: y :: rest) := do
  (do z ← rr x y,
    pair_rewrite (z :: rest)
  ) <|> (do
    res ← pair_rewrite (y :: rest),
    match res with
    | [] := pure [x]
    | (y2 :: rest2) := (do
      z ← rr x y2,
      pair_rewrite (z :: rest2)
      ) <|> (pure $ x :: y2 :: rest2)
    end
  )

def with_indices : list α → list (nat × α) := list.map_with_index prod.mk

def msplit {T : Type u → Type u} [monad T] {α β γ : Type u} (p : α → T (β ⊕ γ))
  : list α → T (list β × list γ)
  | l := do
    ⟨xs,ys⟩ ← l.mfoldl (λ (xsys : list β × list γ) a, do
        ⟨xs,ys⟩ ← pure xsys,
        r ← p a,
        pure $ sum.rec_on r (λ x, ⟨x::xs,ys⟩) (λ y, ⟨xs,y::ys⟩)
    ) (⟨[],[]⟩),
    pure ⟨xs.reverse,ys.reverse⟩

end list