/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise414

/-!
# Exercise 4.24 (Scott 1981, PRG-19, Lecture IV) — Schröder–Bernstein via a fixed
point

(For set theorists.) Let `f : A → B` and `g : B → A` be one-one (injective, not
necessarily onto).
**Then there is a one-one correspondence `h : A ≃ B`** (`schroeder_bernstein`).

Following Tarski's hint, work in the power-set domain `P A` (a complete lattice)
and take a fixed
point `X` of the monotone operator

  `T(X) = (A − g(B)) ∪ g(f(X))`,

which exists by Knaster–Tarski (Exercise 4.14 / 4.13(2), here `lfpSet`). With `X =
T(X)` fixed,
define

  `h(a) = f(a)`        if `a ∈ X`,
  `h(a) = g⁻¹(a)`      if `a ∉ X`

— well-defined because `a ∉ X = T(X)` forces `a ∈ g(B)` (it is not in `(A −
g(B))`), so `a` has a
unique `g`-preimage (`mem_range_of_not_mem`). The map `h` is:

* **injective** (`sbFun_injective`): within `X`, by injectivity of `f`; outside
`X`, by injectivity
  of `g`; the mixed case is impossible — `f(a₁) = g⁻¹(a₂)` would put `a₂ =
  g(f(a₁)) ∈ g(f(X)) ⊆ X`;
* **surjective** (`sbFun_surjective`): for `b ∈ B`, if `g(b) ∉ X` then `h(g(b)) =
b`; if `g(b) ∈ X`
  then `g(b) ∈ g(f(X))`, so `g(b) = g(f(a))` with `a ∈ X`, whence `b = f(a) =
  h(a)`.

Packaged as the equivalence `schroederBernsteinEquiv`. This is a *set
theorists'* exercise and is
inherently classical; the construction of `h` uses `Classical.choice` (the
`g`-preimage), exactly as
the statement demands.
-/

namespace Domain.Neighborhood.Exercise424

open Domain.Neighborhood.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

/-- Tarski's operator `T(X) = (A − g(B)) ∪ g(f(X))` on `P A`. -/
def sbOp (f : A → B) (g : B → A) (X : Set A) : Set A := (Set.range g)ᶜ ∪ g '' (f '' X)

theorem sbOp_monotone (f : A → B) (g : B → A) : Monotone (sbOp f g) := by
  intro X Y hXY a ha
  rcases ha with ha | ⟨b, ⟨x, hx, rfl⟩, rfl⟩
  · exact Or.inl ha
  · exact Or.inr ⟨f x, ⟨x, hXY hx, rfl⟩, rfl⟩

/-- The Tarski fixed point `X` with `X = (A − g(B)) ∪ g(f(X))` (`lfpSet`, Exercise
4.14). -/
def sbSet (f : A → B) (g : B → A) : Set A := lfpSet (sbOp f g)

theorem sbSet_isFixed (f : A → B) (g : B → A) : sbOp f g (sbSet f g) = sbSet f g :=
  lfpSet_isFixed (sbOp f g) (sbOp_monotone f g)

/-- Anything outside the fixed set `X` lies in the range of `g` (so it has a
`g`-preimage). -/
theorem mem_range_of_not_mem {a : A} (ha : a ∉ sbSet f g) : a ∈ Set.range g := by
  have hne : a ∉ sbOp f g (sbSet f g) := by rw [sbSet_isFixed]; exact ha
  have : ¬ a ∉ Set.range g := fun h => hne (Or.inl h)
  exact not_not.mp this

open Classical in
/-- **Exercise 4.24 (Scott 1981, PRG-19).** Tarski's bijection `h : A → B`: `f` on
the fixed set
`X`, and the `g`-inverse off it. -/
noncomputable def sbFun (f : A → B) (g : B → A) (a : A) : B :=
  if ha : a ∈ sbSet f g then f a else Classical.choose (mem_range_of_not_mem ha)

theorem sbFun_mem {a : A} (ha : a ∈ sbSet f g) : sbFun f g a = f a := dif_pos ha

/-- Off the fixed set, `h(a)` is a genuine `g`-preimage of `a`: `g(h(a)) = a`. -/
theorem g_sbFun_not_mem {a : A} (ha : a ∉ sbSet f g) : g (sbFun f g a) = a := by
  rw [sbFun, dif_neg ha]
  exact Classical.choose_spec (mem_range_of_not_mem ha)

/-- `g(f(a)) ∈ X` whenever `a ∈ X` (the `g(f(X)) ⊆ T(X) = X` half). -/
theorem g_f_mem_of_mem {a : A} (ha : a ∈ sbSet f g) : g (f a) ∈ sbSet f g := by
  rw [← sbSet_isFixed]
  exact Or.inr ⟨f a, ⟨a, ha, rfl⟩, rfl⟩

theorem sbFun_injective (hf : Injective f) : Injective (sbFun f g) := by
  intro a₁ a₂ heq
  by_cases h1 : a₁ ∈ sbSet f g <;> by_cases h2 : a₂ ∈ sbSet f g
  · rw [sbFun_mem h1, sbFun_mem h2] at heq
    exact hf heq
  · -- `a₁ ∈ X`, `a₂ ∉ X`: `f a₁ = g⁻¹ a₂` ⟹ `a₂ = g(f a₁) ∈ X`, contradiction.
    exfalso
    rw [sbFun_mem h1] at heq
    have : a₂ = g (f a₁) := by rw [heq, g_sbFun_not_mem h2]
    exact h2 (this ▸ g_f_mem_of_mem h1)
  · exfalso
    rw [sbFun_mem h2] at heq
    have : a₁ = g (f a₂) := by rw [← heq, g_sbFun_not_mem h1]
    exact h1 (this ▸ g_f_mem_of_mem h2)
  · -- both off `X`: apply `g` and use injectivity of `g`.
    have : g (sbFun f g a₁) = g (sbFun f g a₂) := by rw [heq]
    rw [g_sbFun_not_mem h1, g_sbFun_not_mem h2] at this
    exact this

theorem sbFun_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  intro b
  by_cases hb : g b ∈ sbSet f g
  · -- `g b ∈ X = T X`; not in `(range g)ᶜ`, so `g b ∈ g(f(X))`.
    rw [← sbSet_isFixed] at hb
    rcases hb with hb | ⟨y, ⟨a, ha, rfl⟩, hgy⟩
    · exact absurd ⟨b, rfl⟩ hb
    · refine ⟨a, ?_⟩
      rw [sbFun_mem ha, hg hgy]
  · -- `g b ∉ X`: then `h (g b) = b`.
    refine ⟨g b, ?_⟩
    exact hg (g_sbFun_not_mem hb)

/-- **Exercise 4.24 (Scott 1981, PRG-19) — Schröder–Bernstein.** Injections `f : A
→ B` and
`g : B → A` yield a bijection `A → B`. -/
theorem schroeder_bernstein (hf : Injective f) (hg : Injective g) :
    ∃ h : A → B, Bijective h :=
  ⟨sbFun f g, sbFun_injective hf, sbFun_surjective hg⟩

/-- **Exercise 4.24 (Scott 1981, PRG-19).** The one-one correspondence as an
`Equiv A ≃ B`. -/
noncomputable def schroederBernsteinEquiv (hf : Injective f) (hg : Injective g) : A ≃ B :=
  Equiv.ofBijective (sbFun f g) ⟨sbFun_injective hf, sbFun_surjective hg⟩

end Domain.Neighborhood.Exercise424
