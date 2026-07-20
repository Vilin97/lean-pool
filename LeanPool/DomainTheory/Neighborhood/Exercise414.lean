/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Exercise 4.14 (Scott 1981, PRG-19, Lecture IV) — `P A` has a maximum fixed point

*Need a monotone function `f : P A → P A` always have a **maximum** fixed point?*

**Yes.** Contrast this with Exercise 4.12, where a general domain `𝒟` admits
monotone (indeed
approximable) maps `f : 𝒟 → 𝒟` with no greatest fixed point. The reason is that `P
A` — the
power-set domain, whose elements are *arbitrary* subsets of `A` ordered by
inclusion — is a
**complete lattice**: arbitrary unions and intersections exist. So both halves of
the
Knaster–Tarski theorem apply.

* **Greatest fixed point** (this exercise): `gfpSet f = ⋃ {x ∣ x ⊆ f(x)}` (the
union of the
  *post*-fixed points) is a fixed point and dominates every fixed point
  (`gfpSet_isFixed`,
  `gfpSet_greatest`).
* **Least fixed point** (Exercise 4.13(2), the dual): `lfpSet f = ⋂ {x ∣ f(x) ⊆
x}` (the
  intersection of the *pre*-fixed points) is a fixed point and is dominated by
  every fixed point
  (`lfpSet_isFixed`, `lfpSet_least`). This is exactly Scott's remark 4.13(2) that
  the intersection
  construction "can always be applied to power-set domains `P A`" — here `a = A`
  is the automatic
  pre-fixed point `f(A) ⊆ A`.

Both constructions use **only monotonicity** and the complete-lattice structure of
`P A`; they are
entirely **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood.Exercise414

variable {A : Type*}

/-! ### Greatest fixed point — the answer to Exercise 4.14. -/

/-- **Exercise 4.14 (Scott 1981, PRG-19).** The *greatest* fixed point of a
monotone `f : P A →
P A`,
constructed as the union of all post-fixed points `⋃ {x ∣ x ⊆ f(x)}`. -/
def gfpSet (f : Set A → Set A) : Set A := {a | ∃ x : Set A, x ⊆ f x ∧ a ∈ x}

/-- Every post-fixed point `x ⊆ f(x)` is contained in `gfpSet f`. -/
theorem subset_gfpSet (f : Set A → Set A) {x : Set A} (hx : x ⊆ f x) : x ⊆ gfpSet f :=
  fun _ ha => ⟨x, hx, ha⟩

/-- `gfpSet f ⊆ f (gfpSet f)`: it is a post-fixed point. -/
theorem gfpSet_subset_f (f : Set A → Set A) (hf : Monotone f) :
    gfpSet f ⊆ f (gfpSet f) := by
  rintro a ⟨x, hx, hax⟩
  exact hf (subset_gfpSet f hx) (hx hax)

/-- **Exercise 4.14 (Scott 1981, PRG-19).** `gfpSet f` is a fixed point: `f(g) =
g`. -/
theorem gfpSet_isFixed (f : Set A → Set A) (hf : Monotone f) :
    f (gfpSet f) = gfpSet f := by
  have hsub : gfpSet f ⊆ f (gfpSet f) := gfpSet_subset_f f hf
  have hsup : f (gfpSet f) ⊆ gfpSet f := subset_gfpSet f (hf hsub)
  exact Set.Subset.antisymm hsup hsub

/-- **Exercise 4.14 (Scott 1981, PRG-19).** `gfpSet f` is the *greatest* fixed
point: any fixed
point `y = f(y)` satisfies `y ⊆ g`. Hence `f` *does* have a maximum fixed point. -/
theorem gfpSet_greatest (f : Set A → Set A) {y : Set A} (hy : f y = y) :
    y ⊆ gfpSet f := subset_gfpSet f (le_of_eq hy.symm)

/-! ### Least fixed point — the dual, realizing Exercise 4.13(2) on `P A`. -/

/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** The *least* fixed point of a
monotone `f : P A →
P A`,
as the intersection of all pre-fixed points `⋂ {x ∣ f(x) ⊆ x}`. -/
def lfpSet (f : Set A → Set A) : Set A := {a | ∀ x : Set A, f x ⊆ x → a ∈ x}

/-- `lfpSet f ⊆ x` for every pre-fixed point `f(x) ⊆ x`. -/
theorem lfpSet_subset (f : Set A → Set A) {x : Set A} (hx : f x ⊆ x) : lfpSet f ⊆ x :=
  fun _ ha => ha x hx

/-- `f (lfpSet f) ⊆ lfpSet f`: it is a pre-fixed point. -/
theorem f_subset_lfpSet (f : Set A → Set A) (hf : Monotone f) :
    f (lfpSet f) ⊆ lfpSet f := by
  intro a ha x hx
  exact hx (hf (lfpSet_subset f hx) ha)

/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** `lfpSet f` is a fixed point: `f(b)
= b`. -/
theorem lfpSet_isFixed (f : Set A → Set A) (hf : Monotone f) :
    f (lfpSet f) = lfpSet f := by
  have hsub : f (lfpSet f) ⊆ lfpSet f := f_subset_lfpSet f hf
  have hsup : lfpSet f ⊆ f (lfpSet f) := lfpSet_subset f (hf hsub)
  exact Set.Subset.antisymm hsub hsup

/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** `lfpSet f` is the *least* fixed
point: any fixed
point `y = f(y)` satisfies `b ⊆ y`. -/
theorem lfpSet_least (f : Set A → Set A) {y : Set A} (hy : f y = y) :
    lfpSet f ⊆ y := lfpSet_subset f (le_of_eq hy)

end Domain.Neighborhood.Exercise414
