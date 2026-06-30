/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Theorem41
import LeanPool.DomainTheory.Neighborhood.ApproximableExercises

/-!
# Exercise 4.7 (Scott 1981, PRG-19, Lecture IV)

Formula 4.2(iii) gives the *least* fixed point `fix(f) = ⊔ₙ fⁿ(⊥)`. Suppose
instead that
`a ∈ |𝒟|` satisfies `a ⊑ f(a)`. *Will there be a fixed point `x = f(x)` with `a ⊑
x`?*

**Yes.** Replace `⊥` by `a`: the chain `a ⊑ f(a) ⊑ f²(a) ⊑ …` is increasing
(monotonicity of `f`
applied to `a ⊑ f(a)`), hence *directed*, so its union `x = ⊔ₙ fⁿ(a)` is a genuine
element of `|𝒟|`
(Scott's hint: this is why `⊔` makes sense — directed unions of filters are
filters, Exercise 2.11 /
`iSupDirected`). Approximable maps preserve directed unions
(`toElementMap_iSupDirected`), which makes
`x` a fixed point, and `a = f⁰(a) ⊑ x` by construction. Moreover `x` is the
*least* fixed point above
`a` (`fixAbove_least`), the relativized analogue of 4.2(iii).

All constructions are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The chain of approximants from a base point `a`: `iterFrom f a n = fⁿ(a)`. -/
def iterFrom (f : ApproximableMap V V) (a : V.Element) (n : ℕ) : V.Element :=
  (f.toElementMap)^[n] a

@[simp] theorem iterFrom_zero (f : ApproximableMap V V) (a : V.Element) :
    f.iterFrom a 0 = a := rfl

theorem iterFrom_succ (f : ApproximableMap V V) (a : V.Element) (n : ℕ) :
    f.iterFrom a (n + 1) = f.toElementMap (f.iterFrom a n) := by
  rw [iterFrom, iterFrom, Function.iterate_succ', Function.comp_apply]

/-- One step of the chain: `fⁿ(a) ⊑ fⁿ⁺¹(a)` (proved choice-free by induction). -/
theorem iterFrom_step (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    (n : ℕ) : f.iterFrom a n ≤ f.iterFrom a (n + 1) := by
  induction n with
  | zero => rw [iterFrom_succ f a 0, iterFrom_zero]; exact ha
  | succ k ih =>
    rw [iterFrom_succ f a k, iterFrom_succ f a (k + 1)]
    exact f.toElementMap_mono ih

/-- When `a ⊑ f(a)`, the chain `fⁿ(a)` is monotone: `n ≤ m ⟹ fⁿ(a) ⊑ fᵐ(a)`.
Proved by induction
on `n ≤ m` (so as to stay **choice-free**, unlike `monotone_nat_of_le_succ`). -/
theorem iterFrom_mono (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    {n m : ℕ} (hnm : n ≤ m) : f.iterFrom a n ≤ f.iterFrom a m := by
  induction hnm with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (iterFrom_step f ha _)

/-- The fixed point of `f` lying above a pre-fixed-point candidate `a` (with `a ⊑
f(a)`),
constructed as the directed union `⊔ₙ fⁿ(a)`. -/
def fixAbove (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) : V.Element :=
  NeighborhoodSystem.iSupDirected (f.iterFrom a)
    (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩)

/-- `a ⊑ fixAbove f ha`: the constructed fixed point lies above `a` (it is the `n
= 0` term). -/
theorem le_fixAbove (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) :
    a ≤ f.fixAbove ha := by
  have := NeighborhoodSystem.le_iSupDirected (f.iterFrom a)
    (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩) 0
  rwa [iterFrom_zero] at this

/-- **Exercise 4.7 (Scott 1981, PRG-19).** `fixAbove f ha` is a fixed point: `f(x)
= x`. -/
theorem fixAbove_isFixed (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) :
    f.toElementMap (f.fixAbove ha) = f.fixAbove ha := by
  set hdir := (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
    iterFrom_mono f ha (le_max_right i j)⟩ :
    ∀ i j, ∃ k, f.iterFrom a i ≤ f.iterFrom a k ∧ f.iterFrom a j ≤ f.iterFrom a k) with hdir_def
  apply le_antisymm
  · -- `f(x) = ⊔ₙ f(fⁿ(a)) = ⊔ₙ f^{n+1}(a) ⊑ x` since each `f^{n+1}(a) ⊑ x`.
    rw [fixAbove, toElementMap_iSupDirected]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    have : f.toElementMap (f.iterFrom a n) = f.iterFrom a (n + 1) := (iterFrom_succ f a n).symm
    rw [this]
    exact NeighborhoodSystem.le_iSupDirected (f.iterFrom a) hdir (n + 1)
  · -- `x ⊑ f(x)`: each `fⁿ(a) ⊑ fⁿ⁺¹(a) = f(fⁿ(a)) ⊑ f(x)`.
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    calc f.iterFrom a n
        ≤ f.iterFrom a (n + 1) := iterFrom_mono f ha (Nat.le_succ n)
      _ = f.toElementMap (f.iterFrom a n) := iterFrom_succ f a n
      _ ≤ f.toElementMap (f.fixAbove ha) :=
          f.toElementMap_mono (NeighborhoodSystem.le_iSupDirected (f.iterFrom a) hdir n)

/-- **Exercise 4.7 (Scott 1981, PRG-19).** `fixAbove f ha` is the *least* fixed
point above `a`:
any `z` with `a ⊑ z` and `f(z) ⊑ z` lies above it. (Relativized form of 4.2(iii).) -/
theorem fixAbove_least (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    {z : V.Element} (haz : a ≤ z) (hz : f.toElementMap z ≤ z) : f.fixAbove ha ≤ z := by
  apply NeighborhoodSystem.iSupDirected_le
  intro n
  induction n with
  | zero => rwa [iterFrom_zero]
  | succ k ih =>
    rw [iterFrom_succ]
    exact le_trans (f.toElementMap_mono ih) hz

end ApproximableMap

end Domain.Neighborhood
