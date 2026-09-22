/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointBase
import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceFinitePlaceIncrement
import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceInfinityPlaceIncrement

/-!
# Successive growth of one-point Riemann spaces

The local residue argument bounds the jump from `L(nP)` to `L((n+1)P)` by
the degree of `P`. Iterating from `L(0)` also supplies finite-dimensionality
at every level of the one-point filtration.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- One step in the one-point filtration is finite-dimensional and has
dimension jump at most the degree of the distinguished place. -/
theorem finiteExtensionOnePointRiemannSpace_increment
    (P : FiniteExtensionPlace K L) (n : ℕ)
    [Module.Finite K (finiteExtensionOnePointRiemannSpace K L P n)] :
    Module.Finite K
        (finiteExtensionOnePointRiemannSpace K L P (n + 1)) ∧
      Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P (n + 1)) ≤
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P n) +
          finiteExtensionPlaceDegree K L P := by
  classical
  change Module.Finite K
      (finiteExtensionRiemannSpace K L
        (Finsupp.single P ((n + 1 : ℕ) : ℤ))) ∧
    Module.finrank K
        (finiteExtensionRiemannSpace K L
          (Finsupp.single P ((n + 1 : ℕ) : ℤ))) ≤
      Module.finrank K
          (finiteExtensionRiemannSpace K L
            (Finsupp.single P (n : ℤ))) +
        finiteExtensionPlaceDegree K L P
  have hD : ∀ v, 0 ≤ (Finsupp.single P (n : ℤ) :
      FiniteExtensionDivisor K L) v := by
    intro v
    by_cases hv : v = P
    · subst v
      simp
    · simp [Finsupp.single_eq_of_ne hv]
  rcases P with q | q
  · have hbase : Module.Finite K
        (finiteExtensionRiemannSpace K L
          (Finsupp.single (.inl q) (n : ℤ))) := by
      change Module.Finite K
        (finiteExtensionOnePointRiemannSpace K L (.inl q) n)
      infer_instance
    let := hbase
    have h := finiteExtensionRiemannSpace_finitePlace_increment
      K L (Finsupp.single (.inl q) (n : ℤ)) hD q
    have hdivisor :
        Finsupp.single (.inl q) (n : ℤ) + Finsupp.single (.inl q) 1 =
          (Finsupp.single (.inl q) ((n + 1 : ℕ) : ℤ) :
            FiniteExtensionDivisor K L) := by
      ext v
      by_cases hv : v = (.inl q : FiniteExtensionPlace K L)
      · subst v
        simp
      · simp [Finsupp.single_eq_of_ne hv]
    rw [hdivisor] at h
    exact h
  · have hbase : Module.Finite K
        (finiteExtensionRiemannSpace K L
          (Finsupp.single (.inr q) (n : ℤ))) := by
      change Module.Finite K
        (finiteExtensionOnePointRiemannSpace K L (.inr q) n)
      infer_instance
    let := hbase
    have h := finiteExtensionRiemannSpace_infinityPlace_increment
      K L (Finsupp.single (.inr q) (n : ℤ)) hD q
    have hdivisor :
        Finsupp.single (.inr q) (n : ℤ) + Finsupp.single (.inr q) 1 =
          (Finsupp.single (.inr q) ((n + 1 : ℕ) : ℤ) :
            FiniteExtensionDivisor K L) := by
      ext v
      by_cases hv : v = (.inr q : FiniteExtensionPlace K L)
      · subst v
        simp
      · simp [Finsupp.single_eq_of_ne hv]
    rw [hdivisor] at h
    exact h

/-- Every member of a one-point Riemann filtration is finite-dimensional. -/
theorem finiteExtensionOnePointRiemannSpace_moduleFinite
    (P : FiniteExtensionPlace K L) :
    ∀ n, Module.Finite K
      (finiteExtensionOnePointRiemannSpace K L P n) := by
  intro n
  induction n with
  | zero =>
      exact finiteExtensionOnePointRiemannSpace_zero_moduleFinite K L P
  | succ n ih =>
      let : Module.Finite K
          (finiteExtensionOnePointRiemannSpace K L P n) := ih
      exact (finiteExtensionOnePointRiemannSpace_increment K L P n).1

/-- Uniform dimension-jump bound for the one-point filtration. -/
theorem finiteExtensionOnePointRiemannSpace_finrank_succ_le
    (P : FiniteExtensionPlace K L) (n : ℕ) :
    Module.finrank K
        (finiteExtensionOnePointRiemannSpace K L P (n + 1)) ≤
      Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P n) +
        finiteExtensionPlaceDegree K L P := by
  let : Module.Finite K
      (finiteExtensionOnePointRiemannSpace K L P n) :=
    finiteExtensionOnePointRiemannSpace_moduleFinite K L P n
  exact (finiteExtensionOnePointRiemannSpace_increment K L P n).2

end

end BGS.HasseWeil
