/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointDivisorSplit
import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceInfinityPlaceIncrement
import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceConstants
import Mathlib.Tactic

/-!
# Effective increments of exhaustive Riemann spaces

The local finite- and infinity-place residue maps give the same one-place
dimension bound.  This file first packages those two cases as a bound for an
arbitrary exhaustive place, then iterates over the coefficients and support
of an effective divisor.

The final statements split an effective divisor at one selected place.  They
are the linear-algebraic codimension estimates needed to pass from a
many-pole auxiliary space to a one-point Riemann space.
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

/-- The finite- and infinity-place increment lemmas together cover every
place in the exhaustive place type. -/
theorem finiteExtensionRiemannSpace_place_increment
    (D : FiniteExtensionDivisor K L)
    (hD : ∀ v, 0 ≤ D v)
    (P : FiniteExtensionPlace K L)
    [Module.Finite K (finiteExtensionRiemannSpace K L D)] :
    Module.Finite K (finiteExtensionRiemannSpace K L
      (D + Finsupp.single P 1)) ∧
    Module.finrank K (finiteExtensionRiemannSpace K L
      (D + Finsupp.single P 1)) ≤
      Module.finrank K (finiteExtensionRiemannSpace K L D) +
        finiteExtensionPlaceDegree K L P := by
  rcases P with q | P
  · simpa using
      (finiteExtensionRiemannSpace_finitePlace_increment K L D hD q)
  · simpa using
      (finiteExtensionRiemannSpace_infinityPlace_increment K L D hD P)

/-- Adding `n` copies of one place raises dimension by at most `n` times the
degree of that place. -/
theorem finiteExtensionRiemannSpace_natPlace_increment
    (D : FiniteExtensionDivisor K L)
    (hD : ∀ v, 0 ≤ D v)
    (P : FiniteExtensionPlace K L)
    (n : ℕ)
    [Module.Finite K (finiteExtensionRiemannSpace K L D)] :
    Module.Finite K (finiteExtensionRiemannSpace K L
      (D + Finsupp.single P (n : ℤ))) ∧
    Module.finrank K (finiteExtensionRiemannSpace K L
      (D + Finsupp.single P (n : ℤ))) ≤
      Module.finrank K (finiteExtensionRiemannSpace K L D) +
        n * finiteExtensionPlaceDegree K L P := by
  induction n with
  | zero =>
      have hdivisor :
          D + Finsupp.single P (((0 : ℕ) : ℤ)) = D := by
        ext v
        simp
      rw [hdivisor]
      simp only [zero_mul, add_zero]
      constructor
      · exact inferInstance
      · exact le_rfl
  | succ n ih =>
      let E : FiniteExtensionDivisor K L :=
        D + Finsupp.single P (n : ℤ)
      have hE : ∀ v, 0 ≤ E v := by
        intro v
        by_cases hv : v = P
        · subst v
          dsimp only [E]
          simp only [Finsupp.add_apply, Finsupp.single_eq_same]
          exact add_nonneg (hD P) (by positivity)
        · simpa [E, Finsupp.single_eq_of_ne hv] using hD v
      letI : Module.Finite K (finiteExtensionRiemannSpace K L E) := ih.1
      have hstep := finiteExtensionRiemannSpace_place_increment K L E hE P
      have hdivisor :
          D + Finsupp.single P ((n + 1 : ℕ) : ℤ) =
            E + Finsupp.single P 1 := by
        ext v
        by_cases hv : v = P
        · subst v
          simp only [E, Finsupp.add_apply, Finsupp.single_eq_same]
          push_cast
          ring
        · simp only [E, Finsupp.add_apply,
            Finsupp.single_eq_of_ne hv]
          ring
      constructor
      · rw [hdivisor]
        exact hstep.1
      · rw [hdivisor]
        calc
          Module.finrank K (finiteExtensionRiemannSpace K L
              (E + Finsupp.single P 1)) ≤
              Module.finrank K (finiteExtensionRiemannSpace K L E) +
                finiteExtensionPlaceDegree K L P := hstep.2
          _ ≤ (Module.finrank K (finiteExtensionRiemannSpace K L D) +
                n * finiteExtensionPlaceDegree K L P) +
                finiteExtensionPlaceDegree K L P :=
              Nat.add_le_add_right ih.2 _
          _ = Module.finrank K (finiteExtensionRiemannSpace K L D) +
                (n + 1) * finiteExtensionPlaceDegree K L P := by
              simp only [Nat.add_mul, one_mul]
              omega

/-- Adding an effective divisor to an effective starting divisor preserves
finite-dimensionality, and its total dimension cost is at most its degree. -/
theorem finiteExtensionRiemannSpace_add_effective
    (D E : FiniteExtensionDivisor K L)
    (hD : ∀ v, 0 ≤ D v)
    (hE : ∀ v, 0 ≤ E v)
    [Module.Finite K (finiteExtensionRiemannSpace K L D)] :
    Module.Finite K (finiteExtensionRiemannSpace K L (D + E)) ∧
    Module.finrank K (finiteExtensionRiemannSpace K L (D + E)) ≤
      Module.finrank K (finiteExtensionRiemannSpace K L D) +
        (finiteExtensionDivisorDegree K L E).toNat := by
  let motive := fun E : FiniteExtensionDivisor K L =>
    (∀ v, 0 ≤ E v) →
      Module.Finite K (finiteExtensionRiemannSpace K L (D + E)) ∧
      Module.finrank K (finiteExtensionRiemannSpace K L (D + E)) ≤
        Module.finrank K (finiteExtensionRiemannSpace K L D) +
          (finiteExtensionDivisorDegree K L E).toNat
  apply Finsupp.induction E (motive := motive)
  · intro _
    rw [add_zero]
    constructor
    · exact inferInstance
    · exact le_rfl
  · intro P b E hP hb ih hsingleAdd
    have hEP : E P = 0 := Finsupp.notMem_support_iff.mp hP
    have hbNonneg : 0 ≤ b := by
      have h := hsingleAdd P
      simpa [hEP] using h
    have hEeffective : ∀ v, 0 ≤ E v := by
      intro v
      by_cases hv : v = P
      · subst v
        simp [hEP]
      · have h := hsingleAdd v
        simpa [Finsupp.single_eq_of_ne hv] using h
    have hih := ih hEeffective
    letI : Module.Finite K
        (finiteExtensionRiemannSpace K L (D + E)) := hih.1
    have hDEeffective : ∀ v, 0 ≤ (D + E) v := by
      intro v
      exact add_nonneg (hD v) (hEeffective v)
    have hmultiple := finiteExtensionRiemannSpace_natPlace_increment
      K L (D + E) hDEeffective P b.toNat
    have hdivisor :
        D + (Finsupp.single P b + E) =
          (D + E) + Finsupp.single P (b.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hbNonneg]
      abel
    have hdegreeE : 0 ≤ finiteExtensionDivisorDegree K L E :=
      finiteExtensionDivisorDegree_nonnegative_of_effective K L E hEeffective
    have hdegreeSingle :
        0 ≤ b * (finiteExtensionPlaceDegree K L P : ℤ) :=
      mul_nonneg hbNonneg (by positivity)
    have hdegree :
        (finiteExtensionDivisorDegree K L
            (Finsupp.single P b + E)).toNat =
          b.toNat * finiteExtensionPlaceDegree K L P +
            (finiteExtensionDivisorDegree K L E).toNat := by
      rw [finiteExtensionDivisorDegree_add,
        finiteExtensionDivisorDegree_single,
        Int.toNat_add hdegreeSingle hdegreeE,
        Int.toNat_mul hbNonneg (by positivity)]
      simp
    constructor
    · rw [hdivisor]
      exact hmultiple.1
    · rw [hdivisor]
      calc
        Module.finrank K (finiteExtensionRiemannSpace K L
            ((D + E) + Finsupp.single P (b.toNat : ℤ))) ≤
            Module.finrank K (finiteExtensionRiemannSpace K L (D + E)) +
              b.toNat * finiteExtensionPlaceDegree K L P := hmultiple.2
        _ ≤ (Module.finrank K (finiteExtensionRiemannSpace K L D) +
              (finiteExtensionDivisorDegree K L E).toNat) +
              b.toNat * finiteExtensionPlaceDegree K L P :=
            Nat.add_le_add_right hih.2 _
        _ = Module.finrank K (finiteExtensionRiemannSpace K L D) +
              (finiteExtensionDivisorDegree K L
                (Finsupp.single P b + E)).toNat := by omega
  exact hE

/-- Every effective exhaustive divisor has a finite-dimensional Riemann
space. -/
theorem finiteExtensionRiemannSpace_effective_moduleFinite
    (D : FiniteExtensionDivisor K L)
    (hD : ∀ v, 0 ≤ D v) :
    Module.Finite K (finiteExtensionRiemannSpace K L D) := by
  letI : Module.Finite K
      (finiteExtensionRiemannSpace K L (0 : FiniteExtensionDivisor K L)) :=
    finiteExtensionRiemannSpace_zero_moduleFinite K L
  have h := finiteExtensionRiemannSpace_add_effective K L
    (0 : FiniteExtensionDivisor K L) D (by simp) hD
  rw [zero_add] at h
  exact h.1

/-- Splitting an effective divisor at `P`, the discarded poles cost at most
the degree of the away part. -/
theorem finiteExtensionRiemannSpace_finrank_le_onePoint_add_degreeAway
    (D : FiniteExtensionDivisor K L)
    (hD : ∀ v, 0 ≤ D v)
    (P : FiniteExtensionPlace K L) :
    Module.finrank K (finiteExtensionRiemannSpace K L D) ≤
      Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P (D P).toNat) +
        (finiteExtensionDivisorDegree K L
          (finiteExtensionDivisorAway K L D P)).toNat := by
  let A : FiniteExtensionDivisor K L := Finsupp.single P (D P)
  let B : FiniteExtensionDivisor K L := finiteExtensionDivisorAway K L D P
  have hA : ∀ v, 0 ≤ A v := by
    intro v
    by_cases hv : v = P
    · subst v
      simpa [A] using hD P
    · simp [A, Finsupp.single_eq_of_ne hv]
  have hB : ∀ v, 0 ≤ B v := by
    exact finiteExtensionDivisorAway_effective K L D P hD
  letI : Module.Finite K (finiteExtensionRiemannSpace K L A) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L A hA
  have hbound := finiteExtensionRiemannSpace_add_effective K L A B hA hB
  have hsplit : A + B = D := by
    exact single_add_finiteExtensionDivisorAway K L D P
  have hcoeff : ((D P).toNat : ℤ) = D P :=
    Int.toNat_of_nonneg (hD P)
  rw [hsplit] at hbound
  change Module.finrank K (finiteExtensionRiemannSpace K L D) ≤
    Module.finrank K (finiteExtensionRiemannSpace K L
      (Finsupp.single P ((D P).toNat : ℤ))) +
      (finiteExtensionDivisorDegree K L
        (finiteExtensionDivisorAway K L D P)).toNat
  rw [hcoeff]
  simpa only [A, B] using hbound.2

/-- Rearranged form of the away-degree estimate: the selected one-point
space retains at least the full dimension minus the away degree. -/
theorem finiteExtensionOnePointRiemannSpace_finrank_lowerBound
    (D : FiniteExtensionDivisor K L)
    (hD : ∀ v, 0 ≤ D v)
    (P : FiniteExtensionPlace K L) :
    Module.finrank K (finiteExtensionRiemannSpace K L D) -
        (finiteExtensionDivisorDegree K L
          (finiteExtensionDivisorAway K L D P)).toNat ≤
      Module.finrank K
        (finiteExtensionOnePointRiemannSpace K L P (D P).toNat) := by
  have h := finiteExtensionRiemannSpace_finrank_le_onePoint_add_degreeAway
    K L D hD P
  omega

end

end BGS.HasseWeil
