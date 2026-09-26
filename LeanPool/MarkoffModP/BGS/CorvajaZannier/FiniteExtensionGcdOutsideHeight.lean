/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalPlaceSum
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionExhaustiveGcdDivisorBound
public import Mathlib.Tactic

/-! The gcd divisor is controlled by the poles of the one-minus quotient. -/

@[expose] public section

open scoped BigOperators

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

attribute [local instance] Classical.decEq

omit [DecidableEq K] [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- The local integer identity behind the Corvaja--Zannier comparison between
the gcd divisor and the pole height of `(1-u)/(1-v)`. -/
theorem gcdMultiplicity_add_outsidePole_le_secondPositivePart
    (S : Finset (FiniteExtensionPlace K L))
    (Du Dv Drho : FiniteExtensionPlace K L → ℤ)
    (P : FiniteExtensionPlace K L)
    (hRho : Drho P = Du P - Dv P)
    (hOutside : P ∉ S → 0 ≤ Du P ∧ 0 ≤ Dv P)
    (hInside : P ∈ S → min (Du P) (Dv P) ≤ 0) :
    Int.toNat (min (Du P) (Dv P)) +
        (if P ∉ S ∧ Drho P < 0 then (Drho P).natAbs else 0) ≤
      Int.toNat (Dv P) := by
  by_cases hPS : P ∈ S
  · have hmin := hInside hPS
    have hminToNat : Int.toNat (min (Du P) (Dv P)) = 0 :=
      Int.toNat_of_nonpos hmin
    simp [hPS, hminToNat]
  · obtain ⟨hDu, hDv⟩ := hOutside hPS
    rw [hRho]
    by_cases hneg : Du P - Dv P < 0
    · simp only [hPS, not_false_eq_true, hneg, and_self, ite_eq_left]
      have hmin : min (Du P) (Dv P) = Du P :=
        min_eq_left (sub_nonpos.mp (le_of_lt hneg))
      have hcast :
          ((Int.toNat (min (Du P) (Dv P)) +
            (Du P - Dv P).natAbs : ℕ) : ℤ) ≤
            (Int.toNat (Dv P) : ℤ) := by
        rw [Nat.cast_add, Int.toNat_of_nonneg (le_min hDu hDv),
          Int.toNat_of_nonneg hDv, Int.natCast_natAbs,
          abs_of_nonpos (le_of_lt hneg), hmin]
        omega
      exact_mod_cast hcast
    · have hnonneg : 0 ≤ Du P - Dv P := le_of_not_gt hneg
      simp only [hPS, not_false_eq_true, hneg, and_false, ite_false, add_zero]
      exact Int.toNat_le_toNat (min_le_right _ _)

/-- If the local order of `rho` is the difference of the two one-minus
orders, those one-minus orders are nonnegative off `S`, and their minimum is
nonpositive on `S`, then gcd degree plus outside pole height is bounded by the
positive degree of the second one-minus function. -/
theorem finiteExtensionGcdWeightedDegree_add_outsideHeight_le
    (x y rho : L) (S : Finset (FiniteExtensionPlace K L))
    (hRho : ∀ P, finiteExtensionPrincipalDivisor K L rho P =
      finiteExtensionPrincipalDivisor K L x P -
        finiteExtensionPrincipalDivisor K L y P)
    (hOutside : ∀ P, P ∉ S →
      0 ≤ finiteExtensionPrincipalDivisor K L x P ∧
      0 ≤ finiteExtensionPrincipalDivisor K L y P)
    (hInside : ∀ P, P ∈ S →
      min (finiteExtensionPrincipalDivisor K L x P)
        (finiteExtensionPrincipalDivisor K L y P) ≤ 0) :
    finiteExtensionGcdWeightedDegree K L x y +
        finiteExtensionOutsideHeight K L rho S ≤
      finiteExtensionPositiveDegree K L y := by
  classical
  let Dx := finiteExtensionPrincipalDivisor K L x
  let Dy := finiteExtensionPrincipalDivisor K L y
  let Drho := finiteExtensionPrincipalDivisor K L rho
  let T : Finset (FiniteExtensionPlace K L) :=
    S ∪ Dx.support ∪ Dy.support ∪ Drho.support
  have hGcdSupport : finiteExtensionGcdSupport K L x y ⊆ T := by
    intro P hP
    rcases Finset.mem_union.mp hP with hxP | hyP
    · simp [T, Dx, hxP]
    · simp [T, Dy, hyP]
  have hRhoSupport : Drho.support ⊆ T := by
    intro P hP
    simp [T, hP]
  have hYSupport : Dy.support ⊆ T := by
    intro P hP
    simp [T, hP]
  have hGcd : finiteExtensionGcdWeightedDegree K L x y =
      ∑ P ∈ T, Int.toNat (min (Dx P) (Dy P)) *
        finiteExtensionPlaceDegree K L P := by
    rw [finiteExtensionGcdWeightedDegree]
    apply Finset.sum_subset hGcdSupport
    intro P hPT hnot
    have hx0 : Dx P = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hxmem
      exact hnot (by
        rw [finiteExtensionGcdSupport]
        exact Finset.mem_union_left _ hxmem)
    have hy0 : Dy P = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hymem
      exact hnot (by
        rw [finiteExtensionGcdSupport]
        exact Finset.mem_union_right _ hymem)
    simp [finiteExtensionGcdMultiplicity, Dx, Dy, hx0, hy0]
  have hOutsideHeight : finiteExtensionOutsideHeight K L rho S =
      ∑ P ∈ T, (if P ∉ S ∧ Drho P < 0 then (Drho P).natAbs else 0) *
        finiteExtensionPlaceDegree K L P := by
    rw [finiteExtensionOutsideHeight]
    rw [Finset.sum_filter]
    change (∑ P ∈ Drho.support,
      if P ∉ S ∧ Drho P < 0 then
        (Drho P).natAbs * finiteExtensionPlaceDegree K L P else 0) = _
    calc
      _ = ∑ P ∈ Drho.support,
          (if P ∉ S ∧ Drho P < 0 then (Drho P).natAbs else 0) *
            finiteExtensionPlaceDegree K L P := by
              apply Finset.sum_congr rfl
              intro P hP
              split_ifs <;> simp
      _ = _ := by
        apply Finset.sum_subset hRhoSupport
        intro P hPT hnot
        have hzero : Drho P = 0 := Finsupp.notMem_support_iff.mp hnot
        simp [hzero]
  have hPositive : finiteExtensionPositiveDegree K L y =
      ∑ P ∈ T, Int.toNat (Dy P) * finiteExtensionPlaceDegree K L P := by
    rw [finiteExtensionPositiveDegree]
    rw [Finset.sum_filter]
    change (∑ P ∈ Dy.support,
      if 0 < Dy P then Int.toNat (Dy P) *
        finiteExtensionPlaceDegree K L P else 0) = _
    calc
      _ = ∑ P ∈ Dy.support, Int.toNat (Dy P) *
          finiteExtensionPlaceDegree K L P := by
            apply Finset.sum_congr rfl
            intro P hP
            by_cases hpos : 0 < Dy P
            · simp [hpos]
            · have hnonpos : Dy P ≤ 0 := le_of_not_gt hpos
              simp [hpos, Int.toNat_of_nonpos hnonpos]
      _ = _ := by
        apply Finset.sum_subset hYSupport
        intro P hPT hnot
        have hzero : Dy P = 0 := Finsupp.notMem_support_iff.mp hnot
        simp [hzero]
  rw [hGcd, hOutsideHeight, hPositive, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro P hPT
  have hlocal := gcdMultiplicity_add_outsidePole_le_secondPositivePart
    K L S Dx Dy Drho P (hRho P) (hOutside P) (hInside P)
  calc
    Int.toNat (min (Dx P) (Dy P)) * finiteExtensionPlaceDegree K L P +
        (if P ∉ S ∧ Drho P < 0 then (Drho P).natAbs else 0) *
          finiteExtensionPlaceDegree K L P =
      (Int.toNat (min (Dx P) (Dy P)) +
        (if P ∉ S ∧ Drho P < 0 then (Drho P).natAbs else 0)) *
          finiteExtensionPlaceDegree K L P := by rw [add_mul]
    _ ≤ Int.toNat (Dy P) * finiteExtensionPlaceDegree K L P :=
      Nat.mul_le_mul_right (finiteExtensionPlaceDegree K L P) hlocal

end

end BGS.CorvajaZannier
