/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import LeanPool.OperatorTheory.Operator.NumericalRange.Bounded

/-!
# The numerical radius

This file proves the classical sharp comparison between the numerical radius
and the operator norm:

`numericalRadius A ≤ ‖A‖ ≤ 2 * numericalRadius A`.

The reverse estimate is independent of completeness.  Its proof first
homogenizes the unit-vector definition of the numerical range, then applies
the complex polarization identity to the quadratic form
`x ↦ ⟪x, A x⟫_ℂ`.
-/

@[expose] public section

open Complex
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The quadratic form of an operator at an arbitrary vector is bounded by
the numerical radius times the squared norm. -/
theorem norm_inner_apply_self_le_numericalRadius_mul_norm_sq
    (A : E →L[ℂ] E) (x : E) :
    ‖⟪x, A x⟫_ℂ‖ ≤ numericalRadius A * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, inner_zero_left, norm_zero]
    exact mul_nonneg (numericalRadius_nonneg A) (sq_nonneg 0)
  · let u : E := NormedSpace.normalize x
    have hu : ‖u‖ = 1 := by
      exact NormedSpace.norm_normalize hx
    have huW : ⟪u, A u⟫_ℂ ∈ numericalRange A :=
      (mem_numericalRange A _).mpr ⟨u, hu, rfl⟩
    have hrad : ‖⟪u, A u⟫_ℂ‖ ≤ numericalRadius A :=
      norm_le_numericalRadius A huW
    have hxrepr : (‖x‖ : ℂ) • u = x := by
      change ‖x‖ • NormedSpace.normalize x = x
      exact NormedSpace.norm_smul_normalize x
    have hq :
        ‖⟪x, A x⟫_ℂ‖ = ‖x‖ ^ 2 * ‖⟪u, A u⟫_ℂ‖ := by
      conv_lhs => rw [← hxrepr]
      simp only [map_smul, inner_smul_left, inner_smul_right,
        Complex.conj_ofReal, norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x)]
      ring
    rw [hq]
    exact mul_le_mul_of_nonneg_left hrad (sq_nonneg ‖x‖) |>.trans_eq
      (mul_comm _ _)

/-- Polarization upgrades the diagonal numerical-radius estimate to every
matrix coefficient. -/
theorem norm_inner_apply_le_numericalRadius_mul_add_sq
    (A : E →L[ℂ] E) (x y : E) :
    ‖⟪y, A x⟫_ℂ‖ ≤
      numericalRadius A * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hq (v : E) :
      ‖⟪A v, v⟫_ℂ‖ ≤ numericalRadius A * ‖v‖ ^ 2 := by
    rw [norm_inner_symm]
    exact norm_inner_apply_self_le_numericalRadius_mul_norm_sq A v
  rw [norm_inner_symm y (A x)]
  change ‖⟪A.toLinearMap x, y⟫_ℂ‖ ≤ _
  rw [inner_map_polarization A.toLinearMap y x, norm_div, norm_ofNat]
  let a := ⟪A (y + x), y + x⟫_ℂ
  let b := ⟪A (y - x), y - x⟫_ℂ
  let c := ⟪A (y + Complex.I • x), y + Complex.I • x⟫_ℂ
  let d := ⟪A (y - Complex.I • x), y - Complex.I • x⟫_ℂ
  change ‖a - b + Complex.I * c - Complex.I * d‖ / 4 ≤ _
  have habcd :
      ‖a - b + Complex.I * c - Complex.I * d‖ ≤
        ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc
      ‖a - b + Complex.I * c - Complex.I * d‖ ≤
          ‖a - b + Complex.I * c‖ + ‖Complex.I * d‖ := norm_sub_le _ _
      _ ≤ (‖a - b‖ + ‖Complex.I * c‖) + ‖Complex.I * d‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
        gcongr
        exact norm_sub_le _ _
      _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by ring
  have ha : ‖a‖ ≤ numericalRadius A * ‖y + x‖ ^ 2 := hq _
  have hb : ‖b‖ ≤ numericalRadius A * ‖y - x‖ ^ 2 := hq _
  have hc :
      ‖c‖ ≤ numericalRadius A * ‖y + Complex.I • x‖ ^ 2 := hq _
  have hd :
      ‖d‖ ≤ numericalRadius A * ‖y - Complex.I • x‖ ^ 2 := hq _
  have htotal :
      ‖y + x‖ ^ 2 + ‖y - x‖ ^ 2 +
          ‖y + Complex.I • x‖ ^ 2 + ‖y - Complex.I • x‖ ^ 2 =
        4 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have hreal := parallelogram_law_with_norm ℂ y x
    have himag := parallelogram_law_with_norm ℂ y (Complex.I • x)
    rw [norm_smul, Complex.norm_I, one_mul] at himag
    linarith
  have hsum :
      ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ ≤
        4 * numericalRadius A * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    calc
      ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ ≤
          numericalRadius A * ‖y + x‖ ^ 2 +
          numericalRadius A * ‖y - x‖ ^ 2 +
          numericalRadius A * ‖y + Complex.I • x‖ ^ 2 +
          numericalRadius A * ‖y - Complex.I • x‖ ^ 2 := by
        gcongr
      _ = numericalRadius A *
          (‖y + x‖ ^ 2 + ‖y - x‖ ^ 2 +
            ‖y + Complex.I • x‖ ^ 2 +
            ‖y - Complex.I • x‖ ^ 2) := by ring
      _ = 4 * numericalRadius A * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
        rw [htotal]
        ring
  calc
    ‖a - b + Complex.I * c - Complex.I * d‖ / 4 ≤
        (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) / 4 := by gcongr
    _ ≤ (4 * numericalRadius A * (‖x‖ ^ 2 + ‖y‖ ^ 2)) / 4 := by
      gcongr
    _ = numericalRadius A * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by ring

/-- On a unit vector, the operator is bounded by twice its numerical radius. -/
theorem norm_apply_le_two_mul_numericalRadius_of_norm_eq_one
    (A : E →L[ℂ] E) {x : E} (hx : ‖x‖ = 1) :
    ‖A x‖ ≤ 2 * numericalRadius A := by
  by_cases hAx : A x = 0
  · rw [hAx, norm_zero]
    exact mul_nonneg zero_le_two (numericalRadius_nonneg A)
  · let y : E := NormedSpace.normalize (A x)
    have hy : ‖y‖ = 1 := NormedSpace.norm_normalize hAx
    have hrepr : (‖A x‖ : ℂ) • y = A x := by
      change ‖A x‖ • NormedSpace.normalize (A x) = A x
      exact NormedSpace.norm_smul_normalize (A x)
    have hinner : ‖⟪y, A x⟫_ℂ‖ = ‖A x‖ := by
      conv_lhs => rw [← hrepr]
      rw [inner_smul_right, inner_self_eq_one_of_norm_eq_one hy,
        mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (A x))]
    have hpolar := norm_inner_apply_le_numericalRadius_mul_add_sq A x y
    rw [hinner, hx, hy] at hpolar
    norm_num at hpolar
    simpa only [mul_comm] using hpolar

/-- Pointwise sharp comparison of the operator norm and numerical radius. -/
theorem norm_apply_le_two_mul_numericalRadius
    (A : E →L[ℂ] E) (x : E) :
    ‖A x‖ ≤ (2 * numericalRadius A) * ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, norm_zero, mul_zero, le_refl]
  · let u : E := NormedSpace.normalize x
    have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hx
    have hxrepr : (‖x‖ : ℂ) • u = x := by
      change ‖x‖ • NormedSpace.normalize x = x
      exact NormedSpace.norm_smul_normalize x
    have hunit : ‖A u‖ ≤ 2 * numericalRadius A :=
      norm_apply_le_two_mul_numericalRadius_of_norm_eq_one A hu
    calc
      ‖A x‖ = ‖x‖ * ‖A u‖ := by
        conv_lhs => rw [← hxrepr]
        rw [map_smul, norm_smul, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg x)]
      _ ≤ ‖x‖ * (2 * numericalRadius A) :=
        mul_le_mul_of_nonneg_left hunit (norm_nonneg x)
      _ = (2 * numericalRadius A) * ‖x‖ := by ring

/-- The operator norm is at most twice the numerical radius.  Together with
`numericalRadius_le_norm`, this is the classical sharp norm equivalence. -/
theorem norm_le_two_mul_numericalRadius (A : E →L[ℂ] E) :
    ‖A‖ ≤ 2 * numericalRadius A := by
  exact A.opNorm_le_bound
    (mul_nonneg zero_le_two (numericalRadius_nonneg A))
      (norm_apply_le_two_mul_numericalRadius A)

/-- The numerical radius vanishes exactly for the zero operator. -/
theorem numericalRadius_eq_zero_iff (A : E →L[ℂ] E) :
    numericalRadius A = 0 ↔ A = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    apply le_antisymm
    · simpa only [h, mul_zero] using norm_le_two_mul_numericalRadius A
    · exact norm_nonneg A
  · intro h
    subst A
    apply le_antisymm
    · simpa only [norm_zero] using
        numericalRadius_le_norm (0 : E →L[ℂ] E)
    · exact numericalRadius_nonneg (0 : E →L[ℂ] E)

/-- The numerical radius is positive exactly for nonzero operators. -/
theorem numericalRadius_pos_iff (A : E →L[ℂ] E) :
    0 < numericalRadius A ↔ A ≠ 0 := by
  rw [(numericalRadius_nonneg A).lt_iff_ne]
  simpa only [ne_eq, eq_comm] using
    not_congr (numericalRadius_eq_zero_iff A)

@[simp] theorem numericalRadius_zero :
    numericalRadius (0 : E →L[ℂ] E) = 0 :=
  (numericalRadius_eq_zero_iff (0 : E →L[ℂ] E)).2 rfl

/-- Numerical radius is subadditive. -/
theorem numericalRadius_add_le (A B : E →L[ℂ] E) :
    numericalRadius (A + B) ≤ numericalRadius A + numericalRadius B := by
  unfold numericalRadius
  refine Real.iSup_le (fun z => ?_)
    (add_nonneg (numericalRadius_nonneg A) (numericalRadius_nonneg B))
  refine Real.iSup_le (fun hz => ?_)
    (add_nonneg (numericalRadius_nonneg A) (numericalRadius_nonneg B))
  obtain ⟨x, hx, rfl⟩ := (mem_numericalRange (A + B) z).mp hz
  simp only [add_apply, inner_add_right]
  calc
    ‖⟪x, A x⟫_ℂ + ⟪x, B x⟫_ℂ‖ ≤
        ‖⟪x, A x⟫_ℂ‖ + ‖⟪x, B x⟫_ℂ‖ := norm_add_le _ _
    _ ≤ numericalRadius A + numericalRadius B := by
      gcongr
      · exact norm_le_numericalRadius A
          ((mem_numericalRange A _).2 ⟨x, hx, rfl⟩)
      · exact norm_le_numericalRadius B
          ((mem_numericalRange B _).2 ⟨x, hx, rfl⟩)

/-- One half of absolute homogeneity of the numerical radius. -/
theorem numericalRadius_smul_le (c : ℂ) (A : E →L[ℂ] E) :
    numericalRadius (c • A) ≤ ‖c‖ * numericalRadius A := by
  unfold numericalRadius
  refine Real.iSup_le (fun z => ?_)
    (mul_nonneg (norm_nonneg c) (numericalRadius_nonneg A))
  refine Real.iSup_le (fun hz => ?_)
    (mul_nonneg (norm_nonneg c) (numericalRadius_nonneg A))
  obtain ⟨x, hx, rfl⟩ := (mem_numericalRange (c • A) z).mp hz
  simp only [smul_apply, inner_smul_right, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_le_numericalRadius A
      ((mem_numericalRange A _).2 ⟨x, hx, rfl⟩)) (norm_nonneg c)

/-- Numerical radius is absolutely homogeneous. -/
theorem numericalRadius_smul (c : ℂ) (A : E →L[ℂ] E) :
    numericalRadius (c • A) = ‖c‖ * numericalRadius A := by
  apply le_antisymm (numericalRadius_smul_le c A)
  by_cases hc : c = 0
  · subst c
    simp only [zero_smul, numericalRadius_zero, norm_zero, zero_mul]
    exact le_rfl
  · have hback := numericalRadius_smul_le c⁻¹ (c • A)
    have hcancel : c⁻¹ • (c • A) = A := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hcancel, norm_inv] at hback
    calc
      ‖c‖ * numericalRadius A ≤
          ‖c‖ * (‖c‖⁻¹ * numericalRadius (c • A)) :=
        mul_le_mul_of_nonneg_left hback (norm_nonneg c)
      _ = numericalRadius (c • A) := by
        rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul]

@[simp] theorem numericalRadius_neg (A : E →L[ℂ] E) :
    numericalRadius (-A) = numericalRadius A := by
  rw [← neg_one_smul ℂ A, numericalRadius_smul, norm_neg, norm_one, one_mul]

/-- Numerical radius satisfies the triangle inequality for subtraction. -/
theorem numericalRadius_sub_le (A B : E →L[ℂ] E) :
    numericalRadius (A - B) ≤ numericalRadius A + numericalRadius B := by
  rw [sub_eq_add_neg]
  exact (numericalRadius_add_le A (-B)).trans_eq
    (congrArg (numericalRadius A + ·) (numericalRadius_neg B))

/-- The numerical radius bundled as a complex seminorm on bounded operators.
Definiteness is supplied separately by `numericalRadius_eq_zero_iff`. -/
noncomputable def numericalRadiusSeminorm :
    Seminorm ℂ (E →L[ℂ] E) :=
  Seminorm.of numericalRadius numericalRadius_add_le numericalRadius_smul

@[simp] theorem numericalRadiusSeminorm_apply (A : E →L[ℂ] E) :
    numericalRadiusSeminorm A = numericalRadius A := rfl

/-- Numerical radius changes by at most the operator-norm distance. -/
theorem abs_numericalRadius_sub_le_norm (A B : E →L[ℂ] E) :
    |numericalRadius A - numericalRadius B| ≤ ‖A - B‖ := by
  have hAB := numericalRadius_add_le (A - B) B
  rw [sub_add_cancel] at hAB
  have hBA := numericalRadius_add_le (B - A) A
  rw [sub_add_cancel] at hBA
  have hreverse : numericalRadius (B - A) = numericalRadius (A - B) := by
    rw [show B - A = -(A - B) by abel, numericalRadius_neg]
  have hdiff := numericalRadius_le_norm (A - B)
  rw [abs_sub_le_iff]
  constructor
  · linarith
  · rw [hreverse] at hBA
    linarith

/-- Numerical radius is `1`-Lipschitz with respect to the operator norm. -/
theorem lipschitzWith_numericalRadius :
    LipschitzWith 1 (numericalRadius : (E →L[ℂ] E) → ℝ) := by
  apply LipschitzWith.mk_one
  intro A B
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
    abs_numericalRadius_sub_le_norm A B

/-- Numerical radius is continuous in the operator norm. -/
theorem continuous_numericalRadius :
    Continuous (numericalRadius : (E →L[ℂ] E) → ℝ) :=
  lipschitzWith_numericalRadius.continuous

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
