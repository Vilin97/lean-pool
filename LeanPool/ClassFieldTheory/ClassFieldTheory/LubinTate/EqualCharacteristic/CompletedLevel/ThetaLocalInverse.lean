/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaAtCompletedLevel
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
/-!
# The completed theta-intertwining theorem: local injectivity of theta

The theta series has a unit linear coefficient and integral higher
coefficients.  This file records the resulting nonarchimedean local
isometry on the maximal ideal.
-/

@[expose] public section

noncomputable
section

open Filter
open scoped LaurentSeries NNReal NormedField PowerSeries
  PowerSeries.WithPiTopology Topology Valued WithZero


universe u v w

namespace LubinTate
namespace EqualCharacteristic

variable {ι E : Type*}

private theorem norm_finset_sum_le_of_norm_le
    [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {f : ι → E} (t : Finset ι) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ i ∈ t, ‖f i‖ ≤ C) :
    ‖∑ i ∈ t, f i‖ ≤ C := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hC
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact (IsUltrametricDist.norm_add_le_max (f a) (∑ i ∈ t, f i)).trans
        (max_le (hf a (Finset.mem_insert_self a t))
          (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

/-- A convergent series in an ultrametric group has norm bounded by any
common bound for all its terms. -/
theorem norm_le_of_hasSum_of_norm_le
    [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {f : ι → E} {s : E} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) (hs : HasSum f s) :
    ‖s‖ ≤ C := by
  classical
  have hpartial : ∀ t : Finset ι, ‖∑ i ∈ t, f i‖ ≤ C := by
    intro t
    exact norm_finset_sum_le_of_norm_le t hC (fun i _ ↦ hf i)
  have hsClosed : s ∈ Metric.closedBall (0 : E) C :=
    Metric.isClosed_closedBall.mem_of_tendsto hs
      (Filter.Eventually.of_forall fun t ↦ by
        simpa [Metric.mem_closedBall] using hpartial t)
  simpa [Metric.mem_closedBall] using hsClosed

/-- The two-variable geometric factor in `x^n-y^n` is bounded by the
larger of `‖x‖` and `‖y‖` on the open unit ball, once `n ≥ 2`. -/
private theorem norm_geomSum₂_le_max
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
    (x y : Valued.integer L) (n : ℕ) (hn : 2 ≤ n)
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖ ≤
      max ‖x‖ ‖y‖ := by
  let r : ℝ := max ‖x‖ ‖y‖
  have hr0 : 0 ≤ r := le_trans (norm_nonneg x) (le_max_left _ _)
  have hr1 : r < 1 := max_lt hx hy
  apply norm_finset_sum_le_of_norm_le (Finset.range n) hr0
  intro i hiMem
  have hi : i < n := Finset.mem_range.mp hiMem
  have hxi : ‖x‖ ^ i ≤ r ^ i :=
      pow_le_pow_left₀ (norm_nonneg x) (le_max_left _ _) _
  have hyi : ‖y‖ ^ (n - 1 - i) ≤ r ^ (n - 1 - i) :=
      pow_le_pow_left₀ (norm_nonneg y) (le_max_right _ _) _
  rw [norm_mul, norm_pow, norm_pow]
  calc
    ‖x‖ ^ i * ‖y‖ ^ (n - 1 - i) ≤ r ^ i * r ^ (n - 1 - i) :=
      mul_le_mul hxi hyi (pow_nonneg (norm_nonneg y) _) (pow_nonneg hr0 _)
    _ = r ^ (n - 1) := by
      rw [← pow_add]
      congr 1
      omega
    _ = r ^ (n - 2) * r := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    _ ≤ 1 * r :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1.le) hr0
    _ = r := one_mul r

/-- Higher power differences contract strictly relative to `x-y` on the
open unit ball. -/
private theorem norm_pow_sub_pow_le_max_mul_norm_sub
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
    (x y : Valued.integer L) (n : ℕ) (hn : 2 ≤ n)
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    ‖x ^ n - y ^ n‖ ≤ max ‖x‖ ‖y‖ * ‖x - y‖ := by
  rw [← (Commute.all x y).mul_geom_sum₂ n, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (norm_geomSum₂_le_max x y n hn hx hy) (norm_nonneg (x - y))

/-- Nonarchimedean inverse-function estimate for an integral power series.

The coefficient sequence is valued in the valuation ring.  A unit linear
coefficient makes any two convergent evaluations on the open unit ball an
isometry.  No characteristic assumption is needed. -/
theorem integralPowerSeriesEvaluation_norm_sub
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
    (c : ℕ → Valued.integer L) (hc₁ : IsUnit (c 1))
    (x y fx fy : Valued.integer L)
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hfx : HasSum (fun m : ℕ ↦ c m * x ^ m) fx)
    (hfy : HasSum (fun m : ℕ ↦ c m * y ^ m) fy) :
    ‖fx - fy‖ = ‖x - y‖ := by
  by_cases hxy : x = y
  · subst y
    have hvalue : fx = fy := hfx.unique hfy
    subst fy
    simp
  let term : ℕ → Valued.integer L :=
    fun m ↦ c m * x ^ m - c m * y ^ m
  let linear : Valued.integer L := c 1 * (x - y)
  let remainder : Valued.integer L := (fx - fy) - linear
  let r : ℝ := max ‖x‖ ‖y‖
  have hr0 : 0 ≤ r := le_trans (norm_nonneg x) (le_max_left _ _)
  have hr1 : r < 1 := max_lt hx hy
  have hdiff : HasSum term (fx - fy) := by
    simpa only [term] using hfx.sub hfy
  have hprefix : ∑ i ∈ Finset.range 2, term i = linear := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    dsimp only [term, linear]
    ring
  have htail : HasSum (fun m : ℕ ↦ term (m + 2)) remainder := by
    have h := (hasSum_nat_add_iff' (f := term) 2).2 hdiff
    rwa [hprefix] at h
  have htermBound : ∀ m : ℕ,
      ‖term (m + 2)‖ ≤ r * ‖x - y‖ := by
    intro m
    change ‖c (m + 2) * x ^ (m + 2) -
      c (m + 2) * y ^ (m + 2)‖ ≤ r * ‖x - y‖
    rw [← mul_sub, norm_mul]
    calc
      ‖c (m + 2)‖ * ‖x ^ (m + 2) - y ^ (m + 2)‖ ≤
          1 * (r * ‖x - y‖) :=
        mul_le_mul (Valued.integer.norm_le_one _) (by
          simpa only [r] using
            norm_pow_sub_pow_le_max_mul_norm_sub x y (m + 2) (by omega) hx hy)
          (norm_nonneg _) zero_le_one
      _ = r * ‖x - y‖ := one_mul _
  have hremainder_le : ‖remainder‖ ≤ r * ‖x - y‖ :=
    norm_le_of_hasSum_of_norm_le
      (mul_nonneg hr0 (norm_nonneg (x - y))) htermBound htail
  have hsubpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hremainder_lt : ‖remainder‖ < ‖x - y‖ :=
    hremainder_le.trans_lt (by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hr1 hsubpos)
  have hlinear : ‖linear‖ = ‖x - y‖ := by
    change ‖c 1 * (x - y)‖ = ‖x - y‖
    rw [norm_mul,
      (Valued.integer.isUnit_iff_norm_eq_one.mp hc₁), one_mul]
  have hdecomp : fx - fy = linear + remainder := by
    simp [remainder]
  rw [hdecomp]
  calc
    ‖linear + remainder‖ = max ‖linear‖ ‖remainder‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (hlinear.trans_ne hremainder_lt.ne')
    _ = ‖x - y‖ := by
      rw [hlinear, max_eq_left hremainder_lt.le]

/-- Consequently, any analytic evaluation with integral coefficients and
unit linear coefficient is injective on the open unit ball. -/
theorem integralPowerSeriesEvaluation_injectiveOn
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
    (c : ℕ → Valued.integer L) (hc₁ : IsUnit (c 1))
    (eval : Valued.integer L → Valued.integer L)
    (hsum : ∀ x : Valued.integer L, ‖x‖ < 1 →
      HasSum (fun m : ℕ ↦ c m * x ^ m) (eval x)) :
    Set.InjOn eval {x | ‖x‖ < 1} := by
  intro x hx y hy hxy
  have hnorm := integralPowerSeriesEvaluation_norm_sub c hc₁ x y
    (eval x) (eval y) hx hy (hsum x hx) (hsum y hy)
  rw [hxy, sub_self, norm_zero] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm.symm)

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The canonical nontrivial norm on the completed Lubin–Tate field at level `n`. -/
noncomputable local instance equalCharacteristicThetaInverseLevelNormedField
    (F : LocalField.{u, v} K) (n : ℕ) :
    NontriviallyNormedField (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelNormedField F n

noncomputable local instance equalCharacteristicThetaInverseLevelIsUltrametric
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUltrametricDist (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelIsUltrametric F n

noncomputable local instance equalCharacteristicThetaInverseLevelCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelCompleteSpace F n

/-- The nonnegative-real-valued valuation on the completed Lubin–Tate field at level `n`. -/
noncomputable local instance equalCharacteristicThetaInverseLevelValued
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued (equalCharacteristicCompletedLevelField F n) ℝ≥0 :=
  equalCharacteristicCompletedLevelValued F n

noncomputable local instance equalCharacteristicThetaInverseIntegerLinearTopology
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsLinearTopology
      (Valued.integer (equalCharacteristicCompletedLevelField F n))
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerLinearTopology

noncomputable local instance equalCharacteristicThetaInverseIntegerCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerCompleteSpace

noncomputable local instance equalCharacteristicThetaInverseIntegerUniformAddGroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUniformAddGroup
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerIsUniformAddGroup

private noncomputable local instance equalCharacteristicThetaInverseCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace ((AlgebraicClosure F.residueField)⟦X⟧) := ⊥

private theorem equalCharacteristicThetaInverseCoefficientHom_continuous
    (F : LocalField.{u, v} K) (n : ℕ) :
    Continuous (equalCharacteristicCompletedLevelCoefficientHom F n) :=
  continuous_of_discreteTopology

/-- Norm `< 1` supplies the analytic evaluation hypothesis for a point in
the completed-level valuation ring. -/
theorem equalCharacteristicCompletedLevel_hasEval_of_norm_lt_one
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (hx : ‖x‖ < 1) :
    PowerSeries.HasEval x := by
  change Tendsto (fun m : ℕ ↦ x ^ m) atTop (nhds 0)
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx

/-- The linear coefficient of theta stays a unit after inclusion into any
completed level valuation ring. -/
theorem equalCharacteristicThetaCompletedCoefficientOne_isUnit
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsUnit
      (equalCharacteristicCompletedLevelCoefficientHom F n
        (PowerSeries.coeff 1 (equalCharacteristicThetaSeries u))) := by
  apply IsUnit.map (equalCharacteristicCompletedLevelCoefficientHom F n)
  rw [equalCharacteristicThetaSeries_coeff_one,
    PowerSeries.isUnit_iff_constantCoeff]
  apply isUnit_iff_ne_zero.mpr
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
    (equalCharacteristicSemilinearUnit_constantCoeff_ne_zero
      (u : F.residueField⟦X⟧)
      (by
        intro hzero
        have hunit := PowerSeries.isUnit_constantCoeff
          (u : F.residueField⟦X⟧) u.isUnit
        apply hunit.ne_zero
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero))

/-- Theta evaluated at an arbitrary point of the completed-level maximal
ideal. -/
noncomputable def equalCharacteristicThetaOnCompletedLevelMaximalIdeal
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : {x : Valued.integer (equalCharacteristicCompletedLevelField F n) //
      ‖x‖ < 1}) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelEvaluation F n x
    (equalCharacteristicCompletedLevel_hasEval_of_norm_lt_one F n x x.property)
    (equalCharacteristicThetaSeries u)

/-- States the theorem `equalCharacteristicThetaOnCompletedLevelMaximalIdeal_hasSum`. -/
theorem equalCharacteristicThetaOnCompletedLevelMaximalIdeal_hasSum
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : {x : Valued.integer (equalCharacteristicCompletedLevelField F n) //
      ‖x‖ < 1}) :
    HasSum
      (fun m : ℕ ↦
        equalCharacteristicCompletedLevelCoefficientHom F n
            (PowerSeries.coeff m (equalCharacteristicThetaSeries u)) *
          (x : Valued.integer
            (equalCharacteristicCompletedLevelField F n)) ^ m)
      (equalCharacteristicThetaOnCompletedLevelMaximalIdeal F u n x) := by
  rw [equalCharacteristicThetaOnCompletedLevelMaximalIdeal,
    equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom]
  exact PowerSeries.hasSum_eval₂
    (equalCharacteristicThetaInverseCoefficientHom_continuous F n)
    (equalCharacteristicCompletedLevel_hasEval_of_norm_lt_one F n x x.property)
    (equalCharacteristicThetaSeries u)

/-- The faithful analytic conclusion used in the completed theta-intertwining theorem: theta is a
local isometry, hence injective, on the completed-level maximal ideal. -/
theorem equalCharacteristicThetaOnCompletedLevelMaximalIdeal_norm_sub
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x y : {x : Valued.integer (equalCharacteristicCompletedLevelField F n) //
      ‖x‖ < 1}) :
    ‖equalCharacteristicThetaOnCompletedLevelMaximalIdeal F u n x -
        equalCharacteristicThetaOnCompletedLevelMaximalIdeal F u n y‖ =
      ‖(x : Valued.integer (equalCharacteristicCompletedLevelField F n)) - y‖ := by
  exact integralPowerSeriesEvaluation_norm_sub
    (fun m : ℕ ↦
      equalCharacteristicCompletedLevelCoefficientHom F n
        (PowerSeries.coeff m (equalCharacteristicThetaSeries u)))
    (equalCharacteristicThetaCompletedCoefficientOne_isUnit F u n)
    x y
    (equalCharacteristicThetaOnCompletedLevelMaximalIdeal F u n x)
    (equalCharacteristicThetaOnCompletedLevelMaximalIdeal F u n y)
    x.property y.property
    (equalCharacteristicThetaOnCompletedLevelMaximalIdeal_hasSum F u n x)
    (equalCharacteristicThetaOnCompletedLevelMaximalIdeal_hasSum F u n y)

/-- States the theorem `equalCharacteristicThetaOnCompletedLevelMaximalIdeal_injective`. -/
theorem equalCharacteristicThetaOnCompletedLevelMaximalIdeal_injective
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Function.Injective
      (equalCharacteristicThetaOnCompletedLevelMaximalIdeal F u n) := by
  intro x y hxy
  apply Subtype.ext
  have hnorm :=
    equalCharacteristicThetaOnCompletedLevelMaximalIdeal_norm_sub F u n x y
  rw [hxy, sub_self, norm_zero] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm.symm)

end EqualCharacteristic
end LubinTate
