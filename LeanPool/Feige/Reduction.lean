/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Calibration
import LeanPool.Feige.Constants
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic

/-!
# Reduction from exact calibration to Feige's inequality

This file formalizes the reduction in §2.2 at `δ = 1`.  The calibration
theorem and the deterministic simplex bridge are exposed as separate
hypotheses.  The result here is the shift, bad-event inclusion, and
complement argument in the proof of Theorem 1.1.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace Feige

/-- Abstract form of the `δ = 1` geometric estimate in §2.2: a nonnegative
vector with ordinary sum at least `n + 1` has Dirichlet statistic at most
`1 - bₙ,₁`. -/
def LargeSumBridge {n : ℕ} (K : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ y : Fin n → ℝ,
    (∀ i, 0 ≤ y i) →
    (n : ℝ) + 1 ≤ ∑ i, y i →
    K y ≤ 1 - sharpConstant n

/-- A candidate lower bound for the fixed-dimensional unit-slack Feige
inequality, quantified over all admissible probability spaces and random
variables. -/
def FixedDimensionalFeigeLowerBound (n : ℕ) (c : ℝ) : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ) (X : Fin n → Ω → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, Integrable (X i) μ) →
    iIndepFun X μ →
    (∀ i ω, 0 ≤ X i ω) →
    (∀ i, (∫ ω, X i ω ∂μ) ≤ 1) →
    c ≤ μ.real
      {ω | (∑ i, X i ω) < (∫ ω', ∑ i, X i ω' ∂μ) + 1}

/-- The shifted variables `Yᵢ = Xᵢ + 1 - E Xᵢ` used in the proof of
Theorem 1.1 in §2.2. -/
noncomputable def shifted {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (i : Fin n) (ω : Ω) : ℝ :=
  X i ω + 1 - ∫ ω', X i ω' ∂μ

/-- The `δ = 1` reduction in §2.2: exact calibration and the deterministic
bridge imply the sharp fixed-dimensional bound for the strict event
`∑ Xᵢ < E(∑ Xᵢ) + 1`. -/
theorem sharp_feige_of_calibration_and_largeSumBridge
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (K : (Fin n → ℝ) → ℝ)
    (hcal : CalibrationProperty μ K) (hbridge : LargeSumBridge K)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_int : ∀ i, Integrable (X i) μ)
    (hX_indep : iIndepFun X μ)
    (hX_nonneg : ∀ i ω, 0 ≤ X i ω)
    (hX_mean : ∀ i, (∫ ω, X i ω ∂μ) ≤ 1) :
    sharpConstant n ≤
      μ.real {ω | (∑ i, X i ω) < (∫ ω', ∑ i, X i ω' ∂μ) + 1} := by
  let Y : Fin n → Ω → ℝ := shifted μ X
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    exact ((hX_meas i).add_const 1).sub_const _
  have hY_int : ∀ i, Integrable (Y i) μ := by
    intro i
    exact ((hX_int i).add (integrable_const 1)).sub (integrable_const _)
  have hY_indep : iIndepFun Y μ := by
    have hcomp := hX_indep.comp
      (fun i x ↦ x + 1 - ∫ ω, X i ω ∂μ)
      (fun _ ↦ by fun_prop)
    change iIndepFun
      (fun i ω ↦ X i ω + 1 - ∫ ω', X i ω' ∂μ) μ
    simpa [Function.comp_def] using hcomp
  have hY_nonneg : ∀ i ω, 0 ≤ Y i ω := by
    intro i ω
    dsimp [Y, shifted]
    linarith [hX_nonneg i ω, hX_mean i]
  have hY_mean_eq_one : ∀ i, (∫ ω, Y i ω ∂μ) = 1 := by
    intro i
    change (∫ ω, (X i ω + 1) - (∫ ω', X i ω' ∂μ) ∂μ) = 1
    calc
      (∫ ω, (X i ω + 1) - (∫ ω', X i ω' ∂μ) ∂μ) =
          (∫ ω, X i ω + 1 ∂μ) -
            ∫ _ : Ω, (∫ ω', X i ω' ∂μ) ∂μ := by
              exact integral_sub ((hX_int i).add (integrable_const 1))
                (integrable_const _)
      _ = ((∫ ω, X i ω ∂μ) + ∫ _ : Ω, (1 : ℝ) ∂μ) -
            ∫ _ : Ω, (∫ ω', X i ω' ∂μ) ∂μ := by
              rw [integral_add (hX_int i) (integrable_const 1)]
      _ = 1 := by simp
  have hc_nonneg : 0 ≤ sharpConstant n := by
    unfold sharpConstant
    positivity
  have hc_le_one : sharpConstant n ≤ 1 := by
    unfold sharpConstant
    apply pow_le_one₀
    · positivity
    · apply (div_le_one (by positivity)).2
      norm_num
  have hα_nonneg : 0 ≤ 1 - sharpConstant n := by linarith
  have hα_le_one : 1 - sharpConstant n ≤ 1 := by linarith
  have hcalibrated :
      μ.real {ω | K (fun i ↦ Y i ω) ≤ 1 - sharpConstant n} ≤
        1 - sharpConstant n := by
    exact hcal Y hY_meas hY_int hY_indep hY_nonneg
      (fun i ↦ (hY_mean_eq_one i).le) (1 - sharpConstant n) hα_nonneg hα_le_one
  have hmean_sum :
      (∫ ω, ∑ i, X i ω ∂μ) = ∑ i, ∫ ω, X i ω ∂μ := by
    simpa using
      (integral_finsetSum (μ := μ) Finset.univ (fun i _ ↦ hX_int i))
  have hsum_shifted (ω : Ω) :
      (∑ i, Y i ω) =
        (∑ i, X i ω) + (n : ℝ) - ∑ i, ∫ ω', X i ω' ∂μ := by
    simp [Y, shifted, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  let bad : Set Ω := {ω | (n : ℝ) + 1 ≤ ∑ i, Y i ω}
  have hbad_meas : MeasurableSet bad := by
    exact measurableSet_le measurable_const
      (Finset.univ.measurable_sum fun i _ ↦ hY_meas i)
  have hbad_subset :
      bad ⊆ {ω | K (fun i ↦ Y i ω) ≤ 1 - sharpConstant n} := by
    intro ω hω
    exact hbridge (fun i ↦ Y i ω) (fun i ↦ hY_nonneg i ω) hω
  have hbad_bound : μ.real bad ≤ 1 - sharpConstant n :=
    (measureReal_mono hbad_subset).trans hcalibrated
  have hgood_eq :
      {ω | (∑ i, X i ω) < (∫ ω', ∑ i, X i ω' ∂μ) + 1} = badᶜ := by
    ext ω
    simp only [bad, mem_ofPred_eq, mem_compl_iff, not_le]
    rw [hsum_shifted ω, hmean_sum]
    constructor <;> intro h <;> linarith
  rw [hgood_eq, probReal_compl_eq_one_sub hbad_meas]
  linarith

/-- The two structural inputs imply that `sharpConstant n` is a valid
fixed-dimensional lower bound. -/
theorem sharpConstant_is_lowerBound_of_structural_inputs
    {n : ℕ} (K : (Fin n → ℝ) → ℝ)
    (hcal : UniversalCalibration K) (hbridge : LargeSumBridge K) :
    FixedDimensionalFeigeLowerBound n (sharpConstant n) := by
  intro Ω _ μ _ X hX_meas hX_int hX_indep hX_nonneg hX_mean
  exact sharp_feige_of_calibration_and_largeSumBridge μ K
    (hcal Ω inferInstance μ inferInstance) hbridge X hX_meas hX_int
    hX_indep hX_nonneg hX_mean

end Feige
