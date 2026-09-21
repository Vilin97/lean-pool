/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambda
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Weighted Layer Cake -/

namespace Homogenization

open scoped ENNReal NNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-- The measure `‖f‖² dμ` used to weight the layer-cake argument. -/
def sqWeightedMeasure {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : MeasureTheory.Measure α) : MeasureTheory.Measure α :=
  μ.withDensity fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))

/-- The pointwise truncation `‖f‖ ∧ m` appearing in the Caffarelli--Peral proof. -/
def truncNorm {α E : Type*} [NormedAddCommGroup E] (f : α → E) (m : ℝ) : α → ℝ :=
  fun x => min ‖f x‖ m

/-- Layer cake under the squared-density measure, with the threshold written in the source form
`a * λ`. This is an ENNReal identity and therefore needs no integrability assumption. -/
theorem lintegral_truncNorm_div_rpow_eq_weighted_layercake
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} {f : α → E} {p a m : ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f μ) (hp : 2 < p) (ha : 0 < a) (hm : 0 ≤ m) :
    ∫⁻ x, ENNReal.ofReal ((truncNorm f m x / a) ^ (p - 2)) ∂sqWeightedMeasure f μ =
      ENNReal.ofReal (p - 2) *
        ∫⁻ t in Set.Ioi (0 : ℝ),
          sqWeightedMeasure f μ {x | a * t < truncNorm f m x} *
            ENNReal.ofReal (t ^ (p - 3)) := by
  let g : α → ℝ := fun x => truncNorm f m x / a
  have hg_nonneg : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall fun x => by
    exact div_nonneg (le_min (norm_nonneg _) hm) ha.le
  have hg_meas : AEMeasurable g μ := by
    exact ((hf.norm.aemeasurable.min aemeasurable_const).div_const a)
  have hg_nonneg_weighted : 0 ≤ᵐ[sqWeightedMeasure f μ] g :=
    (MeasureTheory.withDensity_absolutelyContinuous μ _).ae_le hg_nonneg
  have h_layer := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
    (sqWeightedMeasure f μ) hg_nonneg_weighted
    (hg_meas.mono' (MeasureTheory.withDensity_absolutelyContinuous μ _))
    (p := p - 2) (by linarith)
  have hpow : p - 2 - 1 = p - 3 := by ring
  have hthreshold (t : ℝ) :
      {x | t < g x} = {x | a * t < truncNorm f m x} := by
    ext x
    simp only [Set.mem_ofPred_eq, g]
    rw [lt_div_iff₀ ha]
    ring_nf
  rw [hpow] at h_layer
  simpa only [g, hthreshold] using h_layer

/-- The algebraic normalization which turns the truncated `Lᵖ` power into the
weighted power used by layer cake. -/
lemma truncNorm_rpow_div_eq_div_rpow_mul_sq
    {α E : Type*} [NormedAddCommGroup E] (f : α → E) {p a m : ℝ}
    (hp : 2 < p) (ha : 0 < a) (hm : 0 ≤ m) (x : α) :
    (truncNorm f m x) ^ p / a ^ (p - 2) =
      (truncNorm f m x / a) ^ (p - 2) * (truncNorm f m x) ^ (2 : ℕ) := by
  have htrunc_nonneg : 0 ≤ truncNorm f m x := le_min (norm_nonneg _) hm
  have hpow : (truncNorm f m x) ^ p =
      (truncNorm f m x) ^ (p - 2) * (truncNorm f m x) ^ (2 : ℝ) := by
    calc
      (truncNorm f m x) ^ p = (truncNorm f m x) ^ (p - 2 + 2) := by ring_nf
      _ = (truncNorm f m x) ^ (p - 2) * (truncNorm f m x) ^ (2 : ℝ) :=
        Real.rpow_add_of_nonneg htrunc_nonneg (by linarith) (by norm_num)
  have hpow_nat : (truncNorm f m x) ^ p =
      (truncNorm f m x) ^ (p - 2) * (truncNorm f m x) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact hpow
  calc
    (truncNorm f m x) ^ p / a ^ (p - 2) =
        ((truncNorm f m x) ^ (p - 2) * (truncNorm f m x) ^ (2 : ℕ)) /
          a ^ (p - 2) := by
            exact congr_arg (fun z => z / a ^ (p - 2)) hpow_nat
    _ = ((truncNorm f m x) ^ (p - 2) / a ^ (p - 2)) *
          (truncNorm f m x) ^ (2 : ℕ) := by ring
    _ = (truncNorm f m x / a) ^ (p - 2) * (truncNorm f m x) ^ (2 : ℕ) := by
      rw [← Real.div_rpow htrunc_nonneg ha.le]

/-- The finite-truncation estimate used for `f_m` in the source proof.  It turns the
truncated `Lᵖ` power into the weighted layer-cake integral, retaining the exact threshold
`a * t`. -/
theorem lintegral_truncNorm_rpow_div_le_weighted_layercake
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} {f : α → E} {p a m : ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f μ) (hp : 2 < p) (ha : 0 < a) (hm : 0 ≤ m) :
    ∫⁻ x, ENNReal.ofReal ((truncNorm f m x) ^ p / a ^ (p - 2)) ∂μ ≤
      ENNReal.ofReal (p - 2) *
        ∫⁻ t in Set.Ioi (0 : ℝ),
          sqWeightedMeasure f μ {x | a * t < truncNorm f m x} *
            ENNReal.ofReal (t ^ (p - 3)) := by
  have hdensity : AEMeasurable (fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) μ := by
    exact (hf.norm.aemeasurable.pow aemeasurable_const).ennreal_ofReal
  have hpower : AEMeasurable (fun x => ENNReal.ofReal ((truncNorm f m x / a) ^ (p - 2))) μ := by
    exact (((hf.norm.aemeasurable.min aemeasurable_const).div_const a).pow
      aemeasurable_const).ennreal_ofReal
  calc
    ∫⁻ x, ENNReal.ofReal ((truncNorm f m x) ^ p / a ^ (p - 2)) ∂μ =
        ∫⁻ x, ENNReal.ofReal ((truncNorm f m x / a) ^ (p - 2)) *
          ENNReal.ofReal ((truncNorm f m x) ^ (2 : ℕ)) ∂μ := by
          apply lintegral_congr
          intro x
          rw [truncNorm_rpow_div_eq_div_rpow_mul_sq f hp ha hm]
          exact ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg
            (le_min (norm_nonneg _) hm) ha.le) _)
    _ ≤ ∫⁻ x, ENNReal.ofReal ((truncNorm f m x / a) ^ (p - 2)) ∂sqWeightedMeasure f μ := by
      rw [sqWeightedMeasure, lintegral_withDensity_eq_lintegral_mul₀ hdensity hpower]
      apply lintegral_mono
      intro x
      simp only [Pi.mul_apply]
      rw [mul_comm (ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)))]
      apply mul_le_mul_right
      apply ENNReal.ofReal_le_ofReal
      simp only [pow_two]
      exact mul_self_le_mul_self (le_min (norm_nonneg _) hm) (min_le_left _ _)
    _ = _ := lintegral_truncNorm_div_rpow_eq_weighted_layercake hf hp ha hm

end CubeCalderonZygmund

end

end Homogenization
