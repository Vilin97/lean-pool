/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

/-!
# Homogeneous Sobolev bounds for smooth square-integrable functions

Spatial cutoffs extend the compactly supported Sobolev inequality to a smooth
function whose value and derivative belong to `L²`. The derivative of the
cutoff contributes an error tending to zero; Fatou's lemma passes to the limit.
-/


noncomputable section

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace NavierStokesR3.RieszTestOperators

open ProblemStatement ComparisonCutoffs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The product rule with a uniformly bounded spatial cutoff. -/
theorem norm_fderiv_cutoff_smul_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (fun y => cutoff R y • f y) x‖ ≤
      ‖fderiv ℝ f x‖ + (derivativeConstant 1 / R) * ‖f x‖ := by
  change ‖fderiv ℝ (cutoff R • f) x‖ ≤ _
  rw [fderiv_smul ((cutoff_smooth R).differentiable (by simp) x)
    (hf.differentiable (by simp) x)]
  calc
    ‖cutoff R x • fderiv ℝ f x + (fderiv ℝ (cutoff R) x).smulRight (f x)‖
        ≤ ‖cutoff R x • fderiv ℝ f x‖ +
          ‖(fderiv ℝ (cutoff R) x).smulRight (f x)‖ := norm_add_le _ _
    _ = cutoff R x * ‖fderiv ℝ f x‖ + ‖fderiv ℝ (cutoff R) x‖ * ‖f x‖ := by
      rw [_root_.norm_smul (cutoff R x) (fderiv ℝ f x), Real.norm_eq_abs,
        abs_of_nonneg (cutoff_nonneg R x),
        ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ 1 * ‖fderiv ℝ f x‖ + (derivativeConstant 1 / R) * ‖f x‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (cutoff_le_one R x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (cutoff_fderiv_le hR x) (norm_nonneg _))
    _ = ‖fderiv ℝ f x‖ + (derivativeConstant 1 / R) * ‖f x‖ := by rw [one_mul]

/-- The cutoff derivative has a vanishing `L²` error. -/
theorem eLpNorm_fderiv_cutoff_smul_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    {R : ℝ} (hR : 0 < R) :
    eLpNorm (fderiv ℝ (fun y => cutoff R y • f y)) 2 volume ≤
      eLpNorm (fderiv ℝ f) 2 volume +
        ENNReal.ofReal (derivativeConstant 1 / R) * eLpNorm f 2 volume := by
  calc
    eLpNorm (fderiv ℝ (fun y => cutoff R y • f y)) 2 volume
        ≤ eLpNorm (fun x => ‖fderiv ℝ f x‖ +
          (derivativeConstant 1 / R) * ‖f x‖) 2 volume :=
      eLpNorm_mono_real (norm_fderiv_cutoff_smul_le hf hR)
    _ ≤ eLpNorm (fun x => ‖fderiv ℝ f x‖) 2 volume +
        eLpNorm (fun x => (derivativeConstant 1 / R) * ‖f x‖) 2 volume :=
      eLpNorm_add_le (hf.continuous_fderiv (by simp)).norm.aestronglyMeasurable
        (continuous_const.mul hf.continuous.norm).aestronglyMeasurable (by norm_num)
    _ = eLpNorm (fderiv ℝ f) 2 volume +
        ENNReal.ofReal (derivativeConstant 1 / R) * eLpNorm f 2 volume := by
      rw [eLpNorm_norm]
      change _ + eLpNorm ((derivativeConstant 1 / R) • (fun x => ‖f x‖)) 2 volume = _
      rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal
        (div_nonneg (derivativeConstant_pos 1).le hR.le)]

/-- The homogeneous `H¹ → L⁶` inequality without a support assumption.
Only the function itself must have finite `L²` norm for this extended-norm
inequality; the right side may be infinite. -/
theorem smooth_eLpNorm_six_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) :
    eLpNorm f 6 volume ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume := by
  let C : ℝ≥0∞ := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2
  let D : ℝ≥0∞ := eLpNorm (fderiv ℝ f) 2 volume
  let M : ℝ≥0∞ := eLpNorm f 2 volume
  let u : ℕ → Space → E := fun n x => cutoff (n : ℝ) x • f x
  have hu (n : ℕ) : ContDiff ℝ 1 (u n) :=
    ((cutoff_smooth (n : ℝ)).of_le (by simp)).smul hf
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpointwise (x : Space) :
      Tendsto (fun n => u n x) atTop (𝓝 (f x)) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hnat.eventually (eventually_cutoff_eq_one x)] with n hn
    simp only [u, hn, one_smul]
  have hfatou : eLpNorm f 6 volume ≤
      atTop.liminf (fun n => eLpNorm (u n) 6 volume) :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (hu n).continuous.aestronglyMeasurable) f
      (Filter.Eventually.of_forall hpointwise)
  have hn_dim : Module.finrank ℝ Space = 3 := by
    simp [Space, NavierStokes.ProblemStatement.Space]
  have hbound : ∀ᶠ n : ℕ in atTop,
      eLpNorm (u n) 6 volume ≤
        C * (D + ENNReal.ofReal (derivativeConstant 1 / (n : ℝ)) * M) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hcompact : HasCompactSupport (u n) :=
      (cutoff_hasCompactSupport hnR).smul_right
    have hSob := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure Space)
      (hu n) hcompact (p := 2) (p' := 6) (by norm_num) (by omega)
      (by rw [hn_dim]; norm_num)
    have hSob' : eLpNorm (u n) 6 volume ≤
        C * eLpNorm (fderiv ℝ (u n)) 2 volume := by
      simpa [C] using hSob
    exact hSob'.trans
      (mul_le_mul_right (eLpNorm_fderiv_cutoff_smul_le hf hnR) C)
  have herr : Tendsto
      (fun n : ℕ => ENNReal.ofReal (derivativeConstant 1 / (n : ℝ)) * M)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_ofReal
        (tendsto_const_div_atTop_nhds_zero_nat (derivativeConstant 1)))
      (Or.inr h2.eLpNorm_ne_top)
  have hsum : Tendsto
      (fun n : ℕ => D + ENNReal.ofReal (derivativeConstant 1 / (n : ℝ)) * M)
      atTop (𝓝 (D + 0)) :=
    tendsto_const_nhds.add herr
  have hlimit : Tendsto
      (fun n : ℕ => C * (D + ENNReal.ofReal (derivativeConstant 1 / (n : ℝ)) * M))
      atTop (𝓝 (C * D)) := by
    simpa only [add_zero] using ENNReal.Tendsto.const_mul hsum
      (Or.inr (show C ≠ (⊤ : ℝ≥0∞) from ENNReal.coe_ne_top))
  exact hfatou.trans ((Filter.liminf_le_liminf hbound).trans_eq hlimit.liminf_eq)

/-- A smooth function with square-integrable value and derivative belongs to
`L⁶`, with no support hypothesis. -/
theorem smooth_memLp_six {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    MemLp f 6 volume := by
  refine ⟨hf.continuous.aestronglyMeasurable, (smooth_eLpNorm_six_le hf h2).trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hD2.2

/-- The real-valued homogeneous Sobolev bound when both `L²` norms are finite. -/
theorem smooth_eLpNorm_six_toReal_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    (eLpNorm f 6 volume).toReal ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
        (eLpNorm (fderiv ℝ f) 2 volume).toReal := by
  have hfinite :
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hD2.2).ne
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using
    ENNReal.toReal_mono hfinite (smooth_eLpNorm_six_le hf h2)

end NavierStokesR3.RieszTestOperators
