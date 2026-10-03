/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmDmScales

/-! Inputs of the first-summand `d_m` estimate: the stream-regularity flow-Jacobian bound
on active cutoff windows in the elementwise supremum norm, and the `L²` bound
of the terminal temperature gradient from the profile. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section4

/-- The stream-regularity estimates bound the pullback Jacobian, in the elementwise supremum norm,
    by two on
every active cutoff window. -/
theorem dm_flowGrad_norm_le_two_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m) :
    ∀ z : ℝ × Vec 2, ∀ l : ℤ, I.hatXiML m l z.1 ≠ 0 →
      ‖I.flowGrad hΦ m l z.1 z.2‖ ≤ 2 := by
  intro z l hl
  refine (Matrix.norm_le_iff (by norm_num)).2 (fun i p => ?_)
  rw [Real.norm_eq_abs]
  exact amnr_flowGrad_abs_le_two_of_A3 I hΦ hreg hm l z.1 z.2
    (amnr_hatXi_support_radius I hm l hl) i p

/-- The `L²(timeCube)` norm of the terminal temperature gradient is controlled by
the profile: `‖∇T‖_{L²} ≤ N / √κ_prev`. -/
theorem dm_Tgrad_eLpNorm_le_of_Tprofile (T : ℝ → Vec 2 → ℝ)
    (hGradCont : Continuous (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (T z.1) z.2))
    {κprev N : ℝ} (hκprev : 0 < κprev)
    (hTprofile : Real.sqrt κprev * Real.sqrt
      (AVenhance.spaceTimeGradNormSq (fun t => AVenhance.spaceGrad (T t))) ≤ N) :
    eLpNorm (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (T z.1) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal (N / Real.sqrt κprev) := by
  let μ : Measure (ℝ × Vec 2) := volume.restrict AVenhance.timeCube
  let q : ℝ × Vec 2 → ℝ := fun z =>
    Real.sqrt (Homogenization.vecNormSq (AVenhance.spaceGrad (T z.1) z.2))
  have hqcont : Continuous q := by
    refine Real.continuous_sqrt.comp ?_
    have : Continuous (fun v : Vec 2 => Homogenization.vecNormSq v) := by
      unfold Homogenization.vecNormSq Homogenization.vecDot
      fun_prop
    exact this.comp hGradCont
  have hqmem : MemLp q 2 μ := by
    dsimp [μ]
    simpa using theta_continuous_timeCube_memLp_two hqcont
  have hqint : Integrable (fun z => q z ^ 2) μ := hqmem.integrable_sq
  have hqmeas : AEStronglyMeasurable q μ :=
    hqcont.measurable.aestronglyMeasurable.restrict
  have hqenergy : (∫ z, q z ^ 2 ∂μ) =
      AVenhance.spaceTimeGradNormSq (fun t => AVenhance.spaceGrad (T t)) := by
    unfold μ AVenhance.spaceTimeGradNormSq
    apply integral_congr_ae
    filter_upwards with z
    dsimp [q]
    exact Real.sq_sqrt (Homogenization.vecNormSq_nonneg _)
  have hqLp : eLpNorm q 2 μ = ENNReal.ofReal (Real.sqrt
      (AVenhance.spaceTimeGradNormSq (fun t => AVenhance.spaceGrad (T t)))) := by
    rw [amnr_scalar_eLpNorm_two_eq_sqrt hqmeas hqint, hqenergy]
  have hpoint : ∀ z : ℝ × Vec 2,
      ‖AVenhance.spaceGrad (T z.1) z.2‖ ≤ ‖q z‖ := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro p
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    simp only [Homogenization.vecNormSq, Homogenization.vecDot, Fin.sum_univ_two]
    fin_cases p <;> simp <;>
      nlinarith [sq_nonneg (AVenhance.spaceGrad (T z.1) z.2 0),
        sq_nonneg (AVenhance.spaceGrad (T z.1) z.2 1)]
  have hgm : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (T z.1) z.2) μ :=
    hGradCont.measurable.aestronglyMeasurable.restrict
  have hmono := eLpNorm_mono_ae hgm
    (Filter.Eventually.of_forall hpoint) (p := 2)
  have hsqrt : 0 < Real.sqrt κprev := Real.sqrt_pos.2 hκprev
  have henergy : Real.sqrt (AVenhance.spaceTimeGradNormSq
      (fun t => AVenhance.spaceGrad (T t))) ≤ N / Real.sqrt κprev := by
    apply (le_div_iff₀ hsqrt).2
    simpa only [mul_comm] using hTprofile
  refine hmono.trans ?_
  rw [hqLp]
  exact ENNReal.ofReal_le_ofReal henergy

end AVenhance.Infra.Section4

end
