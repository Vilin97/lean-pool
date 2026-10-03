/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TimeParameterizedField

/-! The actual flow solves its target-time-parameterized integral equation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- The actual joint state path on the fixed unit interval. -/
def amnrTimeParameterizedCurve {b : ℝ → Vec 2 → Vec 2}
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s d α : ℝ) (z : ℝ × Vec 2) : C(Icc (0 : ℝ) 1, ℝ × Vec 2) :=
  ⟨fun τ => (z.1, X (s + (τ : ℝ) * (d + α * z.1)) z.2 s),
    continuous_const.prodMk
      (((continuous_iff_continuousAt.mpr (fun r => (hX.2 z.2 s r).continuousAt)).comp
        (show Continuous (fun τ : Icc (0 : ℝ) 1 => s + (τ : ℝ) * (d + α * z.1)) by fun_prop)))⟩

/-- Joint continuity of the actual flow yields continuity into the uniform
trajectory space before any parameter derivative is asserted. -/
theorem amnrTimeParameterizedCurve_continuous {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s d α : ℝ) : Continuous (amnrTimeParameterizedCurve hX s d α) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.fst).prodMk ((flow_continuous_joint_of_smoothPeriodic hb hX).comp
    (show Continuous (fun z : (ℝ × Vec 2) × Icc (0 : ℝ) 1 =>
      (s + (z.2 : ℝ) * (d + α * z.1.1), z.1.2, s)) by fun_prop))

/-- The actual parameterized path satisfies its actual augmented ODE. -/
theorem amnrTimeParameterizedCurve_hasDerivAt {b : ℝ → Vec 2 → Vec 2}
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s d α : ℝ) (z : ℝ × Vec 2) (τ : ℝ) :
    HasDerivAt (fun r : ℝ => (z.1, X (s + r * (d + α * z.1)) z.2 s))
      (amnrTimeParameterizedField b s d α
        (τ, (z.1, X (s + τ * (d + α * z.1)) z.2 s))) τ := by
  have ht : HasDerivAt (fun r : ℝ => s + r * (d + α * z.1)) (d + α * z.1) τ :=
    by simpa using ((hasDerivAt_id τ).mul_const (d + α * z.1)).const_add s
  have hx := (hX.2 z.2 s (s + τ * (d + α * z.1))).scomp τ ht
  exact (hasDerivAt_const τ z.1).prodMk hx

/-- The actual parameterized curve obeys the actual Volterra equation. -/
theorem amnrTimeParameterizedCurve_residual_eq_const {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s d α : ℝ) (z : ℝ × Vec 2) :
    amnrCurveResidual (amnrTimeParameterizedField b s d α)
      (amnrTimeParameterizedField_contDiff hb s d α).continuous (amnrTimeCurve 0 1)
      (amnrCurveIntegral (E := ℝ × Vec 2) (by norm_num) 0 ⟨le_rfl, by norm_num⟩)
      (amnrTimeParameterizedCurve hX s d α z) = ContinuousMap.const (Icc (0 : ℝ) 1) z := by
  apply ContinuousMap.ext
  intro τ
  let q := fun r : ℝ => (z.1, X (s + r * (d + α * z.1)) z.2 s)
  let F := fun r : ℝ => amnrTimeParameterizedField b s d α (r, q r)
  have hq : Continuous q := continuous_const.prodMk
    ((continuous_iff_continuousAt.mpr (fun r => (hX.2 z.2 s r).continuousAt)).comp
      (show Continuous (fun r : ℝ => s + r * (d + α * z.1)) by fun_prop))
  have hF : Continuous F := (amnrTimeParameterizedField_contDiff hb s d α).continuous.comp
    (continuous_id.prodMk hq)
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (τ : ℝ))
    (fun r _ => amnrTimeParameterizedCurve_hasDerivAt hX s d α z r) (hF.intervalIntegrable 0 τ)
  change q τ - ∫ r in (0 : ℝ)..(τ : ℝ), amnrExtendCurve (by norm_num)
    (amnrCurveJointCompose (amnrTimeParameterizedField b s d α)
      (amnrTimeParameterizedField_contDiff hb s d α).continuous (amnrTimeCurve 0 1)
      (amnrTimeParameterizedCurve hX s d α z)) r = z
  have heq : (∫ r in (0 : ℝ)..(τ : ℝ), amnrExtendCurve (by norm_num)
      (amnrCurveJointCompose (amnrTimeParameterizedField b s d α)
        (amnrTimeParameterizedField_contDiff hb s d α).continuous (amnrTimeCurve 0 1)
        (amnrTimeParameterizedCurve hX s d α z)) r) = ∫ r in (0 : ℝ)..(τ : ℝ), F r := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hmem : r ∈ Icc (0 : ℝ) 1 := by
      have ht := τ.property
      rw [mem_uIcc] at hr
      rcases hr with hr | hr
      · exact ⟨hr.1, hr.2.trans ht.2⟩
      · exact ⟨ht.1.trans hr.1, hr.2.trans (by norm_num)⟩
    rw [amnrExtendCurve_eq_of_mem (by norm_num) _ hmem]
    rfl
  rw [heq, hI, sub_sub_cancel]
  rw [zero_mul, add_zero, hX.1]

end AVenhance.Infra.Section4
