/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CurveImplicit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FlowIntegral

/-! The characterized flow as an actual compact-time solution curve. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
open scoped NNReal
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- The actual time coordinate on a compact interval. -/
def amnrTimeCurve (a b : ℝ) : C(Icc a b, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The actual characterized flow trajectory, retaining its initial point. -/
def amnrFlowCurve {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X) (s a c : ℝ) (x : Vec 2) : C(Icc a c, Vec 2) :=
  ⟨fun t => X t x s,
    (continuous_iff_continuousAt.mpr (fun t => (hX.2 x s t).continuousAt)).comp
        continuous_subtype_val⟩

/-- Grönwall gives actual uniform continuity of the solution-curve family
with respect to its initial point, before proving any flow derivatives. -/
theorem amnrFlowCurve_lipschitz {b : ℝ → Vec 2 → Vec 2}
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {L : ℝ} (hL₀ : 0 ≤ L) (hL : ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {s a c : ℝ} (hs : s ∈ Icc a c) :
    LipschitzWith (Real.exp (L * (c - a))).toNNReal (amnrFlowCurve hX s a c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le]
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro t
  change ‖X t x s - X t y s‖ ≤ _
  have ht : |(t : ℝ) - s| ≤ c - a :=
    abs_le.mpr ⟨by linarith [hs.2, t.property.1], by linarith [hs.1, t.property.2]⟩
  exact (flow_spatial_gronwall b hL hX x y s t).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hL₀))
        (norm_nonneg _))

/-- The actual flow curves solve the actual compact-time integral equation.
The clamped extension is used only outside the integration interval. -/
theorem amnrFlowCurve_residual_eq_const {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {s a c : ℝ} (hac : a ≤ c) (hs : s ∈ Icc a c) (x : Vec 2) :
    amnrCurveResidual (Function.uncurry b) hb.smooth.continuous (amnrTimeCurve a c)
      (amnrCurveIntegral hac s hs) (amnrFlowCurve hX s a c x) = ContinuousMap.const (Icc a c) x :=
          by
  apply ContinuousMap.ext
  intro t
  change X t x s - ∫ r in s..(t : ℝ),
    amnrExtendCurve hac (amnrCurveJointCompose (Function.uncurry b) hb.smooth.continuous
      (amnrTimeCurve a c) (amnrFlowCurve hX s a c x)) r = x
  have heq : (∫ r in s..(t : ℝ),
      amnrExtendCurve hac (amnrCurveJointCompose (Function.uncurry b) hb.smooth.continuous
        (amnrTimeCurve a c) (amnrFlowCurve hX s a c x)) r) =
      ∫ r in s..(t : ℝ), b r (X r x s) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hrc : r ∈ Icc a c := by
      rw [mem_uIcc] at hr
      rcases hr with hr | hr
      · exact ⟨hs.1.trans hr.1, hr.2.trans t.property.2⟩
      · exact ⟨t.property.1.trans hr.1, hr.2.trans hs.2⟩
    rw [amnrExtendCurve_eq_of_mem hac _ hrc]
    rfl
  rw [heq, flow_eq_initial_add_intervalIntegral hb hX x s t]
  exact add_sub_cancel_right _ _

/-- On a short interval, the actual solution-curve family is smooth in its
initial point. The flow equation and Grönwall, rather than a flow regularity
premise, discharge the two solution-family inputs. -/
theorem amnrFlowCurve_contDiff_infty_of_short {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M : ℝ} (hM : 0 ≤ M) (hstate : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    {s a c : ℝ} (hac : a ≤ c) (hs : s ∈ Icc a c) (hshort : (c - a) * M < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrFlowCurve hX s a c) := by
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  have hQ := (amnrFlowCurve_lipschitz hX hL₀ hL hs).continuous
  apply contDiff_iff_contDiffAt.mpr
  intro x
  apply amnrCurveResidual_solution_contDiffAt hb.smooth (exists_global_iteratedFDeriv_bound hb)
    (amnrTimeCurve a c) (amnrCurveIntegral hac s hs) hM
  · intro z
    exact hstate z.1 z.2
  · exact (mul_le_mul_of_nonneg_right (amnrCurveIntegral_norm_le hac s hs) hM).trans_lt hshort
  · exact hQ.continuousAt
  · exact amnrFlowCurve_residual_eq_const hb hX hac hs

/-- Evaluation of the smooth actual solution curve gives every spatial
order of the actual fixed-time flow map on the same short interval. -/
theorem amnr_flow_spatial_contDiff_infty_of_short {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M : ℝ} (hM : 0 ≤ M) (hstate : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    {s a c t : ℝ} (hac : a ≤ c) (hs : s ∈ Icc a c) (ht : t ∈ Icc a c)
    (hshort : (c - a) * M < 1) : ContDiff ℝ (⊤ : ℕ∞) (fun x => X t x s) := by
  have hh := (ContinuousMap.evalCLM ℝ (⟨t, ht⟩ : Icc a c)).contDiff.comp
    (amnrFlowCurve_contDiff_infty_of_short hb hX hM hstate hac hs hshort)
  exact hh

end AVenhance.Infra.Section4
