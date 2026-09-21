/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Submean estimates for positive powers of holomorphic norms

Jensen's formula and the tangent-line inequality for the exponential give the submean inequality
for every positive real power of a holomorphic norm. In particular, the exponent may be less
than one, as needed for the roots of Taylor coefficients in the proof of Hartogs'
separate-analyticity theorem.

Hahn–Banach transfers the scalar estimate to arbitrary complex normed targets.

## Main results

`norm_rpow_le_circleAverage` is the circle submean inequality for every positive real power of a
holomorphic norm. `log_norm_le_circleAverage` is Jensen's formula for a nonvanishing holomorphic
function.
-/

public section

open Complex Filter MeasureTheory MeromorphicOn Metric Set
open scoped Topology

namespace SeveralComplexVariables

/-- Circle averages preserve inequalities outside a discrete exceptional set. -/
theorem circleAverage_le_of_eventually_le {u v : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : R ≠ 0) (hu : CircleIntegrable u c R) (hv : CircleIntegrable v c R)
    (h : ∀ᶠ z in codiscreteWithin (sphere c |R|), u z ≤ v z) :
    Real.circleAverage u c R ≤ Real.circleAverage v c R := by
  simp only [Real.circleAverage, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_ae_restrict Real.two_pi_pos.le hu hv
  apply ae_restrict_le_codiscreteWithin measurableSet_Icc
  exact codiscreteWithin_mono (by simp) (circleMap_preimage_codiscrete hR h)

/-- For an analytic scalar function nonzero at the center, Jensen's zero terms are nonnegative, so
the mean of its logarithmic norm bounds the center value. -/
theorem log_norm_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ Real.circleAverage (fun z => Real.log ‖f z‖) c R := by
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hf
  rw [hf'.circleAverage_log_norm hR.ne' hc]
  apply le_add_of_nonneg_left
  apply finsum_nonneg
  intro z
  by_cases hz : MeromorphicOn.divisor f (closedBall c |R|) z = 0
  · simp [hz]
  have hzmem : z ∈ closedBall c |R| :=
    (MeromorphicOn.divisor f (closedBall c |R|)).supportWithinDomain hz
  have hzc : c ≠ z := by
    rintro rfl
    apply hz
    rw [hf'.divisor_apply hzmem, (hf' c hzmem).analyticOrderAt_eq_zero.mpr hc]
    simp
  apply mul_nonneg (by exact_mod_cast hf'.divisor_nonneg z)
  apply Real.log_nonneg
  rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr hzc))]
  simpa [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hR] using hzmem

/-- A positive power lies above the affine tangent expressed in logarithmic coordinates. This form
can be integrated even when the exponent is below one. -/
private theorem rpow_log_tangent_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℝ) :
    a ^ p * (1 + p * (Real.log b - Real.log a)) ≤ b ^ p := by
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb]
  calc
    Real.exp (Real.log a * p) * (1 + p * (Real.log b - Real.log a)) ≤
        Real.exp (Real.log a * p) * Real.exp (p * (Real.log b - Real.log a)) :=
      mul_le_mul_of_nonneg_left
        (by simpa [add_comm] using Real.add_one_le_exp (p * (Real.log b - Real.log a)))
        (Real.exp_pos _).le
    _ = Real.exp (Real.log b * p) := by rw [← Real.exp_add]; congr 1; ring

/-- Every positive real power of the norm of a scalar holomorphic function satisfies the circle
submean inequality, including powers less than one. -/
theorem norm_rpow_le_circleAverage_scalar {f : ℂ → ℂ} {c : ℂ} {R p : ℝ}
    (hR : 0 < R) (hp : 0 < p) (hf : AnalyticOnNhd ℂ f (closedBall c R)) :
    ‖f c‖ ^ p ≤ Real.circleAverage (fun z => ‖f z‖ ^ p) c R := by
  by_cases hc : f c = 0
  · simpa [hc, Real.zero_rpow hp.ne'] using
      Real.circleAverage_nonneg_of_nonneg (c := c) (R := R)
        (fun z _ => Real.rpow_nonneg (norm_nonneg (f z)) p)
  have hn : 0 < ‖f c‖ := norm_pos_iff.mpr hc
  have hlog : CircleIntegrable (fun z => Real.log ‖f z‖) c R := by
    apply MeromorphicOn.circleIntegrable_log_norm
    simpa [abs_of_pos hR] using (hf.mono sphere_subset_closedBall).meromorphicOn
  have hpow : CircleIntegrable (fun z => ‖f z‖ ^ p) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact (hf.continuousOn.mono sphere_subset_closedBall).norm.rpow_const
      (fun z _ => Or.inr hp.le)
  have hne : ∀ᶠ z in codiscreteWithin (sphere c |R|), f z ≠ 0 := by
    apply codiscreteWithin_mono (by simpa [abs_of_pos hR] using
      (sphere_subset_closedBall : sphere c R ⊆ closedBall c R))
    exact (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_closedBall c R).isPreconnected).resolve_left
      (fun h => hc (h (mem_closedBall_self hR.le)))
  have htan : CircleIntegrable
      (fun z => ‖f c‖ ^ p * (1 + p * (Real.log ‖f z‖ - Real.log ‖f c‖))) c R := by
    exact ((circleIntegrable_const 1 c R).add
      ((hlog.sub (circleIntegrable_const _ c R)).const_smul (a := p))).const_smul
  have hbound := circleAverage_le_of_eventually_le hR.ne' htan hpow
    (hne.mono fun z hz => rpow_log_tangent_le hn (norm_pos_iff.mpr hz) p)
  have hsub : CircleIntegrable (fun z => Real.log ‖f z‖ - Real.log ‖f c‖) c R :=
    hlog.sub (circleIntegrable_const _ c R)
  have hmul : CircleIntegrable (fun z => p • (Real.log ‖f z‖ - Real.log ‖f c‖)) c R :=
    hsub.const_smul
  have hmean : Real.circleAverage
      (fun z => ‖f c‖ ^ p * (1 + p * (Real.log ‖f z‖ - Real.log ‖f c‖))) c R =
      ‖f c‖ ^ p * (1 + p *
        (Real.circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖)) := by
    simp only [← smul_eq_mul, Real.circleAverage_fun_smul]
    rw [Real.circleAverage_fun_add (circleIntegrable_const 1 c R) hmul, Real.circleAverage_const,
      Real.circleAverage_fun_smul,
      Real.circleAverage_fun_sub hlog (circleIntegrable_const _ c R), Real.circleAverage_const]
  rw [hmean] at hbound
  have hlogbound := log_norm_le_circleAverage hR hf hc
  refine le_trans ?_ hbound
  calc
    ‖f c‖ ^ p = ‖f c‖ ^ p * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by nlinarith) (Real.rpow_nonneg (norm_nonneg _) _)

/-- The submean inequality for positive powers of a holomorphic norm also holds for complex normed
targets, by applying a norming linear functional at the center. -/
theorem norm_rpow_le_circleAverage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {c : ℂ} {R p : ℝ} (hR : 0 < R) (hp : 0 < p)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) :
    ‖f c‖ ^ p ≤ Real.circleAverage (fun z => ‖f z‖ ^ p) c R := by
  obtain ⟨L, hL, hLc⟩ := exists_dual_vector'' ℂ (f c)
  have hLf : AnalyticOnNhd ℂ (fun z => L (f z)) (closedBall c R) :=
    fun z hz => (L.analyticAt (f z)).comp_of_eq (hf z hz) rfl
  have hcenter : ‖L (f c)‖ = ‖f c‖ := by simp [hLc]
  rw [← hcenter]
  refine (norm_rpow_le_circleAverage_scalar hR hp hLf).trans ?_
  apply Real.circleAverage_mono
  · exact (hLf.continuousOn.mono sphere_subset_closedBall).norm.rpow_const
      (fun z _ => Or.inr hp.le) |>.circleIntegrable hR.le
  · exact (hf.continuousOn.mono sphere_subset_closedBall).norm.rpow_const
      (fun z _ => Or.inr hp.le) |>.circleIntegrable hR.le
  · intro z _
    exact Real.rpow_le_rpow (norm_nonneg _) ((L.le_opNorm (f z)).trans
      (by simpa using mul_le_mul_of_nonneg_right hL (norm_nonneg (f z)))) hp.le

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
