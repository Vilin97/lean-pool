/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.SeparateAnalytic.Submean

/-!
# Ball submean estimates for holomorphic norms

Averaging unit complex rotations converts the circle submean inequality into a volume submean
inequality on closed balls of a finite-dimensional complex normed space carrying an additive
Haar volume. This avoids polar-coordinate integration and applies to all positive powers of
norms, including the roots used in Hartogs' lemma. The one-variable case is the disc inequality;
the case of a finite coordinate space is used for the base variables in Hartogs'
separate-analyticity theorem.

## Main results

`volume_mul_norm_rpow_le_integral_closedBall` is the volume submean inequality for positive
powers of holomorphic norms on a closed ball. `integral_closedBall_smul_rotation` averages unit
complex rotations.
-/

public section

open Complex Filter Function MeasureTheory Metric Set
open scoped Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- Unit complex rotations preserve the integral of any real function on a closed ball. Rotation
preserves the unit ball, so it has unit determinant and preserves Haar volume. -/
private theorem integral_closedBall_smul_rotation (u : E → ℝ) (R : ℝ)
    {w : ℂ} (hw : ‖w‖ = 1) :
    ∫ z in closedBall (0 : E) R, u (w • z) = ∫ z in closedBall (0 : E) R, u z := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  let e : E ≃L[ℝ] E :=
    ((LinearEquiv.smulOfNeZero ℂ E w hw0).restrictScalars ℝ).toContinuousLinearEquiv
  have he (z : E) : e z = w • z := rfl
  have hpre (s : ℝ) : e ⁻¹' closedBall 0 s = closedBall 0 s := by
    ext z
    simp only [mem_preimage, mem_closedBall, dist_zero_right, he, norm_smul, hw, one_mul]
  have hdet : ENNReal.ofReal |LinearMap.det (e.symm : E →ₗ[ℝ] E)| = 1 := by
    have h := Measure.addHaar_preimage_continuousLinearEquiv volume e (closedBall (0 : E) 1)
    rw [hpre] at h
    exact (ENNReal.mul_left_inj (measure_closedBall_pos volume (0 : E) one_pos).ne'
      measure_closedBall_lt_top.ne).mp (by rw [one_mul]; exact h.symm)
  have hmp : MeasurePreserving e volume volume := by
    refine ⟨e.continuous.measurable, Measure.ext fun s hs => ?_⟩
    rw [Measure.map_apply e.continuous.measurable hs,
      Measure.addHaar_preimage_continuousLinearEquiv, hdet, one_mul]
  simpa only [hpre, he] using hmp.setIntegral_preimage_emb
    e.toHomeomorph.isClosedEmbedding.measurableEmbedding u (closedBall 0 R)

/-- Averaging rotations turns circle submean inequalities into a ball inequality. Only continuity on
the ball is required of the real-valued function. -/
theorem volume_mul_le_integral_closedBall_of_circle_submean {u : E → ℝ} {R A : ℝ}
    (hu : ContinuousOn u (closedBall 0 R))
    (hmean : ∀ z ∈ closedBall (0 : E) R,
      A ≤ Real.circleAverage (fun w => u (w • z)) 0 1) :
    volume.real (closedBall (0 : E) R) * A ≤ ∫ z in closedBall (0 : E) R, u z := by
  let B := closedBall (0 : E) R
  let T := Icc (0 : ℝ) (2 * π)
  let H := fun (z : E) (θ : ℝ) => u (circleMap 0 1 θ • z)
  have hrot (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by simp
  have hmap : MapsTo (fun p : E × ℝ => circleMap 0 1 p.2 • p.1) (B ×ˢ T) B := by
    intro z hz
    simpa only [B, mem_closedBall, dist_zero_right, norm_smul, hrot, one_mul] using hz.1
  have hcont : ContinuousOn (uncurry H) (B ×ˢ T) := hu.comp (by fun_prop) hmap
  have hint : Integrable (uncurry H) ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hcont.integrableOn_compact ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hpoint (z : E) (hz : z ∈ B) : (2 * π) * A ≤ ∫ θ in T, H z θ := by
    have h := hmean z hz
    rw [Real.circleAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le,
      ← integral_Icc_eq_integral_Ioc, smul_eq_mul] at h
    exact (le_inv_mul_iff₀ Real.two_pi_pos).mp h
  have hbound := setIntegral_mono_on
    (integrableOn_const (isCompact_closedBall (0 : E) R).measure_lt_top.ne)
    hint.integral_prod_left measurableSet_closedBall hpoint
  have hswap := integral_integral_swap hint
  have hright : (∫ θ in T, ∫ z in B, H z θ) = (2 * π) * ∫ z in B, u z := by
    simp_rw [H, B, integral_closedBall_smul_rotation u R (hrot _)]
    simp [T, integral_const, Real.volume_Icc, Measure.real, ENNReal.toReal_ofReal Real.pi_pos.le]
  simp only [uncurry_apply_pair] at hbound
  rw [integral_const, hswap, hright] at hbound
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at hbound
  change volume.real B * (2 * π * A) ≤ 2 * π * ∫ z in B, u z at hbound
  change volume.real B * A ≤ ∫ z in B, u z
  apply (mul_le_mul_iff_right₀ Real.two_pi_pos).mp
  nlinarith only [hbound]

/-- Every positive power of a holomorphic norm satisfies the volume submean inequality on a closed
ball. No completeness of the target is needed. -/
theorem volume_mul_norm_rpow_le_integral_closedBall
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {c : E} {R p : ℝ} (hp : 0 < p)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) :
    volume.real (closedBall c R) * ‖f c‖ ^ p ≤ ∫ z in closedBall c R, ‖f z‖ ^ p := by
  have hpre : (fun z : E => c + z) ⁻¹' closedBall c R = closedBall 0 R := by
    ext z
    simp [mem_closedBall, dist_eq_norm]
  have hvol : volume (closedBall (0 : E) R) = volume (closedBall c R) := by
    rw [← hpre]
    exact measure_preimage_add volume c _
  have htrans : AnalyticOnNhd ℂ (fun z => f (c + z)) (closedBall 0 R) := by
    intro z hz
    exact (hf _ (by simpa [mem_closedBall, dist_eq_norm] using hz)).comp_of_eq
      (analyticAt_const.add analyticAt_id) rfl
  have hb := volume_mul_le_integral_closedBall_of_circle_submean
    (htrans.continuousOn.norm.rpow_const (fun _ _ => Or.inr hp.le)) (A := ‖f c‖ ^ p) ?_
  · have hm := (measurePreserving_add_left (volume : Measure E) c).setIntegral_preimage_emb
      (Homeomorph.addLeft c).isClosedEmbedding.measurableEmbedding
      (fun z => ‖f z‖ ^ p) (closedBall c R)
    rw [hpre] at hm
    simpa only [Measure.real, hvol, hm] using hb
  · intro z hz
    have hline : AnalyticOnNhd ℂ (fun w : ℂ => f (c + w • z)) (closedBall 0 1) := by
      intro w hw
      apply (hf (c + w • z) ?_).comp_of_eq
        (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) rfl
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact (mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.mp hw)
        (norm_nonneg z)).trans (by simpa using hz)
    simpa only [zero_smul, add_zero] using norm_rpow_le_circleAverage zero_lt_one hp hline

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
