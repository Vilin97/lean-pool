/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Cauchy's formula on an annulus

Subtracting the value at the evaluation point removes the singularity of the Cauchy kernel.
Cauchy–Goursat on an annulus then gives the difference of the outer and inner Cauchy integrals.

## Main results

`circleIntegral_sub_inv_smul_sub_of_analyticOnNhd_annulus` is the annulus formula.
`circleIntegral_sub_inv_eq_zero_of_lt_norm` vanishes the inner integral when the evaluation
point lies outside the inner circle. `hasSum_circleIntegral_geometric` expands the outer kernel
as a geometric series.
-/

public noncomputable section

open Complex Set Metric Filter
open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Integrating a divided difference separates the function and constant terms. -/
private theorem circleIntegral_dslope {f : ℂ → F} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (sphere (0 : ℂ) r)) {z : ℂ}
    (hz : ∀ w ∈ sphere (0 : ℂ) r, w ≠ z) :
    (∮ w in C(0, r), dslope f z w) =
      (∮ w in C(0, r), (w - z)⁻¹ • f w) -
        (∮ w in C(0, r), (w - z)⁻¹) • f z := by
  have hk : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (sphere 0 r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun w hw => sub_ne_zero.mpr (hz w hw)
  have h₁ : CircleIntegrable (fun w => (w - z)⁻¹ • f w) 0 r :=
    (hk.smul hf).circleIntegrable hr
  have h₂ : CircleIntegrable (fun w => (w - z)⁻¹ • f z) 0 r :=
    (hk.smul continuousOn_const).circleIntegrable hr
  rw [← circleIntegral.integral_smul_const, ← circleIntegral.integral_sub h₁ h₂]
  apply circleIntegral.integral_congr hr
  intro w hw
  rw [dslope_of_ne _ (hz w hw), slope_def_module, smul_sub]

/-- The Cauchy kernel has zero integral on a circle that does not enclose its pole. -/
theorem circleIntegral_sub_inv_eq_zero_of_lt_norm {r : ℝ} (hr : 0 ≤ r) {z : ℂ}
    (hz : r < ‖z‖) : (∮ w in C(0, r), (w - z)⁻¹) = 0 := by
  have hd : DifferentiableOn ℂ (fun w : ℂ => (w - z)⁻¹) (closedBall 0 r) := by
    intro w hw
    apply ((differentiableAt_id.sub_const z).inv ?_).differentiableWithinAt
    apply sub_ne_zero.mpr
    intro he
    change w = z at he
    subst w
    exact (not_le.mpr hz) (mem_closedBall_zero_iff.mp hw)
  exact (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr

/-- Cauchy's formula between two concentric circles, for Banach-valued functions. -/
theorem circleIntegral_sub_inv_smul_sub_of_analyticOnNhd_annulus
    {f : ℂ → F} {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hzr : r < ‖z‖) (hzR : ‖z‖ < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R \ ball 0 r)) :
    (∮ w in C(0, R), (w - z)⁻¹ • f w) -
      (∮ w in C(0, r), (w - z)⁻¹ • f w) = (2 * Real.pi * I : ℂ) • f z := by
  have hz : z ∈ closedBall (0 : ℂ) R \ ball 0 r := by
    simp only [Set.mem_sdiff, mem_closedBall_zero_iff, mem_ball_zero_iff, not_lt]
    exact ⟨hzR.le, hzr.le⟩
  have hn : closedBall (0 : ℂ) R \ ball 0 r ∈ 𝓝 z :=
    inter_mem (closedBall_mem_nhds_of_mem (mem_ball_zero_iff.mpr hzR))
      (mem_of_superset
        (isClosed_closedBall.isOpen_compl.mem_nhds
          (show z ∈ (closedBall (0 : ℂ) r)ᶜ by simpa using hzr))
        (compl_subset_compl.mpr ball_subset_closedBall))
  have hcont := (continuousOn_dslope hn).mpr ⟨hf.continuousOn, (hf z hz).differentiableAt⟩
  have he := circleIntegral_eq_of_differentiable_on_annulus_off_countable hr
    (hzr.trans hzR).le (countable_singleton z) hcont (by
      intro w hw
      apply (differentiableAt_dslope_of_ne (by simpa using hw.2)).mpr
      exact (hf w ⟨ball_subset_closedBall hw.1.1,
        fun hb => hw.1.2 (ball_subset_closedBall hb)⟩).differentiableAt)
  have hs (t : ℝ) (ht : t = r ∨ t = R) : sphere (0 : ℂ) t ⊆ closedBall 0 R \ ball 0 r := by
    rintro w hw
    have hw' := mem_sphere_zero_iff_norm.mp hw
    simp only [Set.mem_sdiff, mem_closedBall_zero_iff, mem_ball_zero_iff, not_lt, hw']
    rcases ht with rfl | rfl <;> constructor <;> linarith
  rw [circleIntegral_dslope (hr.trans (hzr.trans hzR)).le
      (hf.continuousOn.mono (hs R (Or.inr rfl))) (by
        intro w hw he; subst w; exact (ne_of_lt hzR) (mem_sphere_zero_iff_norm.mp hw)),
    circleIntegral_dslope hr.le (hf.continuousOn.mono (hs r (Or.inl rfl))) (by
        intro w hw he; subst w; exact (ne_of_gt hzr) (mem_sphere_zero_iff_norm.mp hw)),
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_zero_iff.mpr hzR),
    circleIntegral_sub_inv_eq_zero_of_lt_norm hr.le hzr, zero_smul, sub_zero] at he
  exact sub_eq_iff_eq_add.mpr (sub_eq_iff_eq_add.mp he |>.trans (add_comm _ _))

omit [CompleteSpace F] in
/-- A uniformly contracting scalar kernel can be summed under a circle integral. -/
theorem hasSum_circleIntegral_geometric {f : ℂ → F} {g : ℂ → ℂ} {r q : ℝ}
    (hr : 0 ≤ r) (hf : ContinuousOn f (sphere (0 : ℂ) r))
    (hg : ContinuousOn g (sphere (0 : ℂ) r)) (hq₀ : 0 ≤ q) (hq : q < 1)
    (hbound : ∀ w ∈ sphere (0 : ℂ) r, ‖g w‖ ≤ q) :
    HasSum (fun n : ℕ => ∮ w in C(0, r), g w ^ n • f w)
      (∮ w in C(0, r), (1 - g w)⁻¹ • f w) := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn hf
  have hfc : Continuous (fun θ => f (circleMap 0 r θ)) :=
    hf.comp_continuous (continuous_circleMap _ _) (circleMap_mem_sphere _ hr)
  have hgc : Continuous (fun θ => g (circleMap 0 r θ)) :=
    hg.comp_continuous (continuous_circleMap _ _) (circleMap_mem_sphere _ hr)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => r * (q ^ n * M)) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · apply Continuous.aestronglyMeasurable
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 r).mul_const I).smul ((hgc.pow n).smul hfc)
  · refine .of_forall fun θ _ => ?_
    simp only [norm_smul, norm_pow]
    have hd : ‖deriv (circleMap 0 r) θ‖ = r := by simp [deriv_circleMap, abs_of_nonneg hr]
    rw [hd]
    gcongr
    · exact hbound _ (circleMap_mem_sphere _ hr θ)
    · exact hM _ (circleMap_mem_sphere _ hr θ)
  · exact .of_forall fun _ _ =>
      ((summable_geometric_of_lt_one hq₀ hq).mul_right M).mul_left r
  · exact intervalIntegrable_const
  · refine .of_forall fun θ _ => ?_
    exact ((hasSum_geometric_of_norm_lt_one
      ((hbound _ (circleMap_mem_sphere _ hr θ)).trans_lt hq)).smul_const _).const_smul _

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
