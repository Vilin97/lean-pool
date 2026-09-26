/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CauchyPompeiu

/-!
# The Cauchy transform in one variable with parameters

For a compactly supported `C¹` function `g` on `ℂ × G`, the Cauchy transform in the first
variable is `u(z, y) = π⁻¹ ∫ w⁻¹ • g (z - w, y)`. The kernel `w⁻¹` is locally integrable in the
plane, so `u` is real-differentiable with derivative obtained by differentiating under the
integral; the translation structure places the derivative on `g`. The Cauchy–Pompeiu identity
then gives `∂u/∂\bar z = g`, and along the parameter directions the antiholomorphic part of the
derivative of `u` is the Cauchy transform of the corresponding antiholomorphic part of the
derivative of `g`. The transform vanishes on every slice on which `g` vanishes.

References: [Hörmander][Hormander1973] (1973), Theorem 1.2.2 and Theorem 2.3.1;
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Proposition 4.2.2.

## Main definitions

* `cauchyTransformFst`: The Cauchy transform in the first variable of a function on `ℂ × G`.

## Main results

* `hasFDerivAt_cauchyTransformFst`: **Differentiation of the Cauchy transform.** The derivative is
  the Cauchy transform of the derivative.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Complex MeasureTheory Set Filter Metric
open scoped Real Topology

namespace SeveralComplexVariables

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Cauchy transform in the first variable of a function on `ℂ × G`. -/
@[expose] def cauchyTransformFst (g : ℂ × G → F) (x : ℂ × G) : F :=
  (π : ℂ)⁻¹ • ∫ w : ℂ, w⁻¹ • g (x - (w, 0))

section Kernel

omit [NormedSpace ℂ F] [CompleteSpace F] in
/-- The Cauchy kernel is locally integrable in the plane. -/
theorem integrable_indicator_closedBall_mul_inv_norm (C R : ℝ) :
    Integrable ((closedBall (0 : ℂ) R).indicator fun w => C * ‖w‖⁻¹) := by
  have hmeas : AEStronglyMeasurable (fun w : ℂ => C * ‖w‖⁻¹) volume :=
    (measurable_const.mul measurable_norm.inv).aestronglyMeasurable
  have h : IntegrableOn (fun w : ℂ => C * ‖w‖⁻¹) (ball 0 (R + 1)) := by
    refine integrableOn_ball_of_norm_le_rpow (E := ℂ) (μ := volume) (C := |C|) (α := 1) ?_ ?_
      (ae_of_all _ fun w => ?_) hmeas
    · rw [Complex.finrank_real_complex]; norm_num
    · rw [Complex.finrank_real_complex]; norm_num
    · rw [Real.rpow_neg_one, norm_mul, Real.norm_eq_abs, norm_inv, norm_norm]
  exact (h.mono_set (closedBall_subset_ball (lt_add_one R))).integrable_indicator
    measurableSet_closedBall

omit [CompleteSpace F] in
/-- A kernel-type bound: a function of the form `w⁻¹ • h w` with `h` bounded and vanishing outside a
closed ball is integrable. -/
theorem integrable_inv_smul_of_bound {h : ℂ → F} (hmeas : AEStronglyMeasurable h volume) {C R : ℝ}
    (hC : ∀ w, ‖h w‖ ≤ C) (hz : ∀ w, R < ‖w‖ → h w = 0) :
    Integrable fun w : ℂ => w⁻¹ • h w := by
  refine Integrable.mono' (integrable_indicator_closedBall_mul_inv_norm C R)
    (measurable_inv.aestronglyMeasurable.smul hmeas) (ae_of_all _ fun w => ?_)
  by_cases hw : w ∈ closedBall (0 : ℂ) R
  · rw [indicator_of_mem hw, norm_smul, norm_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC w) (inv_nonneg.mpr (norm_nonneg _))
  · rw [mem_closedBall, dist_zero_right, not_le] at hw
    rw [indicator_of_notMem (by rwa [mem_closedBall, dist_zero_right, not_le]), hz w hw,
      smul_zero, norm_zero]

end Kernel

section Support

variable {g : ℂ × G → F}

omit [NormedSpace ℂ G] [NormedSpace ℂ F] [CompleteSpace F] in
/-- Points far in the first variable leave the support after translation. -/
theorem sub_notMem_of_norm_gt {R' : ℝ} (hR : tsupport g ⊆ closedBall 0 R') {x₀ x : ℂ × G}
    (hx : x ∈ ball x₀ 1) {w : ℂ} (hw : R' + ‖x₀‖ + 1 < ‖w‖) : x - (w, 0) ∉ tsupport g := by
  intro hmem
  have h1 := hR hmem
  rw [mem_closedBall, dist_zero_right] at h1
  have hx' : ‖x‖ < ‖x₀‖ + 1 := by
    have := mem_ball.mp hx
    rw [dist_eq_norm] at this
    calc ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
      _ < ‖x₀‖ + 1 := by linarith
  have h2 : ‖w‖ - ‖x‖ ≤ ‖x - (w, 0)‖ := by
    have : ‖((w, 0) : ℂ × G)‖ = ‖w‖ := by rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
    rw [← this, norm_sub_rev]
    exact norm_sub_norm_le _ _
  linarith

omit [NormedSpace ℂ G] [NormedSpace ℂ F] [CompleteSpace F] in
/-- The translated function vanishes for large `w`. -/
theorem eq_zero_of_norm_gt {R' : ℝ} (hR : tsupport g ⊆ closedBall 0 R') {x₀ x : ℂ × G}
    (hx : x ∈ ball x₀ 1) {w : ℂ} (hw : R' + ‖x₀‖ + 1 < ‖w‖) : g (x - (w, 0)) = 0 :=
  image_eq_zero_of_notMem_tsupport (sub_notMem_of_norm_gt hR hx hw)

omit [CompleteSpace F] in
/-- The derivative of the translated function vanishes for large `w`. -/
theorem fderiv_eq_zero_of_norm_gt' {R' : ℝ} (hR : tsupport g ⊆ closedBall 0 R') {x₀ x : ℂ × G}
    (hx : x ∈ ball x₀ 1) {w : ℂ} (hw : R' + ‖x₀‖ + 1 < ‖w‖) : fderiv ℝ g (x - (w, 0)) = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    sub_notMem_of_norm_gt hR hx hw (tsupport_fderiv_subset ℝ h)

end Support

section Derivative

variable {g : ℂ × G → F}

omit [CompleteSpace F] in
/-- Integrability of the derivative kernel. -/
theorem integrable_inv_smul_fderiv_sub (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (x₀ : ℂ × G) : Integrable fun w : ℂ => w⁻¹ • fderiv ℝ g (x₀ - (w, 0)) := by
  obtain ⟨R', hR⟩ := hs.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hg.continuous_fderiv one_ne_zero)
  refine integrable_inv_smul_of_bound (R := R' + ‖x₀‖ + 1)
    (((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).aestronglyMeasurable)
    (fun w => hC _) fun w hw => fderiv_eq_zero_of_norm_gt' hR (mem_ball_self one_pos) hw

omit [CompleteSpace F] in
/-- Integrability of the Cauchy transform integrand. -/
theorem integrable_inv_smul_sub (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) (x₀ : ℂ × G) :
    Integrable fun w : ℂ => w⁻¹ • g (x₀ - (w, 0)) := by
  obtain ⟨R', hR⟩ := hs.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hg.continuous
  refine integrable_inv_smul_of_bound (R := R' + ‖x₀‖ + 1)
    ((hg.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (fun w => hC _) fun w hw => eq_zero_of_norm_gt hR (mem_ball_self one_pos) hw

omit [CompleteSpace F] in
/-- **Differentiation of the Cauchy transform.** The derivative is the Cauchy transform of the
derivative. -/
theorem hasFDerivAt_cauchyTransformFst (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (x₀ : ℂ × G) :
    HasFDerivAt (cauchyTransformFst g)
      ((π : ℂ)⁻¹ • ∫ w : ℂ, w⁻¹ • fderiv ℝ g (x₀ - (w, 0))) x₀ := by
  obtain ⟨R', hR⟩ := hs.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hg.continuous_fderiv one_ne_zero)
  have hmain : HasFDerivAt (fun x : ℂ × G => ∫ w : ℂ, w⁻¹ • g (x - (w, 0)))
      (∫ w : ℂ, w⁻¹ • fderiv ℝ g (x₀ - (w, 0))) x₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (F' := fun x w => w⁻¹ • fderiv ℝ g (x - (w, 0)))
      (bound := (closedBall (0 : ℂ) (R' + ‖x₀‖ + 1)).indicator fun w => C * ‖w‖⁻¹)
      (ball_mem_nhds x₀ one_pos) ?_ (integrable_inv_smul_sub hg hs x₀) ?_ ?_
      (integrable_indicator_closedBall_mul_inv_norm _ _) ?_
    · exact Eventually.of_forall fun x =>
        measurable_inv.aestronglyMeasurable.smul
          ((hg.continuous.comp (by fun_prop)).aestronglyMeasurable)
    · exact measurable_inv.aestronglyMeasurable.smul
        (((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).aestronglyMeasurable)
    · refine ae_of_all _ fun w x hx => ?_
      by_cases hw : w ∈ closedBall (0 : ℂ) (R' + ‖x₀‖ + 1)
      · rw [indicator_of_mem hw, norm_smul, norm_inv, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC _) (inv_nonneg.mpr (norm_nonneg _))
      · rw [mem_closedBall, dist_zero_right, not_le] at hw
        rw [indicator_of_notMem (by rwa [mem_closedBall, dist_zero_right, not_le]),
          fderiv_eq_zero_of_norm_gt' hR hx hw, smul_zero, norm_zero]
    · refine ae_of_all _ fun w x _ => ?_
      have h1 : HasFDerivAt (fun x : ℂ × G => x - (w, 0)) (ContinuousLinearMap.id ℝ (ℂ × G)) x :=
        (hasFDerivAt_id x).sub_const _
      have h2 := ((hg.differentiable one_ne_zero) _).hasFDerivAt.comp x h1
      rw [ContinuousLinearMap.comp_id] at h2
      exact h2.const_smul w⁻¹
  exact hmain.const_smul _

omit [CompleteSpace F] in
/-- The derivative of the Cauchy transform applied to a direction. -/
theorem fderiv_cauchyTransformFst_apply (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (x₀ v : ℂ × G) :
    fderiv ℝ (cauchyTransformFst g) x₀ v = (π : ℂ)⁻¹ • ∫ w : ℂ, w⁻¹ • fderiv ℝ g (x₀ - (w, 0)) v
      := by
  rw [(hasFDerivAt_cauchyTransformFst hg hs x₀).fderiv, smul_apply,
    ContinuousLinearMap.integral_apply (integrable_inv_smul_fderiv_sub hg hs x₀)]
  congr 1

omit [CompleteSpace F] in
/-- The antiholomorphic part of the derivative of the Cauchy transform along a direction is the
Cauchy transform of the antiholomorphic part of the derivative. -/
theorem dbarAlong_fderiv_cauchyTransformFst (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (x₀ v : ℂ × G) :
    dbarAlong (fderiv ℝ (cauchyTransformFst g) x₀) v =
      (π : ℂ)⁻¹ • ∫ w : ℂ, w⁻¹ • dbarAlong (fderiv ℝ g (x₀ - (w, 0))) v := by
  have hint := integrable_inv_smul_fderiv_sub hg hs x₀
  have h1 : Integrable fun w : ℂ => w⁻¹ • fderiv ℝ g (x₀ - (w, 0)) v := by
    simpa only [FunLike.coe_smul, Pi.smul_apply] using hint.apply_continuousLinearMap v
  have h2 : Integrable fun w : ℂ => w⁻¹ • fderiv ℝ g (x₀ - (w, 0)) (I • v) := by
    simpa only [FunLike.coe_smul, Pi.smul_apply] using hint.apply_continuousLinearMap (I • v)
  have h1' : Integrable fun w : ℂ => (2 : ℂ)⁻¹ • (w⁻¹ • fderiv ℝ g (x₀ - (w, 0)) v) := h1.smul _
  have h2' : Integrable fun w : ℂ =>
      ((2 : ℂ)⁻¹ * I) • (w⁻¹ • fderiv ℝ g (x₀ - (w, 0)) (I • v)) := h2.smul _
  have hpt : ∀ w : ℂ, w⁻¹ • ((2 : ℂ)⁻¹ • (fderiv ℝ g (x₀ - (w, 0)) v +
      I • fderiv ℝ g (x₀ - (w, 0)) (I • v))) =
      (2 : ℂ)⁻¹ • (w⁻¹ • fderiv ℝ g (x₀ - (w, 0)) v) +
        ((2 : ℂ)⁻¹ * I) • (w⁻¹ • fderiv ℝ g (x₀ - (w, 0)) (I • v)) := by
    intro w
    module
  unfold dbarAlong
  rw [fderiv_cauchyTransformFst_apply hg hs, fderiv_cauchyTransformFst_apply hg hs]
  simp_rw [hpt]
  rw [integral_add h1' h2', integral_smul, integral_smul]
  module

omit [NormedSpace ℂ G] [CompleteSpace F] in
/-- The Cauchy transform vanishes on a slice where `g` vanishes. -/
theorem cauchyTransformFst_eq_zero {y : G} (hy : ∀ z : ℂ, g (z, y) = 0) (z : ℂ) :
    cauchyTransformFst g (z, y) = 0 := by
  unfold cauchyTransformFst
  have : ∀ w : ℂ, w⁻¹ • g (z - w, y) = 0 := fun w => by rw [hy, smul_zero]
  simp only [Prod.mk_sub_mk, sub_zero, this, integral_zero, smul_zero]

end Derivative

section Pompeiu

variable {h : ℂ × G → F}

/-- The Cauchy–Pompeiu identity in the first variable with parameters: the Cauchy transform of
`∂h/∂\bar z₁` recovers `h`. -/
theorem integral_inv_smul_dbarAlong_fderiv_sub (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h)
    (x₀ : ℂ × G) :
    ∫ w : ℂ, w⁻¹ • dbarAlong (fderiv ℝ h (x₀ - (w, 0))) ((1 : ℂ), (0 : G)) = (π : ℂ) • h x₀ := by
  set ψ : ℂ → F := fun w => h (x₀ - (w, 0)) with hψ
  have hiso : Isometry fun w : ℂ => x₀ - (w, 0) := by
    refine Isometry.of_dist_eq fun w w' => ?_
    rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_left, Prod.mk_sub_mk, sub_zero, Prod.norm_mk,
      norm_zero, max_eq_left (norm_nonneg _), norm_sub_rev]
  have hψs : HasCompactSupport ψ := hs.comp_isClosedEmbedding hiso.isClosedEmbedding
  have hψc : ContDiff ℝ 1 ψ :=
    hh.comp (contDiff_const.sub (ContinuousLinearMap.inl ℝ ℂ G).contDiff)
  have hder : ∀ w : ℂ, fderiv ℝ ψ w =
      (fderiv ℝ h (x₀ - (w, 0))).comp (-(ContinuousLinearMap.inl ℝ ℂ G)) := by
    intro w
    have h1 : HasFDerivAt (fun w : ℂ => x₀ - (w, 0)) (-(ContinuousLinearMap.inl ℝ ℂ G)) w :=
      (ContinuousLinearMap.inl ℝ ℂ G).hasFDerivAt.const_sub x₀
    exact (((hh.differentiable one_ne_zero) _).hasFDerivAt.comp w h1).fderiv
  have hdbar : ∀ w : ℂ, dbarAlong (fderiv ℝ ψ w) 1 =
      -dbarAlong (fderiv ℝ h (x₀ - (w, 0))) ((1 : ℂ), (0 : G)) := by
    intro w
    rw [hder]
    simp only [dbarAlong, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.inl_apply, map_neg, smul_eq_mul, mul_one, Prod.smul_mk, smul_zero,
      smul_neg]
    module
  have := integral_inv_smul_dbarAlong_fderiv hψc hψs
  simp_rw [hdbar, smul_neg, integral_neg] at this
  rw [neg_eq_iff_eq_neg.mp this, neg_neg, hψ]
  simp only
  rw [show ((0 : ℂ), (0 : G)) = 0 from rfl, sub_zero]

end Pompeiu

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
