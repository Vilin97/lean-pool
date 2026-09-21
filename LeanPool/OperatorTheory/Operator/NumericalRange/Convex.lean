/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Convexity of the numerical range

This file proves the Toeplitz--Hausdorff theorem: the numerical range of a
bounded linear operator on a complex inner product space is convex over `ℝ`.
-/
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Order.IntermediateValue
import LeanPool.OperatorTheory.Operator.NumericalRange.Basic
import LeanPool.OperatorTheory.Operator.NumericalRange.Helpers

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private lemma inner_smul_apply_smul (A : E →L[ℂ] E) (c : ℂ) (x : E) :
    ⟪c • x, A (c • x)⟫_ℂ = (‖c‖ ^ 2 : ℂ) * ⟪x, A x⟫_ℂ := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul']

private lemma inner_apply_self_eq_of_smul (A : E →L[ℂ] E) (c : ℂ) (x y : E)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : c • y = x) :
    ⟪x, A x⟫_ℂ = ⟪y, A y⟫_ℂ := by
  have hc : ‖c‖ = 1 := by
    simpa only [norm_smul, hx, hy, mul_one] using congrArg norm hxy
  rw [← hxy, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul', hc]
  norm_num

/-- A nonzero scalar rotating the full pair of cross terms onto the real axis. -/
private noncomputable def phaseScalar (p q : ℂ) : ℂ :=
  if p - starRingEnd ℂ q = 0 then 1 else (p - starRingEnd ℂ q)⁻¹

private lemma phaseScalar_ne_zero (p q : ℂ) : phaseScalar p q ≠ 0 := by
  unfold phaseScalar
  split_ifs with h
  · exact one_ne_zero
  · exact inv_ne_zero h

private lemma phaseScalar_cross_im (p q : ℂ) :
    (phaseScalar p q * p + starRingEnd ℂ (phaseScalar p q) * q).im = 0 := by
  rw [show (phaseScalar p q * p + starRingEnd ℂ (phaseScalar p q) * q).im =
      (phaseScalar p q * (p - starRingEnd ℂ q)).im by
    simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im]
    ring]
  unfold phaseScalar
  split_ifs with h
  · rw [h, mul_zero]
    exact Complex.zero_im
  · rw [inv_mul_cancel₀ h]
    exact Complex.one_im

private lemma affinePath_ne_zero (x₀ x₁ : E) (ω : ℂ) (hω : ω ≠ 0)
    (hlin : LinearIndependent ℂ ![x₀, x₁]) (r : ℝ) :
    ((1 - r : ℝ) : ℂ) • x₀ + (r : ℂ) • (ω • x₁) ≠ 0 := by
  intro hv
  have hc := hlin.eq_zero_of_pair (s := ((1 - r : ℝ) : ℂ))
    (t := (r : ℂ) * ω) (by simpa only [smul_smul] using hv)
  have hr1 : r = 1 := by
    have hre := congrArg Complex.re hc.1
    norm_num at hre
    linarith
  have hrc : (r : ℂ) = 0 := (mul_eq_zero.mp hc.2).resolve_right hω
  have hr0 : r = 0 := by
    have hre := congrArg Complex.re hrc
    norm_num at hre ⊢
    exact hre
  linarith

private lemma inner_affinePath_apply (B : E →L[ℂ] E) (x₀ x₁ : E)
    (ω : ℂ) (u v : ℝ) :
    ⟪((u : ℂ) • x₀ + (v : ℂ) • (ω • x₁)),
      B ((u : ℂ) • x₀ + (v : ℂ) • (ω • x₁))⟫_ℂ =
      (u : ℂ) ^ 2 * ⟪x₀, B x₀⟫_ℂ +
        ((u * v : ℝ) : ℂ) *
          (ω * ⟪x₀, B x₁⟫_ℂ + starRingEnd ℂ ω * ⟪x₁, B x₀⟫_ℂ) +
        (v : ℂ) ^ 2 * (‖ω‖ ^ 2 : ℂ) * ⟪x₁, B x₁⟫_ℂ := by
  exact inner_apply_real_smul_add_real_smul B x₀ x₁ ω u v

private lemma inner_affinePath_apply_im_eq_zero (B : E →L[ℂ] E)
    (x₀ x₁ : E) (ω : ℂ) (u v : ℝ)
    (h₀ : ⟪x₀, B x₀⟫_ℂ = 0) (h₁ : ⟪x₁, B x₁⟫_ℂ = 1)
    (hc : (ω * ⟪x₀, B x₁⟫_ℂ +
      starRingEnd ℂ ω * ⟪x₁, B x₀⟫_ℂ).im = 0) :
    (⟪((u : ℂ) • x₀ + (v : ℂ) • (ω • x₁)),
      B ((u : ℂ) • x₀ + (v : ℂ) • (ω • x₁))⟫_ℂ).im = 0 := by
  rw [inner_affinePath_apply, h₀, h₁]
  simp only [mul_zero, zero_add, mul_one]
  rw [Complex.add_im]
  have hleft : (((u * v : ℝ) : ℂ) *
      (ω * ⟪x₀, B x₁⟫_ℂ + starRingEnd ℂ ω * ⟪x₁, B x₀⟫_ℂ)).im = 0 := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hc]
    ring
  have hright : ((v : ℂ) ^ 2 * (‖ω‖ ^ 2 : ℂ)).im = 0 := by
    rw [show (v : ℂ) ^ 2 * (‖ω‖ ^ 2 : ℂ) =
      ((v ^ 2 * ‖ω‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_im _
  rw [hleft, hright, add_zero]

/-- The normalized `0`-to-`1` core of Toeplitz--Hausdorff. The affine path is
nonzero by linear independence, its phase-adjusted quadratic form is real,
and the intermediate value theorem supplies every point of `[0, 1]`. -/
private lemma normalized_segment_exists (B : E →L[ℂ] E) (x₀ x₁ : E)
    (hlin : LinearIndependent ℂ ![x₀, x₁])
    (hx₀ : ‖x₀‖ = 1) (hx₁ : ‖x₁‖ = 1)
    (h₀ : ⟪x₀, B x₀⟫_ℂ = 0) (h₁ : ⟪x₁, B x₁⟫_ℂ = 1)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ∃ y : E, ‖y‖ = 1 ∧ ⟪y, B y⟫_ℂ = (t : ℂ) := by
  let p : ℂ := ⟪x₀, B x₁⟫_ℂ
  let q : ℂ := ⟪x₁, B x₀⟫_ℂ
  let ω : ℂ := phaseScalar p q
  have hω : ω ≠ 0 := phaseScalar_ne_zero p q
  have hcross : (ω * ⟪x₀, B x₁⟫_ℂ +
      starRingEnd ℂ ω * ⟪x₁, B x₀⟫_ℂ).im = 0 := by
    exact phaseScalar_cross_im p q
  let v : ℝ → E := fun r =>
    ((1 - r : ℝ) : ℂ) • x₀ + (r : ℂ) • (ω • x₁)
  have hv_ne (r : ℝ) : v r ≠ 0 := by
    exact affinePath_ne_zero x₀ x₁ ω hω hlin r
  let y : ℝ → E := fun r => ((‖v r‖ : ℂ)⁻¹) • v r
  have hy_norm (r : ℝ) : ‖y r‖ = 1 := by
    exact norm_inv_norm_smul (hv_ne r)
  have hv_cont : Continuous v := by
    dsimp only [v]
    fun_prop
  have hnorm_cont : Continuous (fun r => (‖v r‖ : ℂ)) := by
    fun_prop
  have hnorm_ne (r : ℝ) : (‖v r‖ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hv_ne r))
  have hinv_cont : Continuous (fun r => (‖v r‖ : ℂ)⁻¹) :=
    hnorm_cont.inv₀ hnorm_ne
  have hy_cont : Continuous y := by
    dsimp only [y]
    exact hinv_cont.smul hv_cont
  let F : ℝ → ℝ := fun r => (⟪y r, B (y r)⟫_ℂ).re
  have hF_cont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hv_im (r : ℝ) : (⟪v r, B (v r)⟫_ℂ).im = 0 := by
    exact inner_affinePath_apply_im_eq_zero B x₀ x₁ ω (1 - r) r h₀ h₁ hcross
  have hy_im (r : ℝ) : (⟪y r, B (y r)⟫_ℂ).im = 0 := by
    rw [show ⟪y r, B (y r)⟫_ℂ =
        (‖(‖v r‖ : ℂ)⁻¹‖ ^ 2 : ℂ) * ⟪v r, B (v r)⟫_ℂ by
      exact inner_smul_apply_smul B (‖v r‖ : ℂ)⁻¹ (v r)]
    rw [Complex.mul_im, hv_im]
    have hfactor_im : ((‖(‖v r‖ : ℂ)⁻¹‖ : ℂ) ^ 2).im = 0 := by
      rw [pow_two, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hfactor_im]
    ring
  have hy₀ : y 0 = x₀ := by
    simp only [y, v, sub_zero, Complex.ofReal_one, one_smul, Complex.ofReal_zero,
      zero_smul, add_zero, hx₀, inv_one]
  have hv₁ : v 1 = ω • x₁ := by
    simp only [v, sub_self, Complex.ofReal_zero, zero_smul, Complex.ofReal_one,
      one_smul, zero_add]
  have hy₁_q : ⟪y 1, B (y 1)⟫_ℂ = ⟪x₁, B x₁⟫_ℂ := by
    apply inner_apply_self_eq_of_smul B (((‖v 1‖ : ℂ)⁻¹) * ω) (y 1) x₁
      (hy_norm 1) hx₁
    dsimp only [y]
    rw [hv₁, smul_smul]
  have hF₀ : F 0 = 0 := by
    dsimp only [F]
    rw [hy₀, h₀]
    exact Complex.zero_re
  have hF₁ : F 1 = 1 := by
    dsimp only [F]
    rw [hy₁_q, h₁]
    exact Complex.one_re
  have ht : t ∈ Set.Icc (F 0) (F 1) := by
    rw [hF₀, hF₁]
    exact ⟨ht₀, ht₁⟩
  obtain ⟨r, _hr, hFr⟩ :=
    intermediate_value_Icc (a := (0 : ℝ)) (b := 1) zero_le_one
      hF_cont.continuousOn ht
  refine ⟨y r, hy_norm r, ?_⟩
  apply Complex.ext
  · simpa only [F, Complex.ofReal_re] using hFr
  · rw [hy_im, Complex.ofReal_im]

/-- The Toeplitz--Hausdorff theorem: the numerical range of a bounded linear
operator on a complex inner product space is convex. -/
theorem convex_numericalRange (A : E →L[ℂ] E) :
    Convex ℝ (numericalRange A) := by
  intro z₀ hz₀ z₁ hz₁ a b ha hb hab
  by_cases hz : z₀ = z₁
  · subst z₁
    rw [← add_smul, hab, one_smul]
    exact hz₀
  obtain ⟨x₀, hx₀, hAx₀⟩ := hz₀
  obtain ⟨x₁, hx₁, hAx₁⟩ := hz₁
  have hlin : LinearIndependent ℂ ![x₀, x₁] := by
    by_contra hn
    apply hz
    calc
      z₀ = ⟪x₀, A x₀⟫_ℂ := hAx₀.symm
      _ = ⟪x₁, A x₁⟫_ℂ :=
        inner_apply_self_eq_of_not_linearIndependent A hx₀ hx₁ hn
      _ = z₁ := hAx₁
  let B : E →L[ℂ] E := (z₁ - z₀)⁻¹ • (A - z₀ • 1)
  have hB₀ : ⟪x₀, B x₀⟫_ℂ = 0 := by
    dsimp only [B]
    rw [inner_smul_sub_smul_one_apply_self _ _ A hx₀, hAx₀]
    ring
  have hB₁ : ⟪x₁, B x₁⟫_ℂ = 1 := by
    dsimp only [B]
    rw [inner_smul_sub_smul_one_apply_self _ _ A hx₁, hAx₁]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hz))
  have hb_one : b ≤ 1 := by linarith
  obtain ⟨y, hy, hBy⟩ :=
    normalized_segment_exists B x₀ x₁ hlin hx₀ hx₁ hB₀ hB₁ b hb hb_one
  have hb_mem_B : (b : ℂ) ∈ numericalRange B := ⟨y, hy, hBy⟩
  have hb_mem : (b : ℂ) ∈ numericalRange ((z₁ - z₀)⁻¹ • (A - z₀ • 1)) := by
    exact hb_mem_B
  exact smul_add_smul_mem_numericalRange_of_mem_normalized A hz hab hb_mem
/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
