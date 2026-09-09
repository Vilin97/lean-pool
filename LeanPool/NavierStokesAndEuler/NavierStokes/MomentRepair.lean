/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Finite moment repair

This file proves the finite-dimensional algebra behind the manuscript's moment
repairs. Nonsingularity is an explicit hypothesis for an arbitrary family of
moment functionals and correction profiles. It is proved separately for a
two-row weighted point-evaluation matrix. No assertion about the existence of
smooth bumps or the conditioning of their moment matrices is implicit here.
-/

noncomputable section

open scoped BigOperators NNReal

namespace NavierStokes.MomentRepair

section LinearRepair

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module ℝ V]

/-- The vector of prescribed linear moments. -/
def moments (L : ι → V →ₗ[ℝ] ℝ) (u : V) : ι → ℝ := fun i => L i u

/-- A finite correction assembled from fixed profiles. -/
def synthesize (b : ι → V) (c : ι → ℝ) : V := ∑ j, c j • b j

/-- Each column records the moments of one correction profile. -/
def momentMatrix (L : ι → V →ₗ[ℝ] ℝ) (b : ι → V) : Matrix ι ι ℝ :=
  fun i j => L i (b j)

omit [DecidableEq ι] in
theorem moments_synthesize (L : ι → V →ₗ[ℝ] ℝ) (b : ι → V) (c : ι → ℝ) :
    moments L (synthesize b c) = (momentMatrix L b).mulVec c := by
  ext i
  simp [moments, synthesize, momentMatrix, Matrix.mulVec, dotProduct, mul_comm]

/-- Coefficients obtained using the actual matrix inverse. -/
def coefficients (B : Matrix ι ι ℝ) (d : ι → ℝ) : ι → ℝ := B⁻¹.mulVec d

theorem matrix_mul_coefficients (B : Matrix ι ι ℝ) (hB : B.det ≠ 0)
    (d : ι → ℝ) : B.mulVec (coefficients B d) = d := by
  rw [coefficients, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec]

theorem coefficients_unique (B : Matrix ι ι ℝ) (hB : B.det ≠ 0)
    (d c : ι → ℝ) (hc : B.mulVec c = d) : c = coefficients B d := by
  rw [coefficients, ← hc, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec]

/-- Add a finite correction which targets an arbitrary vector of moments. -/
def repair (L : ι → V →ₗ[ℝ] ℝ) (b : ι → V) (u : V) (target : ι → ℝ) : V :=
  u + synthesize b (coefficients (momentMatrix L b) (target - moments L u))

/-- Exact moment matching follows from nonsingularity, with no smallness needed. -/
theorem repair_exact (L : ι → V →ₗ[ℝ] ℝ) (b : ι → V)
    (hB : (momentMatrix L b).det ≠ 0) (u : V) (target : ι → ℝ) :
    moments L (repair L b u target) = target := by
  have h := matrix_mul_coefficients (momentMatrix L b) hB (target - moments L u)
  rw [← moments_synthesize L b] at h
  ext i
  have hi := congrFun h i
  change L i (u + synthesize b _) = target i
  rw [map_add]
  change L i u + moments L (synthesize b _) i = target i
  rw [hi]
  simp [moments]

theorem repair_unchanged_when_exact (L : ι → V →ₗ[ℝ] ℝ) (b : ι → V) (u : V) :
    repair L b u (moments L u) = u := by
  simp [repair, coefficients, synthesize]

/-- An arbitrary correction attaining the target has the computed coefficients. -/
theorem repair_coefficients_unique (L : ι → V →ₗ[ℝ] ℝ) (b : ι → V)
    (hB : (momentMatrix L b).det ≠ 0) (u : V) (target c : ι → ℝ)
    (hc : moments L (u + synthesize b c) = target) :
    c = coefficients (momentMatrix L b) (target - moments L u) := by
  apply coefficients_unique (momentMatrix L b) hB
  rw [← moments_synthesize L b]
  ext i
  have hi := congrFun hc i
  change L i (u + synthesize b c) = target i at hi
  simp only [map_add] at hi
  change L i (synthesize b c) = target i - L i u
  linarith

/-- The repair is idempotent for fixed target moments. -/
theorem repair_idempotent (L : ι → V →ₗ[ℝ] ℝ) (b : ι → V)
    (hB : (momentMatrix L b).det ≠ 0) (u : V) (target : ι → ℝ) :
    repair L b (repair L b u target) target = repair L b u target := by
  conv_lhs => rhs; rw [← repair_exact L b hB u target]
  exact repair_unchanged_when_exact L b (repair L b u target)

end LinearRepair

section Support

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]

/-- Correction cannot change the function where every correction profile vanishes. -/
theorem repair_eq_of_profiles_zero (L : ι → (X → ℝ) →ₗ[ℝ] ℝ) (b : ι → X → ℝ)
    (u : X → ℝ) (target : ι → ℝ) (x : X) (hb : ∀ j, b j x = 0) :
    repair L b u target x = u x := by
  simp [repair, synthesize, Finset.sum_apply, hb]

/-- A common support set is preserved by finite moment repair. -/
theorem repair_support_subset (L : ι → (X → ℝ) →ₗ[ℝ] ℝ) (b : ι → X → ℝ)
    (u : X → ℝ) (target : ι → ℝ) (S : Set X)
    (hb : ∀ j, Function.support (b j) ⊆ S) :
    Function.support (repair L b u target - u) ⊆ S := by
  intro x hx
  by_contra hxs
  have hzero : ∀ j, b j x = 0 := by
    intro j
    by_contra h
    exact hxs (hb j h)
  have h := repair_eq_of_profiles_zero L b u target x hzero
  exact hx (by simpa using sub_eq_zero.mpr h)

end Support

/-- The two-row weighted evaluation matrix for exponents `0` and `1`. -/
def twoPointMatrix (x₁ x₂ w₁ w₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![w₁, w₂; x₁ * w₁, x₂ * w₂]

theorem twoPointMatrix_det (x₁ x₂ w₁ w₂ : ℝ) :
    (twoPointMatrix x₁ x₂ w₁ w₂).det = w₁ * w₂ * (x₂ - x₁) := by
  simp [twoPointMatrix, Matrix.det_fin_two]
  ring

/-- Ordered nodes and positive weights genuinely imply nonsingularity in two rows. -/
theorem twoPointMatrix_det_pos (x₁ x₂ w₁ w₂ : ℝ)
    (hx : x₁ < x₂) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    0 < (twoPointMatrix x₁ x₂ w₁ w₂).det := by
  rw [twoPointMatrix_det]
  exact mul_pos (mul_pos hw₁ hw₂) (sub_pos.mpr hx)

section NonlinearRepair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fixed-point iteration used to solve `B c + Q c = d`. -/
def correctionIteration (B : E ≃L[ℝ] E) (Q : E → E) (d c : E) : E :=
  B.symm (d - Q c)

/-- The quantitative hypotheses in Lemma 3.7 make the correction ball invariant. -/
theorem correctionIteration_norm_le
    (B : E ≃L[ℝ] E) (Q : E → E) (d : E) (β K r : ℝ)
    (hβ : 0 ≤ β) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hB : ∀ x, ‖B.symm x‖ ≤ β * ‖x‖)
    (hQ : ∀ x, ‖x‖ ≤ r → ‖Q x‖ ≤ K * ‖x‖ ^ 2)
    (hsmall : 4 * β * K * r ≤ 1) (hd : 2 * β * ‖d‖ ≤ r)
    (c : E) (hc : ‖c‖ ≤ r) : ‖correctionIteration B Q d c‖ ≤ r := by
  have hc2 : ‖c‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg c]
  have hQc : ‖Q c‖ ≤ K * r ^ 2 :=
    (hQ c hc).trans (mul_le_mul_of_nonneg_left hc2 hK)
  have hsr := mul_le_mul_of_nonneg_right hsmall hr
  calc
    ‖correctionIteration B Q d c‖ ≤ β * ‖d - Q c‖ := hB _
    _ ≤ β * (‖d‖ + ‖Q c‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) hβ
    _ ≤ β * (‖d‖ + K * r ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hQc _) hβ
    _ ≤ r := by nlinarith

/-- On the correction ball the iteration has Lipschitz constant at most `1/2`. -/
theorem correctionIteration_sub_le
    (B : E ≃L[ℝ] E) (Q : E → E) (d : E) (β K r : ℝ)
    (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hB : ∀ x, ‖B.symm x‖ ≤ β * ‖x‖)
    (hQ : ∀ x, ‖x‖ ≤ r → ∀ y, ‖y‖ ≤ r →
      ‖Q x - Q y‖ ≤ K * (‖x‖ + ‖y‖) * ‖x - y‖)
    (hsmall : 4 * β * K * r ≤ 1)
    (x y : E) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖correctionIteration B Q d x - correctionIteration B Q d y‖ ≤
      (1 / 2 : ℝ) * ‖x - y‖ := by
  have hsum : ‖x‖ + ‖y‖ ≤ 2 * r := by linarith
  have hcoef : β * (K * (2 * r)) ≤ (1 / 2 : ℝ) := by nlinarith [hsmall]
  calc
    ‖correctionIteration B Q d x - correctionIteration B Q d y‖ =
        ‖B.symm ((d - Q x) - (d - Q y))‖ := by rw [map_sub]; rfl
    _ ≤ β * ‖(d - Q x) - (d - Q y)‖ := hB _
    _ = β * ‖Q x - Q y‖ := by
      rw [sub_sub_sub_cancel_left, norm_sub_rev]
    _ ≤ β * (K * (‖x‖ + ‖y‖) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (hQ x hx y hy) hβ
    _ ≤ β * (K * (2 * r) * ‖x - y‖) := by
      apply mul_le_mul_of_nonneg_left _ hβ
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hK)
        (norm_nonneg _)
    _ = (β * (K * (2 * r))) * ‖x - y‖ := by ring
    _ ≤ (1 / 2 : ℝ) * ‖x - y‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

/--
The existence and local uniqueness part of the manuscript's quadratic moment
adjustment, proved by Banach's fixed-point theorem. The hypotheses are explicit
inverse and quadratic remainder bounds. Smooth dependence on extra parameters
is not asserted.
-/
theorem exists_unique_small_correction [CompleteSpace E]
    (B : E ≃L[ℝ] E) (Q : E → E) (d : E) (β K r : ℝ)
    (hβ : 0 ≤ β) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hB : ∀ x, ‖B.symm x‖ ≤ β * ‖x‖)
    (hQnorm : ∀ x, ‖x‖ ≤ r → ‖Q x‖ ≤ K * ‖x‖ ^ 2)
    (hQdiff : ∀ x, ‖x‖ ≤ r → ∀ y, ‖y‖ ≤ r →
      ‖Q x - Q y‖ ≤ K * (‖x‖ + ‖y‖) * ‖x - y‖)
    (hsmall : 4 * β * K * r ≤ 1) (hd : 2 * β * ‖d‖ ≤ r) :
    ∃! c : E, ‖c‖ ≤ r ∧ B c + Q c = d := by
  let f : E → E := correctionIteration B Q d
  let S : Set E := Metric.closedBall 0 r
  have hmaps : Set.MapsTo f S S := by
    intro c hc
    apply (Metric.mem_closedBall).mpr
    rw [dist_zero_right]
    exact correctionIteration_norm_le B Q d β K r hβ hK hr hB hQnorm hsmall hd c
      (by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hc)
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict f S S) := by
    refine ⟨(div_lt_one (by norm_num : (0 : ℝ≥0) < 2)).mpr (by norm_num),
      LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (f x) (f y) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist (x : E) (y : E)
    simp only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    exact correctionIteration_sub_le B Q d β K r hβ hK hB hQdiff hsmall x y
      (by simpa only [S, Metric.mem_closedBall, dist_zero_right] using x.property)
      (by simpa only [S, Metric.mem_closedBall, dist_zero_right] using y.property)
  have hcomplete : IsComplete S := Metric.isClosed_closedBall.isComplete
  have hzero : (0 : E) ∈ S := by simpa [S] using hr
  obtain ⟨c, hcS, hfix, _, _⟩ :=
    ContractingWith.exists_fixedPoint' hcomplete hmaps hcontract hzero (edist_ne_top 0 (f 0))
  have hc : ‖c‖ ≤ r := by
    simpa only [S, Metric.mem_closedBall, dist_zero_right] using hcS
  have heq : B c + Q c = d := by
    apply eq_sub_iff_add_eq.mp
    have h := congrArg B hfix
    simpa only [f, correctionIteration, ContinuousLinearEquiv.apply_symm_apply] using h.symm
  refine ⟨c, ⟨hc, heq⟩, ?_⟩
  intro y hy
  have hyfix : correctionIteration B Q d y = y := by
    apply B.injective
    change B (B.symm (d - Q y)) = B y
    rw [B.apply_symm_apply]
    exact (eq_sub_iff_add_eq.mpr hy.2).symm
  have hdist := correctionIteration_sub_le B Q d β K r hβ hK hB hQdiff hsmall y c hy.1 hc
  change correctionIteration B Q d c = c at hfix
  rw [hyfix, hfix] at hdist
  have hnorm : ‖y - c‖ = 0 := by nlinarith [norm_nonneg (y - c)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end NonlinearRepair

end NavierStokes.MomentRepair
