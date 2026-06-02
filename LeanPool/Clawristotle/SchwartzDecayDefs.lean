/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Theorem42
import LeanPool.Clawristotle.TorusInstance
import LeanPool.Clawristotle.IteratedDerivHelpers

/-!
# Schwartz Decay Definitions and Integrability Helpers

Defines `UniformSchwartzDecay` (uniform-in-x Schwartz-class decay in velocity)
and proves basic integrability lemmas. This is the standard regularity assumption
for kinetic theory used throughout the Coulomb concrete theorem files.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- Uniform C² velocity decay: f(x,·) and its first two velocity derivatives
    decay faster than any polynomial in |v|, uniformly in x ∈ T³.

    This is weaker than Schwartz class (which requires ALL derivatives to decay).
    The proof of the H-theorem only uses derivatives up to order 2. -/
structure UniformSchwartzDecay
    (f : Torus3 → (Fin 3 → ℝ) → ℝ) : Prop where
  /-- Velocity derivatives up to order 2 of f decay faster than any polynomial, uniformly in x -/
  hDecay : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
    ‖iteratedFDeriv ℝ k (f x) v‖ * (1 + ‖v‖) ^ N ≤ C
  /-- Spatial gradients of f also have Schwartz decay in v -/
  hGradDecay : ∀ (N : ℕ) (i : Fin 3), ∃ C > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
    |torusGradX (fun y => f y v) x i| * (1 + ‖v‖) ^ N ≤ C

lemma inverse_poly_integrable (C : ℝ) :
    Integrable (fun (v : Fin 3 → ℝ) => C / (1 + ‖v‖) ^ 4) := by
  -- Proved by Aristotle (job 3a0ec4f6)
  have h_integrable : Integrable (fun v : Fin 3 → ℝ => (1 + ‖v‖)⁻¹ ^ 4) volume := by
    have h_integrable :
        IntegrableOn (fun v : Fin 3 → ℝ => (1 + ‖v‖)⁻¹ ^ 4)
          (Set.univ : Set (Fin 3 → ℝ)) := by
      have hpw : ∀ v : Fin 3 → ℝ, (1 + ‖v‖)⁻¹ ^ 4 ≤ (1 + ‖v‖ ^ 2)⁻¹ ^ 2 := by
        intro v
        rw [inv_pow, inv_pow]
        gcongr
        nlinarith [norm_nonneg v]
      have h_integrable2 :
        IntegrableOn (fun v : Fin 3 → ℝ => (1 + ‖v‖ ^ 2)⁻¹ ^ 2)
            (Set.univ : Set (Fin 3 → ℝ)) := by
        have := @integrable_rpow_neg_one_add_norm_sq
        specialize @this (Fin 3 → ℝ) _ _ _ _ _ (MeasureSpace.volume) _ 4; norm_num at this
        rw [integrableOn_univ]
        convert this using 1
        ext v
        rw [inv_pow]
        rfl
      refine h_integrable2.mono' ?_ ?_
      · exact Measurable.aestronglyMeasurable (by measurability)
      · filter_upwards [] with v
        rw [Real.norm_of_nonneg (by positivity)]
        exact hpw v
    rwa [integrableOn_univ] at h_integrable
  simpa [div_eq_mul_inv] using h_integrable.const_mul C

/-- Schwartz decay implies integrability. -/
lemma _root_.VML.UniformSchwartzDecay.integrable {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hS : UniformSchwartzDecay f) (hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (x : Torus3) : Integrable (f x) := by
  obtain ⟨C, hC_pos, hbound⟩ := hS.hDecay (k := 0) 4 (by omega)
  have hint := inverse_poly_integrable C
  apply hint.mono' (hf_smooth x).continuous.aestronglyMeasurable
  filter_upwards [] with v
  have hb := hbound x v
  simp [iteratedFDeriv_zero_eq_comp] at hb
  -- hb : |f x v| * (1 + ‖v‖) ^ 4 ≤ C
  -- goal : ‖f x v‖ ≤ C / (1 + ‖v‖) ^ 4
  have hv_pos : (0 : ℝ) < (1 + ‖v‖) ^ 4 := by positivity
  rw [Real.norm_eq_abs, le_div_iff₀ hv_pos]
  linarith

/-- Schwartz decay implies integrability with polynomial weight.
    If f(x,·) decays faster than any polynomial, then (1+‖v‖)^M * |f(x,v)| is integrable
    for any M. -/
lemma _root_.VML.UniformSchwartzDecay.integrable_poly_mul {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hS : UniformSchwartzDecay f) (hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (x : Torus3) (M : ℕ) :
    Integrable (fun v => (1 + ‖v‖) ^ M * f x v) := by
  obtain ⟨C, hC_pos, hbound⟩ := hS.hDecay (k := 0) (M + 4) (by omega)
  have hint := inverse_poly_integrable C
  apply hint.mono' ((continuous_const.add continuous_norm).pow M |>.mul
    (hf_smooth x).continuous).aestronglyMeasurable
  filter_upwards [] with v
  have hb := hbound x v
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
    continuousMultilinearCurryFin0_symm_apply, ContinuousMultilinearMap.uncurry0_norm,
    norm_eq_abs] at hb
  have hv_pos : (0 : ℝ) < (1 + ‖v‖) ^ 4 := by positivity
  have hMnn : (0 : ℝ) ≤ (1 + ‖v‖) ^ M := by positivity
  -- `Continuous.mul` produces a `Pi` product; unfold it pointwise before the abs rewrites.
  simp only [Pi.mul_apply, Pi.add_apply, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hMnn]
  rw [le_div_iff₀ hv_pos]
  calc (1 + ‖v‖) ^ M * |f x v| * (1 + ‖v‖) ^ 4
      = |f x v| * ((1 + ‖v‖) ^ M * (1 + ‖v‖) ^ 4) := by ring
    _ = |f x v| * (1 + ‖v‖) ^ (M + 4) := by rw [pow_add]
    _ ≤ C := hb


/-- If ‖v‖^k * |φ(v)| is integrable for every k, then (1+‖v‖)^K * |φ(v)| is too.
    Uses the binomial theorem to expand (1+‖v‖)^K as a finite sum.
    Generalized to any normed space (dimension-independent). -/
lemma integrable_one_add_norm_pow_mul
    {α : Type*} [MeasureSpace α] [SeminormedAddCommGroup α]
    {φ : α → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    (K : ℕ) :
    Integrable (fun v => (1 + ‖v‖) ^ K * |φ v|) := by
  have h_binom : ∀ v : α, (1 + ‖v‖) ^ K * |φ v| =
      ∑ k ∈ Finset.range (K + 1), Nat.choose K k * ‖v‖ ^ k * |φ v| := by
    simp [add_comm (1 : ℝ), add_pow, mul_comm,
      Finset.mul_sum _ _ _]
  simp_rw [h_binom]
  exact MeasureTheory.integrable_finsetSum _ fun k _ => by
    simpa only [mul_assoc] using MeasureTheory.Integrable.const_mul (hφ k) _

/-- If ‖v‖^k * |φ(v)| is integrable for every k, and ‖g(v)‖ ≤ C*(1+‖v‖)^K*|φ(v)|,
    then g is integrable. Core tool for Schwartz-dominance arguments.
    Generalized to any normed space (dimension-independent). -/
lemma integrable_of_schwartz_bound
    {α : Type*} [MeasureSpace α] [SeminormedAddCommGroup α]
    {φ : α → ℝ}
    (hφ : ∀ k : ℕ, Integrable (fun v => ‖v‖ ^ k * |φ v|))
    {g : α → ℝ}
    (hg_meas : AEStronglyMeasurable g)
    {C : ℝ} (_ : 0 ≤ C) {K : ℕ}
    (hbound : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ K * |φ v|) :
    Integrable g := by
  have hdom : Integrable (fun v => C * ((1 + ‖v‖) ^ K * |φ v|)) :=
    (integrable_one_add_norm_pow_mul hφ K).const_mul C
  exact hdom.mono' hg_meas (by
    filter_upwards with v
    calc ‖g v‖ ≤ C * (1 + ‖v‖) ^ K * |φ v| := hbound v
    _ = C * ((1 + ‖v‖) ^ K * |φ v|) := by ring)

/-- Extract pointwise (k=0) decay from the Schwartz hypothesis.
    Generalized to any normed space (dimension-independent). -/
lemma schwartz_pointwise_decay
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {f : α → ℝ}
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C) :
    ∀ N, ∃ C > 0, ∀ w, |f w| * (1 + ‖w‖) ^ N ≤ C :=
  fun N => (hf_schwartz (k := 0) N (by omega)).imp fun C ⟨hC, hb⟩ =>
    ⟨hC, fun w => by simpa [iteratedFDeriv_zero_eq_comp] using hb w⟩

/-- Extract partial derivative (k=1) decay from the Schwartz hypothesis.
    Generalized to Fin n → ℝ (dimension-independent). -/
lemma schwartz_fderiv_component_decay
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C) :
    ∀ (j : Fin n) (N : ℕ), ∃ C > 0, ∀ w,
      |fderiv ℝ f w (Pi.single j 1)| * (1 + ‖w‖) ^ N ≤ C := by
  intro j N; obtain ⟨C, hC, hb⟩ := hf_schwartz (k := 1) N (by omega)
  refine ⟨C, hC, fun w => le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) (hb w)⟩
  rw [← Real.norm_eq_abs]
  exact le_trans (le_trans (ContinuousLinearMap.le_opNorm _ _)
    (mul_le_of_le_one_right (norm_nonneg _) (by simp [Pi.norm_single])))
    (by rw [norm_fderiv_eq_iteratedFDeriv_one])

/-- Score bound: |∂_i log f(u)| ≤ Cg * (1+‖u‖)^Kg from the gradient bound on f.
    Uses chain rule: ∂_i(log∘f) = (∂_if)/f, combined with |∂_if| ≤ Cg*(1+‖u‖)^Kg*f. -/
lemma score_bound_of_grad_bound
    {f : (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f)
    {Cg : ℝ} {Kg : ℕ}
    (hGrad : ∀ v i, |fderiv ℝ f v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f v) :
    ∀ u i, |vGrad (Real.log ∘ f) u i| ≤ Cg * (1 + ‖u‖) ^ Kg := by
  intro u i; simp only [vGrad]
  have hfu := hf_pos u
  rw [show Real.log ∘ f = fun u => Real.log (f u) from rfl,
      fderiv.log (hf_smooth.differentiable (by norm_num)).differentiableAt (ne_of_gt hfu)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr hfu)]
  rw [inv_mul_le_iff₀ hfu]; linarith [hGrad u i]

/-- Polynomial-weighted Schwartz decay: if |f(w)|*(1+‖w‖)^N ≤ C for all N,
    then |(1+‖w‖)^M * f(w)| * (1+‖w‖)^N ≤ C' for all N.
    Generalized to any normed space (dimension-independent). -/
lemma schwartz_poly_weighted_decay
    {α : Type*} [SeminormedAddCommGroup α]
    {f : α → ℝ}
    (hf_decay : ∀ N, ∃ C > 0, ∀ w, |f w| * (1 + ‖w‖) ^ N ≤ C)
    (M : ℕ) :
    ∀ N, ∃ C > 0, ∀ w, |(1 + ‖w‖) ^ M * f w| * (1 + ‖w‖) ^ N ≤ C := by
  intro N; obtain ⟨C, hC, hb⟩ := hf_decay (M + N)
  exact ⟨C, hC, fun w => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith [norm_nonneg w]) _)]
    calc (1 + ‖w‖) ^ M * |f w| * (1 + ‖w‖) ^ N
        = |f w| * (1 + ‖w‖) ^ (M + N) := by rw [pow_add]; ring
      _ ≤ C := hb w⟩

/-- Polynomial-weighted Schwartz functions are integrable (on ℝ³).
    If f has Schwartz decay and f > 0, then `(1+‖v‖)^K * f(v)` is integrable. -/
lemma schwartz_poly_mul_integrable
    {f : (Fin 3 → ℝ) → ℝ} (hf_pos : ∀ v, 0 < f v)
    (hf_cont : Continuous f)
    (hf_decay : ∀ N : ℕ, ∃ C > 0, ∀ v, |f v| * (1 + ‖v‖) ^ N ≤ C)
    (K : ℕ) :
    Integrable (fun v => (1 + ‖v‖) ^ K * f v) := by
  obtain ⟨C, _, hbound⟩ := hf_decay (K + 4)
  apply (inverse_poly_integrable C).mono'
  · exact ((continuous_const.add continuous_norm).pow _ |>.mul hf_cont).aestronglyMeasurable
  · filter_upwards with v
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg (by linarith [norm_nonneg v]) K),
      abs_of_pos (hf_pos v),
      le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖v‖) ^ 4)]
    calc (1 + ‖v‖) ^ K * f v * (1 + ‖v‖) ^ 4
        = f v * ((1 + ‖v‖) ^ K * (1 + ‖v‖) ^ 4) := by ring
      _ = f v * (1 + ‖v‖) ^ (K + 4) := by rw [pow_add]
      _ = |f v| * (1 + ‖v‖) ^ (K + 4) := by rw [abs_of_pos (hf_pos v)]
      _ ≤ C := hbound v

end VML
