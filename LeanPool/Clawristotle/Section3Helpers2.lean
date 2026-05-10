/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Section3Helpers

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- Gap 8: For a log-quadratic f = exp(a₀ + b·v + c₀|v|²), the Landau flux vanishes.
    This follows because ∇log f(v) - ∇log f(w) = 2c₀(v-w), so the flux is
    proportional to A(v-w)(v-w) = 0 by Lemma 3 (projection annihilation).
    Reference: Key step in the proof of Theorem 5 (thm:nullspace_sufficiency). -/
lemma maxwellian_landau_flux_zero (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hf : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)) :
    ∀ v w, mulVec (landauMatrix Ψ (v - w))
      (f w • vGrad f v - f v • vGrad f w) = 0 := by
  -- Proved by Aristotle (Harmonic). Full proof in gap08_aristotle.lean.
  -- Key: ∇f(v) = f(v)·(b + 2c₀v), so flux ∝ A(v-w)(v-w) = 0
  have h_grad : ∀ v : Fin 3 → ℝ, VML.vGrad f v = f v • (b + 2 * c₀ • v) := by
    unfold VML.vGrad
    rw [show f = _ from funext hf]
    intro v
    ext i
    rw [fderiv_exp]
    · norm_num [dotProduct, Fin.sum_univ_three]
      ring_nf
      unfold VML.normSq
      norm_num [Fin.sum_univ_three, dotProduct]
      ring_nf
      erw [HasFDerivAt.fderiv
        (HasFDerivAt.add
          (HasFDerivAt.add
            (HasFDerivAt.add
              (HasFDerivAt.add
                (HasFDerivAt.add
                  (HasFDerivAt.add
                    (hasFDerivAt_const _ _)
                    (HasFDerivAt.mul
                      (hasFDerivAt_const _ _)
                      (hasFDerivAt_apply _ _)))
                  (HasFDerivAt.mul
                    (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2)
                    (hasFDerivAt_const _ _)))
                (HasFDerivAt.mul
                  (hasFDerivAt_const _ _)
                  (hasFDerivAt_apply _ _)))
              (HasFDerivAt.mul
                (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2)
                (hasFDerivAt_const _ _)))
            (HasFDerivAt.mul
              (hasFDerivAt_const _ _)
              (hasFDerivAt_apply _ _)))
          (HasFDerivAt.mul
            (hasFDerivAt_apply _ _ |> HasFDerivAt.pow <| 2)
            (hasFDerivAt_const _ _)))]
      norm_num
      ring_nf
      fin_cases i <;> norm_num <;> ring_nf!
      · simp
      · simp
      · simp
    · apply_rules [DifferentiableAt.add,
        DifferentiableAt.mul, differentiableAt_id,
        differentiableAt_const]
      all_goals apply_rules [differentiableAt_pi.1, differentiableAt_id]
  intros v w
  simp only [h_grad, Algebra.mul_smul_comm, smul_add]
  convert congr_arg
    (fun x : Fin 3 → ℝ =>
      f w • f v • c₀ • (2 : ℝ) • x)
    (landauMatrix_mulVec_self Ψ (v - w)) using 1
  · ext
    norm_num
    ring_nf!
    simp [mul_assoc, mul_comm, mul_left_comm,
      Finset.mul_sum _ _ _, Matrix.mulVec, dotProduct]
    ring_nf!
  · norm_num [Algebra.smul_def]

/-- Maxwellians are in the nullspace of the Landau operator: Q(f,f) = 0.
    The flux A(v-w)[f(w)∇f(v) - f(v)∇f(w)] vanishes pointwise (because
    ∇log f is affine, so the score difference is proportional to v-w,
    which is annihilated by A(v-w)), making the integral and its divergence zero. -/
lemma _root_.VML.IsMaxwellian.landauOperator_eq_zero (Ψ : ℝ → ℝ)
    (hM : IsMaxwellian f) (v : Fin 3 → ℝ) :
    LandauOperator Ψ f v = 0 := by
  obtain ⟨a₀, b, c₀, _, hf⟩ := hM
  have hflux := maxwellian_landau_flux_zero Ψ f a₀ b c₀ hf
  unfold LandauOperator
  simp only [hflux, MeasureTheory.integral_zero]
  simp [vDiv]

/-- Gap 11: D(f) = 0 implies f is a Maxwellian.
    Chains: D=0 → parallelism (Lemma 6) → ∇log f affine (Lemma 7) →
    log f quadratic (Lemma 8) → f = exp(quadratic) → c₀ < 0 (L¹ integrability).
    Reference: Proof of Theorem 4 (thm:nullspace_necessity) + Corollary 2. -/
lemma D_zero_implies_maxwellian (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ 3 f) (hf_int : Integrable f)
    (hD : entropyDissipation Ψ f = 0)
    -- Analytical interface (from IBP + Fubini + score + integrability)
    (hScoreForm : entropyDissipation Ψ f =
      -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w)
    (hPSD_cont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ f p.1 p.2))
    (hPSD_inner : ∀ v, Integrable (PSDIntegrand Ψ f v))
    (hPSD_outer : Integrable (fun v => ∫ w, PSDIntegrand Ψ f v w)) :
    IsMaxwellian f := by
  -- Chain: D=0 → quadform=0 → parallel → affine → quadratic → Maxwellian
  have hlog_smooth := hf_smooth.log (fun v => ne_of_gt (hf_pos v))
  -- Step 1: D=0 → parallelism (via gap 5 + PSD equality case)
  have hpar : ∀ v w, v ≠ w →
      ∃ l : ℝ, vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w = l • (v - w) :=
    fun v w hvw => landauMatrix_quadForm_eq_zero_iff
      (hΨ (eucNorm (v - w))) (sub_ne_zero.mpr hvw) _
      (entropy_zero_quadform_zero Ψ f hΨ hf_pos hf_smooth hD
        hScoreForm hPSD_cont hPSD_inner hPSD_outer v w)
  -- Step 2: parallel → affine (gap 6)
  -- vGrad (log ∘ f) is smooth (each component is fderiv applied to a smooth function)
  have hvGrad_smooth : ContDiff ℝ 2 (fun v => vGrad (Real.log ∘ f) v) :=
    analysis_vGrad_smooth _ hlog_smooth
  obtain ⟨b, c₀, haffine⟩ := parallel_curl_free_affine _ hvGrad_smooth hpar
  -- Step 3: affine gradient → quadratic (gap 7)
  have hquad := affine_gradient_antiderivative (Real.log ∘ f) b c₀ hlog_smooth haffine
  -- Step 4: f = exp(quadratic)
  set a₀ := Real.log (f 0) with ha₀
  have hf_exp : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v) := by
    intro v
    rw [← Real.exp_log (hf_pos v)]
    congr 1
    have := hquad v
    simp only [Function.comp] at this
    exact this
  -- Step 5: c₀ < 0 from the form of f
  exact ⟨a₀, b, c₀, analysis_gaussian_integrability f a₀ b c₀ hf_pos hf_int hf_exp, hf_exp⟩

end VML
