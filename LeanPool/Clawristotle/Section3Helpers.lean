/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs
import LeanPool.Clawristotle.Section2
import LeanPool.Clawristotle.GaussianHelpers
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Helper Lemmas for Section 3

Gaussian normalization, gradient of exponential-quadratic functions, Maxwellian
characterization, and derivative bounds used in the nullspace analysis of the
Landau operator.
-/

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

/-- Flux factoring: f(w)∇f(v) - f(v)∇f(w) = f(v)f(w)(∇logf(v) - ∇logf(w)). -/
lemma analysis_fluxFactor
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) :
    ∀ v w, f w • vGrad f v - f v • vGrad f w =
    (f v * f w) • (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w) := by
  -- Proved by Aristotle (Harmonic)
  intro v w
  have h_log_grad : ∀ (v : (Fin 3) → ℝ),
      VML.vGrad (Real.log ∘ f) v = (1 / f v) • VML.vGrad f v := by
    intro v
    ext i
    simp only [VML.vGrad, Pi.smul_apply, smul_eq_mul, one_div]
    by_cases H : DifferentiableAt ℝ f v
    · erw [fderiv_comp] <;> norm_num [H, ne_of_gt (hf_pos v)]
      ring
    · rw [fderiv_zero_of_not_differentiableAt]
      · rw [fderiv_zero_of_not_differentiableAt H]
        norm_num
      · exact fun h => H <| by
          simpa [Real.exp_log (hf_pos _)] using
            h.exp.congr_of_eventuallyEq
            (by filter_upwards [] using fun _ => by simp [Real.exp_log (hf_pos _)])
  simp only [h_log_grad, smul_sub]
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [ne_of_gt (hf_pos v), ne_of_gt (hf_pos w)]

/-- Scalar factors through mulVec and dotProduct:
    y ⬝ (A *ᵥ (c • y)) = c * (y ⬝ (A *ᵥ y)). -/
lemma analysis_scalarFactor
    (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) :
    ∀ v w, dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
      (mulVec (landauMatrix Ψ (v - w))
        ((f v * f w) • (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w))) =
    f v * f w *
      dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)) := fun v w => by
  simp only [dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- Nonneg double integral zero → pointwise zero. -/
lemma analysis_nonneg_dbl_zero
    (g : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
    (hnn : ∀ v w, 0 ≤ g v w)
    (hcont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => g p.1 p.2))
    (hint_inner : ∀ v, Integrable (g v))
    (hint_outer : Integrable (fun v => ∫ w, g v w))
    (hint : (∫ v, ∫ w, g v w) = 0) :
    ∀ v w, g v w = 0 := by
  -- Proved by Aristotle (Harmonic)
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun v => MeasureTheory.integral_nonneg fun w => hnn v w)
    hint_outer] at hint
  have h_zero_ae : ∀ᵐ v ∂MeasureTheory.volume, ∀ w, g v w = 0 := by
    filter_upwards [hint] with v hv w
    contrapose! hv
    simp_all only [Pi.zero_apply, ne_eq]
    rw [MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => hnn v x) (hint_inner v)]
    obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ w', dist w' w < ε → g v w' ≠ 0 :=
      Metric.mem_nhds_iff.mp
        (hcont.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
          |> fun h => h.eventually_ne hv)
        |> fun ⟨ε, εpos, hε⟩ => ⟨ε, εpos, fun w' hw' => hε <| by simpa using hw'⟩
    exact ne_of_gt (lt_of_lt_of_le
      (by simpa using Metric.measure_ball_pos _ _ hε.1)
      (MeasureTheory.measure_mono
        (show { a : Fin 3 → ℝ | ¬g v a = 0 } ⊇ Metric.ball w ε
          from fun x hx => hε.2 x hx)))
  intro v w
  by_contra h_nonzero
  push Not at h_nonzero
  have hU_open : IsOpen { u : Fin 3 → ℝ | g u w ≠ 0 } :=
    isOpen_ne.preimage (hcont.comp (continuous_id.prodMk continuous_const))
  exact absurd h_zero_ae (ne_of_gt (lt_of_lt_of_le
    (hU_open.measure_pos MeasureTheory.MeasureSpace.volume ⟨v, h_nonzero⟩)
    (MeasureTheory.measure_mono fun u hu h => absurd (h w) hu)))

-- ============================================================================
-- Polynomial Extraction Lemmas
--
-- These pure algebra lemmas extract coefficient equations from polynomial
-- identities that hold for all v ∈ ℝ³.
-- ============================================================================

/-- Polynomial cubic extraction: cubic part of a vanishing polynomial vanishes.
    Proved by Aristotle (Harmonic). -/
lemma poly_cubic_extraction
    (d_c : Fin 3 → ℝ) (K : Fin 3 → Fin 3 → ℝ) (d_lin : Fin 3 → ℝ) (C : ℝ)
    (h : ∀ v : Fin 3 → ℝ,
      dotProduct v d_c * normSq v +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j * K i j) +
      dotProduct v d_lin + C = 0) :
    ∀ v : Fin 3 → ℝ, dotProduct v d_c * normSq v = 0 := by
  intro v
  by_contra h_nonzero
  have hv : v ⬝ᵥ d_c * normSq v ≠ 0 := h_nonzero
  have h_poly_zero : ∀ t : ℝ, (t • v) ⬝ᵥ d_c * normSq (t • v) +
      ∑ i, ∑ j, (t • v i) * (t • v j) * (K i j) +
      (t • v) ⬝ᵥ d_lin + C = 0 := fun t => h _
  simp only [smul_dotProduct, smul_eq_mul, normSq, dotProduct_smul] at h_poly_zero
  have h_cubic_zero : ∀ t : ℝ, t^3 * (v ⬝ᵥ d_c * (v ⬝ᵥ v)) +
      t^2 * (∑ i, ∑ j, (v i) * (v j) * (K i j)) +
      t * (v ⬝ᵥ d_lin) + C = 0 := by
    convert h_poly_zero using 2
    ring_nf
    simp [Fin.sum_univ_three]
    ring
  have h_coeff_zero : v ⬝ᵥ d_c * (v ⬝ᵥ v) = 0 := by
    linarith [h_cubic_zero (-2), h_cubic_zero (-1), h_cubic_zero 0,
              h_cubic_zero 1, h_cubic_zero 2]
  exact h_nonzero (by simpa [normSq] using h_coeff_zero)

/-- Polynomial quadratic extraction: Killing equation from vanishing quadratic form.
    Proved by Aristotle (Harmonic). -/
lemma poly_killing_extraction
    (K : Fin 3 → Fin 3 → ℝ)
    (h : ∀ v : Fin 3 → ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j * K i j) = 0) :
    ∀ i j : Fin 3, K i j + K j i = 0 := by
  intros i j
  have h_diff : ∑ k, ∑ l, (if k = i then 1 else 0) * (if l = j then 1 else 0) * K k l +
      ∑ k, ∑ l, (if k = j then 1 else 0) * (if l = i then 1 else 0) * K k l = 0 := by
    convert h (fun x => if x = i then 1 else if x = j then 1 else 0) using 1
    simp [Fin.sum_univ_three]; ring_nf
    fin_cases i <;> fin_cases j <;> simp
    all_goals
      have := h (fun i => if i = 0 then 1 else 0)
      have := h (fun i => if i = 1 then 1 else 0)
      have := h (fun i => if i = 2 then 1 else 0)
      simp_all [Fin.sum_univ_three]
    all_goals ring
  simp_all [Fin.sum_univ_three]

/-- Polynomial linear extraction: coefficients of vanishing linear polynomial vanish.
    Proved by Aristotle (Harmonic). -/
lemma poly_linear_extraction
    (d : Fin 3 → ℝ) (C : ℝ)
    (h : ∀ v : Fin 3 → ℝ, dotProduct v d + C = 0) :
    d = 0 ∧ C = 0 := by
  constructor
  <;> have := h 0
  <;> have := h (fun i => if i = 0 then 1 else 0)
  <;> have := h (fun i => if i = 1 then 1 else 0)
  <;> have := h (fun i => if i = 2 then 1 else 0)
  <;> simp_all only [dotProduct, Fin.sum_univ_three, Fin.isValue, Pi.zero_apply, zero_mul,
        sum_const_zero, zero_add, ite_mul, one_mul, sum_ite_eq', mem_univ, ↓reduceIte, add_zero,
        mul_zero, implies_true]
  exact funext fun i => by fin_cases i <;> assumption

-- ============================================================================
-- Analytical Gap Lemmas (proved using axioms above)
--
-- Each lemma uses standard analytical axioms declared above to bridge
-- the gap between Lean's Mathlib and the required analysis.
-- ============================================================================

/-- Gap 1-3 combined: Score function identity for the entropy dissipation formula.
    D(f) = -(1/2) ∫∫ f(v)f(w) ⟨Δ, A(v-w) Δ⟩ where Δ = ∇log f(v) - ∇log f(w).
    Derived from: IBP (Gap 1) + Fubini+symmetrization (Gap 2) + score substitution (Gap 3).
    Reference: Proof of Lemma 5 (lem:entropy_dissipation). -/
lemma entropy_score_form (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ v, 0 < f v) (_hf_smooth : ContDiff ℝ 3 f)
    (hSWF : ∫ v, LandauOperator Ψ f v * (Real.log ∘ f) v =
      -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w))) :
    entropyDissipation Ψ f =
    -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w := by
  unfold entropyDissipation PSDIntegrand
  simp_rw [show ∀ v, Real.log (f v) = (Real.log ∘ f) v from fun _ => rfl, hSWF,
    analysis_fluxFactor f hf_pos, analysis_scalarFactor]

/-- Gap 4: Non-negativity of the PSD-weighted double integral.
    Since f > 0, Ψ ≥ 0, and Yᵀ A(z) Y ≥ 0 (Lemma 2), the integrand is
    non-negative, so the double integral is non-negative.
    Reference: Step in the proof of Theorem 3 (thm:H_theorem). -/
lemma psd_weighted_integral_nonneg (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 ≤ Ψ r) (hf_pos : ∀ v, 0 < f v) :
    0 ≤ ∫ v, ∫ w, f v * f w *
      dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)) := by
  -- Proved by Aristotle (Harmonic). Integrand is nonneg (f>0, PSD quadratic form).
  exact integral_nonneg fun v => integral_nonneg fun w =>
    mul_nonneg (le_of_lt (mul_pos (hf_pos v) (hf_pos w)))
      (landauMatrix_posSemidef (hΨ (eucNorm (v - w))) _)

/-- Gap 5: D(f) = 0 forces the PSD quadratic form integrand to vanish pointwise.
    From D(f) = 0, the entropy dissipation formula, f > 0, and continuity:
    the non-negative integrand integrates to zero, hence vanishes pointwise.
    Reference: Step in the proof of Lemma 6 (lem:D_zero_functional_eq). -/
lemma entropy_zero_quadform_zero (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (_hf_smooth : ContDiff ℝ 3 f)
    (hD : entropyDissipation Ψ f = 0)
    (hScoreForm : entropyDissipation Ψ f =
      -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w)
    (hPSD_cont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ f p.1 p.2))
    (hPSD_inner : ∀ v, Integrable (PSDIntegrand Ψ f v))
    (hPSD_outer : Integrable (fun v => ∫ w, PSDIntegrand Ψ f v w))
    (v w : Fin 3 → ℝ) :
    dotProduct
      (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
      (mulVec (landauMatrix Ψ (v - w))
        (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)) = 0 := by
  have h_int_zero : ∫ v, ∫ w, PSDIntegrand Ψ f v w = 0 := by linarith [hScoreForm ▸ hD]
  have h_pw := analysis_nonneg_dbl_zero (PSDIntegrand Ψ f) (fun v w =>
    mul_nonneg (le_of_lt (mul_pos (hf_pos v) (hf_pos w)))
      (landauMatrix_posSemidef (le_of_lt (hΨ (eucNorm (v - w)))) _))
    hPSD_cont hPSD_inner hPSD_outer h_int_zero v w
  unfold PSDIntegrand at h_pw
  nlinarith [mul_pos (hf_pos v) (hf_pos w)]


/-- Gap 6: Solution of the functional equation: parallel + curl-free → affine.
    If g(v) - g(w) ∥ (v - w) for all v ≠ w and g is smooth (hence curl-free),
    then g(v) = b + 2c₀ v for constants b, c₀.
    Reference: Proof of Lemma 7 (lem:functional_eq_solution). -/
lemma parallel_curl_free_affine (g : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hg_smooth : ContDiff ℝ 2 g)
    (hparallel : ∀ v w, v ≠ w → ∃ l : ℝ, g v - g w = l • (v - w)) :
    ∃ (b : Fin 3 → ℝ) (c₀ : ℝ), ∀ v, g v = b + (2 * c₀) • v := by
  -- Proved by Aristotle (Harmonic). Full proof in gap06_aristotle.lean.
  -- Step 1: Show fderiv g v = c(v) • id for some scalar function c
  have h_deriv : ∀ v : Fin 3 → ℝ, ∃ c : ℝ, ∀ w : Fin 3 → ℝ, (fderiv ℝ g v) w = c • w := fun v => by
    have h_deriv_eq : ∀ w : Fin 3 → ℝ, (fderiv ℝ g v) w ∈ Submodule.span ℝ {w} := by
      intro w
      have h_deriv_eq : ∀ t : ℝ, g (v + t • w) - g v ∈ Submodule.span ℝ {w} := by
        intro t
        by_cases ht : t = 0 ∨ w = 0 <;>
          simp_all only [ne_eq, not_or, Submodule.mem_span_singleton]
        · exact ⟨0, by rcases ht with rfl | rfl <;> simp⟩
        · obtain ⟨l, hl⟩ := hparallel (v + t • w) v (by simp_all)
          use l * t
          simp_all [mul_comm, smul_smul]
      have h_lim : Filter.Tendsto
          (fun t : ℝ => (1 / t) • (g (v + t • w) - g v))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((fderiv ℝ g v) w)) := by
        have h_lim : HasDerivAt (fun t : ℝ => g (v + t • w)) ((fderiv ℝ g v) w) 0 := by
          have hsmul : HasDerivAt (fun t : ℝ => t • w) w 0 := by
            simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
          have hinner : HasDerivAt (fun t : ℝ => v + t • w) w 0 := hsmul.const_add v
          have hgd : HasFDerivAt g (fderiv ℝ g (v + (0 : ℝ) • w)) (v + (0 : ℝ) • w) :=
            (hg_smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
          have hcomp := hgd.comp_hasDerivAt 0 hinner
          rw [zero_smul, add_zero] at hcomp
          exact hcomp
        simpa [div_eq_inv_mul] using h_lim.tendsto_slope_zero_right
      exact Submodule.closed_of_finiteDimensional _
        |> fun h => h.mem_of_tendsto h_lim <|
          Filter.eventually_of_mem self_mem_nhdsWithin
            fun t ht => Submodule.smul_mem _ _ <|
            h_deriv_eq t
    have h_deriv_scalar : ∀ w : Fin 3 → ℝ, ∃ c : ℝ, (fderiv ℝ g v) w = c • w :=
      fun w => by simpa [eq_comm] using Submodule.mem_span_singleton.mp (h_deriv_eq w)
    choose c hc using h_deriv_scalar
    have h_c_const : ∀ i j : Fin 3, c (Pi.single i 1) = c (Pi.single j 1) := by
      intro i j
      rcases eq_or_ne i j with rfl | hij
      · rfl
      have key := hc (Pi.single i 1 + Pi.single j 1)
      rw [map_add, hc, hc] at key
      have hi := congr_fun key i
      have hj := congr_fun key j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm, mul_one, mul_zero,
        add_zero, zero_add] at hi hj
      linarith [hi, hj]
    use c (Pi.single 0 1)
    intro w
    rw [hc]
    ext i
    simp only [← h_c_const i 0, Pi.smul_apply, smul_eq_mul, Fin.isValue, mul_eq_mul_right_iff]
    have h_c_const : ∀ w : Fin 3 → ℝ,
        (fderiv ℝ g v) w =
        ∑ i, w i • (fderiv ℝ g v) (Pi.single i 1) := by
      intro w
      rw [show w = ∑ i, Pi.single i (w i) by ext i; simp]
      simp [Finset.sum_apply, Pi.single_apply]
      ring_nf
      exact Finset.sum_congr rfl fun i _ => by
        rw [← map_smul]; congr; ext j
        fin_cases i <;> fin_cases j <;> simp
    specialize h_c_const w
    rw [hc] at h_c_const
    simp only [Fin.sum_univ_three, Fin.isValue] at h_c_const
    replace h_c_const := congr_fun h_c_const i
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul,
        hc, Pi.add_apply, Pi.single_eq_same, mul_one, ne_eq, zero_ne_one, one_ne_zero,
        not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, zero_add, Fin.reduceEq]
        at h_c_const ⊢
    all_goals exact Classical.or_iff_not_imp_right.2 fun h => mul_left_cancel₀ h <| by linarith
  -- Step 2: c is constant (via symmetry of second derivatives)
  have h_const_deriv : ∃ c₀ : ℝ, ∀ v : Fin 3 → ℝ, ∀ w : Fin 3 → ℝ, (fderiv ℝ g v) w = c₀ • w := by
    choose c hc using h_deriv
    have h_const_c : ∀ v w : Fin 3 → ℝ, c v = c w := by
      have hc_partial : ∀ v : Fin 3 → ℝ, ∀ i j : Fin 3,
          (fderiv ℝ g v) (Pi.single j 1) i =
          c v * (if i = j then 1 else 0) :=
        fun v i j => by simp only [hc, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      have h_diff_fderiv : ContDiff ℝ 1 (fderiv ℝ g) := hg_smooth.fderiv_right le_rfl
      have h_symm_second_deriv :
          ∀ v : Fin 3 → ℝ, ∀ i j k : Fin 3,
          (fderiv ℝ (fun v => (fderiv ℝ g v) (Pi.single j 1)) v)
            (Pi.single k 1) i =
          (fderiv ℝ (fun v => (fderiv ℝ g v) (Pi.single k 1)) v)
            (Pi.single j 1) i := fun v i j k => by
        rw [fderiv_clm_apply, fderiv_clm_apply]
        · simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
            ContinuousLinearMap.flip_apply]
          apply_rules [ContDiffAt.isSymmSndFDerivAt]
          exacts [hg_smooth.contDiffAt, by norm_num [minSmoothness]]
        · exact h_diff_fderiv.differentiable one_ne_zero v
        · exact differentiableAt_const _
        · exact h_diff_fderiv.differentiable one_ne_zero v
        · exact differentiableAt_const _
      have h_second_deriv : ∀ v : Fin 3 → ℝ,
          ∀ i j k : Fin 3,
          (fderiv ℝ (fun v =>
            (fderiv ℝ g v) (Pi.single j 1)) v)
            (Pi.single k 1) i =
          (fderiv ℝ c v) (Pi.single k 1) *
          (if i = j then 1 else 0) := fun v i j k => by
        have hDiff_comp_j : ∀ i', DifferentiableAt ℝ
            (fun v => (fderiv ℝ g v) (Pi.single j 1) i') v :=
          fun i' => DifferentiableAt.comp v
            (differentiableAt_pi.1
              ((h_diff_fderiv.clm_apply contDiff_const).contDiffAt.differentiableAt one_ne_zero) i')
            differentiableAt_id
        have h_pi_comp : (fderiv ℝ (fun v => (fderiv ℝ g v) (Pi.single j 1)) v)
            (Pi.single k 1) i =
            (fderiv ℝ (fun v => (fderiv ℝ g v) (Pi.single j 1) i) v) (Pi.single k 1) := by
          rw [fderiv_pi hDiff_comp_j]; simp only [ContinuousLinearMap.pi_apply]
        rw [h_pi_comp]
        by_cases hij : i = j
        · subst hij
          simp only [ite_true, mul_one]
          rw [show (fun v => (fderiv ℝ g v) (Pi.single i 1) i) = c from
            funext fun v => by rw [hc_partial]; simp]
        · simp only [hij, ite_false, mul_zero]
          rw [show (fun v => (fderiv ℝ g v) (Pi.single j 1) i) = fun _ => (0:ℝ) from
            funext fun v => by rw [hc_partial]; simp [hij]]
          simp
      have h_zero_deriv : ∀ v : Fin 3 → ℝ, ∀ k : Fin 3, (fderiv ℝ c v) (Pi.single k 1) = 0 := by
        intro v k
        obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ≠ k := by fin_cases k <;> trivial
        specialize h_symm_second_deriv v i i k; simp_all
      have h_const_c : ∀ v : Fin 3 → ℝ, (fderiv ℝ c v) = 0 := by
        intro v; ext w
        have : (fderiv ℝ c v) w = ∑ k : Fin 3, w k • (fderiv ℝ c v) (Pi.single k 1) := by
          conv_lhs => rw [show w = ∑ k, Pi.single k (w k) by ext i; simp]
          simp only [map_sum, smul_eq_mul]
          exact Finset.sum_congr rfl fun i _ => by
            rw [show Pi.single i (w i) = w i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) from
              funext fun j => by simp [Pi.single_apply, smul_eq_mul], map_smul, smul_eq_mul]
        simp [this, h_zero_deriv]
      have h_diff_c : Differentiable ℝ c := by
        have : ContDiff ℝ 1 (fun v => (fderiv ℝ g v) (Pi.single 0 1) 0) :=
          (contDiff_apply ℝ ℝ 0).comp (h_diff_fderiv.clm_apply contDiff_const)
        have heq : c = (fun v => (fderiv ℝ g v) (Pi.single 0 1) 0) := by
          funext v; simp [hc, smul_eq_mul]
        rw [heq]
        exact this.differentiable one_ne_zero
      intro v w; exact is_const_of_fderiv_eq_zero h_diff_c h_const_c v w
    use c 0
    intro v w
    rw [hc, h_const_c v 0]
  -- Step 3: FTC to get g(v) = g(0) + c₀ v
  obtain ⟨c₀, hc₀⟩ := h_const_deriv
  have h_ftc : ∀ v : Fin 3 → ℝ, g v = g 0 + ∫ t in (0 : ℝ)..1, (fderiv ℝ g (t • v)) v := fun v => by
    have h_integral_eq : ∀ a b : ℝ,
        ∫ t in a..b, (fderiv ℝ g (t • v)) v =
        g (b • v) - g (a • v) := fun a b => by
      rw [intervalIntegral.integral_deriv_eq_sub']
      · ext t
        erw [deriv]
        erw [fderiv_comp] <;> norm_num [hg_smooth.contDiffAt.differentiableAt (by norm_num), hc₀]
        rw [deriv_pi] <;> norm_num [Fin.forall_fin_succ]
      · exact fun x hx => DifferentiableAt.comp x
          (hg_smooth.contDiffAt.differentiableAt (by norm_num))
          (differentiableAt_id.smul_const _)
      · exact Continuous.continuousOn (by continuity)
    simp [h_integral_eq]
  use g 0, c₀ / 2
  intro v
  rw [h_ftc v]
  norm_num [hc₀]
  ring_nf

/-- Gap 7: Antiderivative of an affine gradient.
    If ∇h(v) = b + 2c₀ v, then h(v) = h(0) + b · v + c₀|v|².
    Reference: Proof of Lemma 8 (lem:log_f_quadratic). -/
lemma affine_gradient_antiderivative (h : (Fin 3 → ℝ) → ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hh_smooth : ContDiff ℝ 3 h)
    (hgrad : ∀ v, vGrad h v = b + (2 * c₀) • v) :
    ∀ v, h v = h 0 + dotProduct b v + c₀ * normSq v := by
  -- Proved by Aristotle (Harmonic). Full proof in gap07_aristotle.lean.
  have h_deriv : ∀ v : Fin 3 → ℝ, ∀ t : ℝ,
      deriv (fun t => h (t • v)) t =
      (b + 2 * c₀ • (t • v)) ⬝ᵥ v := fun v t => by
    -- For a fixed point `p`, the Fréchet derivative applied to `v` equals `(vGrad h p) ⬝ᵥ v`.
    have hfderiv_dot : ∀ p : Fin 3 → ℝ, fderiv ℝ h p v = (VML.vGrad h p) ⬝ᵥ v := by
      intro p
      unfold VML.vGrad
      have hv_decomp : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
        ext i; simp [Pi.single_apply, Finset.sum_apply, smul_eq_mul]
      conv_lhs => rw [hv_decomp]
      simp only [map_sum, map_smul, smul_eq_mul, dotProduct, mul_comm]
    have h_deriv_def : deriv (fun t => h (t • v)) t = (VML.vGrad h (t • v)) ⬝ᵥ v := by
      -- The line `fun t => t • v` has derivative `v` at every point.
      have hline : HasDerivAt (fun t : ℝ => t • v) v t := by
        simpa using (hasDerivAt_id t).smul_const v
      -- Compose with `h` to obtain the derivative of `fun t => h (t • v)`.
      have hfd : HasFDerivAt h (fderiv ℝ h (t • v)) (t • v) :=
        (hh_smooth.differentiable (by norm_num) (t • v)).hasFDerivAt
      have hcomp := (hfd.comp_hasDerivAt t hline).deriv
      rw [← hfderiv_dot (t • v), ← hcomp]
      rfl
    simp_all [two_mul]
    ring
  intro v
  -- The integrand `deriv (t ↦ h (t • v))` is the affine function
  -- `t ↦ b ⬝ᵥ v + (2 c₀ ‖v‖²) t`.
  have hderiv_eq : deriv (fun t => h (t • v)) = fun t : ℝ => b ⬝ᵥ v + (2 * c₀ * normSq v) * t := by
    funext t
    rw [h_deriv v t]
    simp only [dotProduct, normSq, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
      Pi.mul_apply, Pi.ofNat_apply, smul_eq_mul]
    ring
  have hint : IntervalIntegrable (deriv (fun t => h (t • v))) MeasureTheory.volume 0 1 := by
    rw [hderiv_eq]; exact (by continuity : Continuous _).intervalIntegrable 0 1
  have hFTC : ∫ t in (0 : ℝ)..1, deriv (fun t => h (t • v)) t = h v - h 0 :=
    intervalIntegral.integral_deriv_eq_sub
      (fun t _ => DifferentiableAt.comp t
        (hh_smooth.contDiffAt.differentiableAt (by norm_num))
        (differentiableAt_id.smul_const _))
      hint |>.trans (by simp)
  have hval : ∫ t in (0 : ℝ)..1, deriv (fun t => h (t • v)) t = b ⬝ᵥ v + c₀ * normSq v := by
    rw [intervalIntegral.integral_congr (fun t _ => congrFun hderiv_eq t),
      intervalIntegral.integral_add intervalIntegrable_const
        ((by continuity : Continuous fun t : ℝ => (2 * c₀ * normSq v) * t).intervalIntegrable 0 1),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]; ring
  linarith [hFTC, hval]


end VML
