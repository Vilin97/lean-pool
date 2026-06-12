/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # MainTheorem.lean
  Assembly of the main Fock-space coercivity theorem.
  Scaffolding notes: Assembly/main_theorem.md

  Dependencies: AnnulusLocalEstimate, LeakageEstimate, LipschitzRho, Definitions

  Public API:
  - `fock_space_coercivity` (Theorem 7.1)
-/
import LeanPool.PhaseRetrieval.Constant.Internal.AnnulusLocalEstimate
import LeanPool.PhaseRetrieval.Constant.Internal.LeakageEstimate
import LeanPool.PhaseRetrieval.Constant.Internal.LipschitzRho
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # MainTheorem -/


open MeasureTheory Complex Real Finset Polynomial

noncomputable section

namespace FockSPR

/-! ## Private Lemma 7.1a: `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` -/
-- to_mathlib: Mathlib.Analysis.InnerProductSpace.Basic
private lemma norm_add_sq_le (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := parallelogram_law_with_norm ℂ a b
  nlinarith [sq_abs (‖a + b‖), sq_abs (‖a - b‖), sq_abs (‖a‖), sq_abs (‖b‖)]

/-! ## Private Lemma 7.1b: Numerical absorption check -/
private lemma absorption_check :
    (4 * 1620 ^ 2 + 2) * (4 / (10 : ℝ) ^ 11) < 1 / 2 := by norm_num

/-! ## Private Lemma 7.1c: Final constant check -/
private lemma final_constant_check : 8 * 1620 ^ 2 ≤ 4600 ^ 2 := by norm_num

/-! ## Helper lemmas -/

private lemma fockNormSq_nonneg {D : ℕ} (a : Fin D → ℂ) : 0 ≤ fockNormSq a := by
  unfold fockNormSq; apply Finset.sum_nonneg; intro k _
  exact mul_nonneg (sq_nonneg _) (by exact_mod_cast Nat.zero_le _)

private lemma rhoFockNormSq_nonneg {D : ℕ} (a : Fin D → ℂ) : 0 ≤ rhoFockNormSq a := by
  unfold rhoFockNormSq; apply mul_nonneg; · positivity
  · exact integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _)))

private lemma etaCoeff_nonneg (M J : ℕ) : 0 ≤ etaCoeff M J := by
  unfold etaCoeff; apply mul_nonneg
  · exact mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _))
  · exact Finset.sum_nonneg (fun m _ => le_of_lt (Real.exp_pos _))

private lemma absorption_lemma {x y c η : ℝ} (hx : 0 ≤ x)
    (hη : η < 1 / 2) (h : x ≤ c * y + η * x) :
    x ≤ 2 * c * y := by nlinarith

/-! ## Auxiliary lemmas for polar decomposition -/

private lemma filter_cast_eq_singleton {D : ℕ} (k : Fin D) :
    (Finset.univ : Finset (Fin D)).filter
      (fun j => ((j.val + 1 : ℕ) : ℤ) = ((k.val + 1 : ℕ) : ℤ)) = {k} := by
  ext j; constructor
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    intro h; ext; omega
  · simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h; rw [h]

private lemma integrable_pow_mul_exp_neg_sq (n : ℕ) :
    Integrable (fun r : ℝ => r ^ n * Real.exp (-r ^ 2)) volume := by
  have hs : (-1 : ℝ) < (n : ℝ) := by exact_mod_cast (show -1 < (n : ℤ) by omega)
  have h := integrable_rpow_mul_exp_neg_mul_sq one_pos hs
  refine h.congr ?_; filter_upwards with r; rw [rpow_natCast]; ring_nf

private lemma radial_gaussian_integral (n : ℕ) :
    2 * ∫ r in Set.Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-r ^ 2) =
    (n.factorial : ℝ) := by
  have hp : (0 : ℝ) < 2 := two_pos
  have hq : (-1 : ℝ) < (2 * (n : ℝ) + 1) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have pow_eq : ∀ (r : ℝ), r ∈ Set.Ioi (0 : ℝ) →
      r ^ (2 * n + 1) * Real.exp (-r ^ 2) =
      r ^ (2 * (n : ℝ) + 1) * Real.exp (-r ^ (2 : ℝ)) := by
    intro r _; congr 1
    · rw [← rpow_natCast r (2 * n + 1)]; congr 1; push_cast; ring
    · congr 1; congr 1; rw [← rpow_natCast r 2]; norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi pow_eq]
  rw [integral_rpow_mul_exp_neg_rpow hp hq]
  have h1 : (2 * (n : ℝ) + 1 + 1) / 2 = ↑n + 1 := by ring
  rw [h1, Real.Gamma_nat_eq_factorial]; ring

/-! ## Parseval identity on circles -/
private lemma circleNormSq_polyEvalCircle {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle =
    ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) := by
  let E' := (Finset.univ : Finset (Fin D)).map
    ⟨fun k => ((k.val + 1 : ℕ) : ℤ), fun k₁ k₂ h => by
      simp only at h; exact Fin.ext (by omega)⟩
  let b : ℤ → ℂ := fun n => ∑ k ∈ (Finset.univ : Finset (Fin D)).filter
    (fun k => ((k.val + 1 : ℕ) : ℤ) = n), a k * (r : ℂ) ^ (k.val + 1)
  have hb_eq : ∀ k : Fin D,
      b ((k.val + 1 : ℕ) : ℤ) = a k * (r : ℂ) ^ (k.val + 1) := by
    intro k; simp only [b]
    rw [filter_cast_eq_singleton, Finset.sum_singleton]
  let Pcont : C(AddCircle T, ℂ) := ∑ k : Fin D,
    (a k * (r : ℂ) ^ (k.val + 1)) • fourier ((k.val + 1 : ℕ) : ℤ)
  have hPcont_eq : ∀ t : AddCircle T, (Pcont : AddCircle T → ℂ) t =
      polyEvalCircle a r t := by
    intro t; simp only [Pcont, polyEvalCircle, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  let PLp := (ContinuousMap.toLp (α := AddCircle T) 2 AddCircle.haarAddCircle ℂ) Pcont
  have hPLp' : PLp = ∑ n ∈ E', b n • fourierLp 2 n := by
    simp only [PLp, Pcont, fourierLp, map_sum, map_smul, E', b]
    rw [Finset.sum_map]; congr 1; ext k
    simp only [Function.Embedding.coeFn_mk]
    rw [filter_cast_eq_singleton, Finset.sum_singleton]
  have hinner_orth : @inner ℂ _ _ PLp PLp =
      Complex.ofReal (∑ k : Fin D, ‖a k * (r : ℂ) ^ (k.val + 1)‖ ^ 2) := by
    rw [hPLp', orthonormal_fourier.inner_sum b b E']
    rw [show E' = (Finset.univ : Finset (Fin D)).map
      ⟨fun k => ((k.val + 1 : ℕ) : ℤ), fun k₁ k₂ h => by
        simp only at h; exact Fin.ext (by omega)⟩ from rfl]
    rw [Finset.sum_map, Complex.ofReal_sum]; congr 1; ext k
    simp only [Function.Embedding.coeFn_mk]
    rw [hb_eq k, mul_comm (starRingEnd ℂ _), mul_conj]
    congr 1; exact (Complex.sq_norm _).symm
  have hnorm_eq : ∀ k : Fin D,
      ‖a k * (r : ℂ) ^ (k.val + 1)‖ ^ 2 = ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) := by
    intro k; rw [norm_mul, norm_pow, Complex.norm_real, mul_pow]
    congr 1; rw [← pow_mul, show (k.val + 1) * 2 = 2 * (k.val + 1) from by ring,
        pow_mul, Real.norm_eq_abs, sq_abs]
  simp_rw [hnorm_eq] at hinner_orth
  have hcombine := (L2.inner_def (𝕜 := ℂ) PLp PLp).symm.trans hinner_orth
  have hae := ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) (p := 2) Pcont
  calc ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle
      = ∫ t, ‖(↑↑PLp : AddCircle T → ℂ) t‖ ^ 2 ∂AddCircle.haarAddCircle := by
          symm; apply integral_congr_ae; filter_upwards [hae] with t ht
          rw [show (↑↑PLp : AddCircle T → ℂ) t = Pcont t from ht, hPcont_eq t]
    _ = (∫ t, @inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
            ((↑↑PLp : AddCircle T → ℂ) t) ∂AddCircle.haarAddCircle).re := by
          have hint := L2.integrable_inner (𝕜 := ℂ) PLp PLp; symm
          calc _ = Complex.reCLM (∫ t, @inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
                ((↑↑PLp : AddCircle T → ℂ) t) ∂AddCircle.haarAddCircle) := rfl
            _ = ∫ t, Complex.reCLM (@inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
                ((↑↑PLp : AddCircle T → ℂ) t)) ∂AddCircle.haarAddCircle :=
                (ContinuousLinearMap.integral_comp_comm _ hint).symm
            _ = _ := by congr 1; ext t
                        exact @inner_self_eq_norm_sq ℂ ℂ _ _ _ _
    _ = ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) := by
          rw [show (∫ t : AddCircle T, @inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
              ((↑↑PLp : AddCircle T → ℂ) t) ∂AddCircle.haarAddCircle) =
              Complex.ofReal (∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1))
              from hcombine, Complex.ofReal_re]

/-! ## Polar decomposition of fockNormSq -/
private lemma fockNormSq_polar {D : ℕ} (a : Fin D → ℂ) :
    fockNormSq a = 2 * ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
        ∂AddCircle.haarAddCircle) := by
  simp_rw [circleNormSq_polyEvalCircle a]
  have integrand_eq : ∀ r : ℝ,
      r * Real.exp (-r ^ 2) * ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) =
      ∑ k : Fin D, ‖a k‖ ^ 2 *
        (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) := by
    intro r; rw [Finset.mul_sum]; congr 1; ext k
    have : (r ^ 2) ^ (k.val + 1) = r ^ (2 * (k.val + 1)) := by rw [← pow_mul]
    rw [this]; ring
  simp_rw [integrand_eq]
  have hint_summand : ∀ k : Fin D,
      IntegrableOn (fun r => ‖a k‖ ^ 2 *
        (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)))
        (Set.Ioi 0) volume := by
    intro k
    exact (integrable_pow_mul_exp_neg_sq (2 * (k.val + 1) + 1)).integrableOn
      |>.const_mul _
  rw [integral_finsetSum Finset.univ (fun k _ => (hint_summand k).integrable)]
  simp_rw [MeasureTheory.integral_const_mul]
  rw [Finset.mul_sum]; simp only [fockNormSq]; congr 1; ext k
  rw [← mul_assoc, mul_comm 2, mul_assoc, radial_gaussian_integral (k.val + 1)]

/-! ## Helper: `polyEvalCircle = polyEval` on the circle -/

-- to_mathlib: Mathlib.Analysis.Fourier.AddCircle
private lemma fourier_pow_eq (n : ℕ) (t : AddCircle T) :
    ((fourier 1 t : ℂ)) ^ n = (fourier (↑n : ℤ) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← fourier_add]; push_cast; ring_nf

private lemma polyEvalCircle_eq_polyEval {D : ℕ} (a : Fin D → ℂ)
    (r : ℝ) (t : AddCircle T) :
    polyEvalCircle a r t = polyEval a (↑r * (fourier 1 t : ℂ)) := by
  simp only [polyEvalCircle, polyEval]
  congr 1; ext k
  rw [mul_pow, ← fourier_pow_eq]; ring

/-- `polyEval = localPoly + remainderPoly` by definition. -/
private lemma polyEval_decompose {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) (z : ℂ) :
    polyEval a z = localPoly a M j z + remainderPoly a M j z := by
  simp [remainderPoly]

/-! ## Helper: real `norm_add_sq_le` for the `ρ` squaring step -/

private lemma real_add_sq_le (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]

/-! ## Continuity and integrability helpers -/

private lemma cont_integrable_circle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AddCircle T → E} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma continuous_polyEvalCircle {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    Continuous (polyEvalCircle a r) := by
  unfold polyEvalCircle
  apply continuous_finsetSum; intro k _
  exact continuous_const.mul (fourier _).continuous

private lemma continuous_mul_fourier_pow (r : ℝ) (n : ℕ) :
    Continuous (fun t : AddCircle T => ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ n) := by
  exact ((continuous_const.mul (fourier 1).continuous).pow n)

private lemma continuous_localPoly_circle {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) (r : ℝ) :
    Continuous (fun t : AddCircle T => localPoly a M j (↑r * (fourier 1 t : ℂ))) := by
  unfold localPoly blockPoly
  apply continuous_finsetSum; intro ℓ _
  apply continuous_finsetSum; intro k _
  by_cases h : (k.val + 1) ∈ freqBlock ℓ
  · simp only [h, ite_true]
    exact continuous_const.mul (continuous_mul_fourier_pow r (k.val + 1))
  · simp only [h, ite_false]; exact continuous_const

private lemma continuous_remainderPoly_circle {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) (r : ℝ) :
    Continuous (fun t : AddCircle T => remainderPoly a M j (↑r * (fourier 1 t : ℂ))) := by
  change Continuous (fun t => polyEval a (↑r * (fourier 1 t : ℂ)) -
    localPoly a M j (↑r * (fourier 1 t : ℂ)))
  have h1 : Continuous (fun t : AddCircle T => polyEval a (↑r * (fourier 1 t : ℂ))) := by
    unfold polyEval
    apply continuous_finsetSum; intro k _
    exact continuous_const.mul (continuous_mul_fourier_pow r (k.val + 1))
  exact h1.sub (continuous_localPoly_circle a M j r)

private lemma integrable_sq_of_continuous {f : AddCircle T → ℂ} (hf : Continuous f) :
    Integrable (fun t => ‖f t‖ ^ 2) AddCircle.haarAddCircle :=
  cont_integrable_circle ((hf.norm).pow 2)

private lemma continuous_rho : Continuous (rho : ℂ → ℝ) := by
  unfold rho
  exact continuous_abs.comp (continuous_norm.comp (continuous_const.add continuous_id) |>.sub
    continuous_const)

private lemma integrable_rho_sq_of_continuous {f : AddCircle T → ℂ} (hf : Continuous f) :
    Integrable (fun t => (rho (f t)) ^ 2) AddCircle.haarAddCircle :=
  cont_integrable_circle ((continuous_rho.comp hf).pow 2)

/-! ## Step 1: Circle-level pointwise bound -/
private lemma circle_level_bound {D : ℕ} (hD : 1 ≤ D) (a : Fin D → ℂ)
    (j : ℕ) {r : ℝ} (hr_nn : 0 ≤ r) (hr_lo : (j : ℝ) ≤ r) (hr_hi : r ≤ (j : ℝ) + 1) :
    ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle ≤
      4 * 1620 ^ 2 *
        (∫ t : AddCircle T, (rho (polyEvalCircle a r t)) ^ 2
          ∂AddCircle.haarAddCircle) +
      (4 * 1620 ^ 2 + 2) *
        (∫ t : AddCircle T,
          ‖remainderPoly a 5 j (↑r * (fourier 1 t : ℂ))‖ ^ 2
          ∂AddCircle.haarAddCircle) := by
  set V := fun t : AddCircle T => localPoly a 5 j (↑r * (fourier 1 t : ℂ))
  set R := fun t : AddCircle T => remainderPoly a 5 j (↑r * (fourier 1 t : ℂ))
  set U := polyEvalCircle a r
  have hcV : Continuous V := continuous_localPoly_circle a 5 j r
  have hcR : Continuous R := continuous_remainderPoly_circle a 5 j r
  have hcU : Continuous U := continuous_polyEvalCircle a r
  have hU_eq : ∀ t, U t = V t + R t := by
    intro t; simp only [U, V, R]
    rw [polyEvalCircle_eq_polyEval, polyEval_decompose]
  have hiV : Integrable (fun t => ‖V t‖ ^ 2) AddCircle.haarAddCircle :=
    integrable_sq_of_continuous hcV
  have hiR : Integrable (fun t => ‖R t‖ ^ 2) AddCircle.haarAddCircle :=
    integrable_sq_of_continuous hcR
  have hiU : Integrable (fun t => ‖U t‖ ^ 2) AddCircle.haarAddCircle :=
    integrable_sq_of_continuous hcU
  have hiRhoV : Integrable (fun t => (rho (V t)) ^ 2) AddCircle.haarAddCircle :=
    integrable_rho_sq_of_continuous hcV
  have hiRhoU : Integrable (fun t => (rho (U t)) ^ 2) AddCircle.haarAddCircle :=
    integrable_rho_sq_of_continuous hcU
  have hiVR_add : Integrable (fun t => 2 * ‖V t‖ ^ 2 + 2 * ‖R t‖ ^ 2)
      AddCircle.haarAddCircle :=
    cont_integrable_circle (((hcV.norm.pow 2).const_mul 2).add ((hcR.norm.pow 2).const_mul 2))
  have hiRhoUR_add : Integrable (fun t => 2 * (rho (U t)) ^ 2 + 2 * ‖R t‖ ^ 2)
      AddCircle.haarAddCircle :=
    cont_integrable_circle ((((continuous_rho.comp hcU).pow 2).const_mul 2).add
      ((hcR.norm.pow 2).const_mul 2))
  have h_pw : ∀ t, ‖U t‖ ^ 2 ≤ 2 * ‖V t‖ ^ 2 + 2 * ‖R t‖ ^ 2 := by
    intro t; rw [hU_eq]; exact norm_add_sq_le (V t) (R t)
  have h_norm_add : ∫ t, ‖U t‖ ^ 2 ∂AddCircle.haarAddCircle ≤
      2 * ∫ t, ‖V t‖ ^ 2 ∂AddCircle.haarAddCircle +
      2 * ∫ t, ‖R t‖ ^ 2 ∂AddCircle.haarAddCircle := by
    have h1 := integral_mono hiU hiVR_add h_pw
    have h2 : ∫ t, (2 * ‖V t‖ ^ 2 + 2 * ‖R t‖ ^ 2) ∂AddCircle.haarAddCircle =
        2 * ∫ t, ‖V t‖ ^ 2 ∂AddCircle.haarAddCircle +
        2 * ∫ t, ‖R t‖ ^ 2 ∂AddCircle.haarAddCircle := by
      rw [show (fun t => 2 * ‖V t‖ ^ 2 + 2 * ‖R t‖ ^ 2) =
        (fun t => (2 : ℝ) * (fun t => ‖V t‖ ^ 2) t + (2 : ℝ) * (fun t => ‖R t‖ ^ 2) t)
        from rfl]
      rw [integral_add (hiV.const_mul _) (hiR.const_mul _),
          integral_const_mul, integral_const_mul]
    linarith
  have h_annulus := annulus_local_estimate hD a j hr_nn hr_lo hr_hi
  have h_rho_pw : ∀ t, (rho (V t)) ^ 2 ≤
      2 * (rho (U t)) ^ 2 + 2 * ‖R t‖ ^ 2 := by
    intro t
    have h_VU : V t - U t = -(R t) := by
      simp only [V, R, U]; rw [polyEvalCircle_eq_polyEval]
      simp [remainderPoly]
    have h_lip : rho (V t) ≤ rho (U t) + ‖R t‖ := by
      calc rho (V t) ≤ rho (U t) + ‖V t - U t‖ := rho_pointwise_upper (V t) (U t)
        _ = rho (U t) + ‖R t‖ := by rw [h_VU, norm_neg]
    have h_nn : 0 ≤ rho (V t) := abs_nonneg _
    have h_nn2 : 0 ≤ rho (U t) := abs_nonneg _
    have h_nn3 : 0 ≤ ‖R t‖ := norm_nonneg _
    nlinarith [sq_nonneg (rho (V t) - (rho (U t) + ‖R t‖)),
              sq_nonneg (rho (U t) - ‖R t‖)]
  have h_rho_sq : ∫ t, (rho (V t)) ^ 2 ∂AddCircle.haarAddCircle ≤
      2 * ∫ t, (rho (U t)) ^ 2 ∂AddCircle.haarAddCircle +
      2 * ∫ t, ‖R t‖ ^ 2 ∂AddCircle.haarAddCircle := by
    have h1 := integral_mono hiRhoV hiRhoUR_add h_rho_pw
    have h2 : ∫ t, (2 * (rho (U t)) ^ 2 + 2 * ‖R t‖ ^ 2) ∂AddCircle.haarAddCircle =
        2 * ∫ t, (rho (U t)) ^ 2 ∂AddCircle.haarAddCircle +
        2 * ∫ t, ‖R t‖ ^ 2 ∂AddCircle.haarAddCircle := by
      rw [show (fun t => 2 * (rho (U t)) ^ 2 + 2 * ‖R t‖ ^ 2) =
        (fun t => (2 : ℝ) * (fun t => (rho (U t)) ^ 2) t +
          (2 : ℝ) * (fun t => ‖R t‖ ^ 2) t) from rfl]
      rw [integral_add (hiRhoU.const_mul _) (hiR.const_mul _),
          integral_const_mul, integral_const_mul]
    linarith
  have h_ann : ∫ t, ‖V t‖ ^ 2 ∂AddCircle.haarAddCircle ≤
      1620 ^ 2 * ∫ t, (rho (V t)) ^ 2 ∂AddCircle.haarAddCircle := h_annulus
  have h_rho_nn : 0 ≤ ∫ t, (rho (V t)) ^ 2 ∂AddCircle.haarAddCircle :=
    integral_nonneg (fun t => sq_nonneg _)
  have h_rhoU_nn : 0 ≤ ∫ t, (rho (U t)) ^ 2 ∂AddCircle.haarAddCircle :=
    integral_nonneg (fun t => sq_nonneg _)
  have h_R_nn : 0 ≤ ∫ t, ‖R t‖ ^ 2 ∂AddCircle.haarAddCircle :=
    integral_nonneg (fun t => sq_nonneg _)
  have h_V_nn : 0 ≤ ∫ t, ‖V t‖ ^ 2 ∂AddCircle.haarAddCircle :=
    integral_nonneg (fun t => sq_nonneg _)
  change ∫ t, ‖U t‖ ^ 2 ∂AddCircle.haarAddCircle ≤
    4 * 1620 ^ 2 * ∫ t, (rho (U t)) ^ 2 ∂AddCircle.haarAddCircle +
    (4 * 1620 ^ 2 + 2) * ∫ t, ‖R t‖ ^ 2 ∂AddCircle.haarAddCircle
  nlinarith [h_norm_add, h_ann, h_rho_sq, h_rho_nn, h_rhoU_nn, h_R_nn, h_V_nn]

/-! ## Annular decomposition infrastructure -/

private lemma annular_summand_nonneg (j : ℕ)
    {g : ℝ → ℝ} (hg : ∀ r, r ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1) → 0 ≤ g r) :
    0 ≤ 2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) * g r := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  apply intervalIntegral.integral_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j])
  intro r hr
  exact mul_nonneg (mul_nonneg (le_trans (Nat.cast_nonneg (α := ℝ) j) hr.1)
    (le_of_lt (Real.exp_pos _))) (hg r hr)

/-- Partial annular sums of fock integrand ≤ fockNormSq.
Standard measure-theory fact: nonneg sum over disjoint subsets ≤ integral. -/
private lemma annular_fock_partial_le {D : ℕ} (a : Fin D → ℂ) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
          ∂AddCircle.haarAddCircle)) ≤ fockNormSq a := by
  rw [fockNormSq_polar]
  set f := fun r : ℝ => r * Real.exp (-r ^ 2) *
    (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) with hf_def
  -- Factor out the 2
  have h_factor : ∀ j : ℕ,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), f r =
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), f r := fun _ => rfl
  -- Show ∑ 2 * ∫ = 2 * ∑ ∫
  rw [← Finset.mul_sum]
  gcongr
  -- Now need: ∑_{j<J} ∫_j^{j+1} f ≤ ∫_{Ioi 0} f
  -- Strategy: telescope the sum to ∫_0^J f, then bound by ∫_{Ioi 0} f
  -- Step 1: each piece is interval integrable (continuous)
  have hf_cont : Continuous f := by
    apply Continuous.mul
    · exact continuous_id.mul (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2)))
    · show Continuous (fun r => ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
        ∂AddCircle.haarAddCircle)
      simp_rw [circleNormSq_polyEvalCircle]
      apply continuous_finsetSum; intro k _
      exact continuous_const.mul ((continuous_pow 2).pow _)
  have hf_ii : ∀ (a b : ℝ), IntervalIntegrable f volume a b :=
    fun a b => hf_cont.intervalIntegrable a b
  -- Step 2: telescope
  have h_telescope : ∀ J : ℕ,
      ∑ j ∈ Finset.range J, ∫ r in (j : ℝ)..(j + 1 : ℝ), f r =
      ∫ r in (0 : ℝ)..(J : ℝ), f r := by
    intro J; induction J with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : (↑(n + 1) : ℝ) = (↑n : ℝ) + 1 := by push_cast; ring
      rw [this]
      exact (intervalIntegral.integral_add_adjacent_intervals (hf_ii 0 n) (hf_ii n (↑n + 1)))
  rw [h_telescope]
  -- Step 3: ∫_0^J f ≤ ∫_{Ioi 0} f (for nonneg f with f integrable on Ioi)
  -- We need f integrable on Ioi 0.
  -- From the proof of fockNormSq_polar, f equals a finite sum of integrable functions.
  have hf_intOn : IntegrableOn f (Set.Ioi 0) volume := by
    simp_rw [hf_def, circleNormSq_polyEvalCircle]
    have integrand_eq : ∀ r : ℝ,
        r * Real.exp (-r ^ 2) * ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) =
        ∑ k : Fin D, ‖a k‖ ^ 2 *
          (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) := by
      intro r; rw [Finset.mul_sum]; congr 1; ext k
      have : (r ^ 2) ^ (k.val + 1) = r ^ (2 * (k.val + 1)) := by rw [← pow_mul]
      rw [this]; ring
    simp_rw [integrand_eq]
    apply Integrable.integrableOn
    apply integrable_finsetSum; intro k _
    exact (integrable_pow_mul_exp_neg_sq (2 * (k.val + 1) + 1)).const_mul _
  have hJ_nn : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
  rw [intervalIntegral.integral_of_le hJ_nn]
  apply setIntegral_mono_set hf_intOn
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun r hr => by
      simp only [hf_def, Pi.zero_apply]; apply mul_nonneg
      · exact mul_nonneg (le_of_lt (Set.mem_Ioi.mp hr)) (le_of_lt (Real.exp_pos _))
      · exact integral_nonneg (fun t => sq_nonneg _))
  · exact Filter.Eventually.of_forall (fun r hr => Set.Ioc_subset_Ioi_self hr)

/-- Partial annular sums of rho integrand ≤ rhoFockNormSq. -/
private lemma annular_rho_partial_le {D : ℕ} (a : Fin D → ℂ) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, (rho (polyEvalCircle a r t)) ^ 2
          ∂AddCircle.haarAddCircle)) ≤ rhoFockNormSq a := by
  rw [polar_coord_fock]
  set g := fun r : ℝ => r * Real.exp (-r ^ 2) *
    (∫ t : AddCircle T, (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle) with hg_def
  rw [← Finset.mul_sum]
  gcongr
  -- Now need: ∑_{j<J} ∫_j^{j+1} g ≤ ∫_{Ioi 0} g
  -- Same structure as annular_fock_partial_le, using polar_coord_fock instead of fockNormSq_polar
  -- Continuity of the rho² circle integral as a function of r
  -- We use: rho(polyEvalCircle a r t)² ≤ ‖polyEvalCircle a r t‖² = polynomial in r
  -- and the norm² integral has closed form by circleNormSq_polyEvalCircle
  have h_rho_le_norm : ∀ r, ∫ t : AddCircle T, (rho (polyEvalCircle a r t)) ^ 2
      ∂AddCircle.haarAddCircle ≤
      ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle := by
    intro r
    exact integral_mono
      (integrable_rho_sq_of_continuous (continuous_polyEvalCircle a r))
      (integrable_sq_of_continuous (continuous_polyEvalCircle a r))
      (fun t => by
        exact pow_le_pow_left₀ (abs_nonneg _) (rho_le_norm _) 2)
  -- Continuity of r ↦ ∫ ‖polyEvalCircle a r t‖² (polynomial in r)
  have hf_circle_cont : Continuous (fun r : ℝ =>
      ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    simp_rw [circleNormSq_polyEvalCircle]
    apply continuous_finsetSum; intro k _
    exact continuous_const.mul ((continuous_pow 2).pow _)
  -- Integrability of the fock integrand on Ioi 0
  have hf_intOn : IntegrableOn (fun r => r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle))
      (Set.Ioi 0) volume := by
    simp_rw [circleNormSq_polyEvalCircle]
    have integrand_eq : ∀ r : ℝ,
        r * Real.exp (-r ^ 2) * ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) =
        ∑ k : Fin D, ‖a k‖ ^ 2 *
          (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) := by
      intro r; rw [Finset.mul_sum]; congr 1; ext k
      have : (r ^ 2) ^ (k.val + 1) = r ^ (2 * (k.val + 1)) := by rw [← pow_mul]
      rw [this]; ring
    simp_rw [integrand_eq]
    apply Integrable.integrableOn
    apply integrable_finsetSum; intro k _
    exact (integrable_pow_mul_exp_neg_sq (2 * (k.val + 1) + 1)).const_mul _
  -- Joint continuity of polyEvalCircle in (r, t)
  have h_jc : Continuous (fun (p : ℝ × AddCircle T) => polyEvalCircle a p.1 p.2) := by
    unfold polyEvalCircle
    apply continuous_finsetSum; intro k _
    exact ((continuous_const.mul ((Complex.continuous_ofReal.comp continuous_fst).pow _)).mul
      ((fourier _).continuous.comp continuous_snd))
  -- g is continuous
  have hg_cont : Continuous g := by
    change Continuous (fun r => r * Real.exp (-r ^ 2) *
      ∫ t : AddCircle T, (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle)
    apply Continuous.mul
    · exact continuous_id.mul (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2)))
    · -- Use continuous_parametric_integral_of_continuous with s = Set.univ
      have h_uncurry : Continuous (Function.uncurry
          (fun r (t : AddCircle T) => (rho (polyEvalCircle a r t)) ^ 2)) :=
        (continuous_rho.comp h_jc).pow 2
      have h_set : Continuous (fun r => ∫ t in Set.univ,
          (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle) :=
        continuous_parametric_integral_of_continuous h_uncurry isCompact_univ
      have : (fun r => ∫ t in Set.univ,
          (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle) =
          (fun r => ∫ t, (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle) := by
        ext r; exact MeasureTheory.setIntegral_univ
      rw [this] at h_set; exact h_set
  have hg_ii : ∀ (a b : ℝ), IntervalIntegrable g volume a b :=
    fun a b => hg_cont.intervalIntegrable a b
  -- Telescope
  have h_telescope : ∀ J : ℕ,
      ∑ j ∈ Finset.range J, ∫ r in (j : ℝ)..(j + 1 : ℝ), g r =
      ∫ r in (0 : ℝ)..(J : ℝ), g r := by
    intro J; induction J with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : (↑(n + 1) : ℝ) = (↑n : ℝ) + 1 := by push_cast; ring
      rw [this]
      exact intervalIntegral.integral_add_adjacent_intervals (hg_ii 0 n) (hg_ii n (↑n + 1))
  rw [h_telescope]
  -- Integrability of g on Ioi 0 (dominated by fock integrand)
  have hg_intOn : IntegrableOn g (Set.Ioi 0) volume := by
    rw [IntegrableOn]
    apply Integrable.mono' hf_intOn
    · exact hg_cont.aestronglyMeasurable.restrict
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall (fun r hr => by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · simp only [hg_def]
          apply mul_le_mul_of_nonneg_left (h_rho_le_norm r)
            (mul_nonneg (le_of_lt (Set.mem_Ioi.mp hr)) (le_of_lt (Real.exp_pos _)))
        · simp only [hg_def]
          exact mul_nonneg (mul_nonneg (le_of_lt (Set.mem_Ioi.mp hr))
            (le_of_lt (Real.exp_pos _))) (integral_nonneg (fun t => sq_nonneg _)))
  have hJ_nn : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
  rw [intervalIntegral.integral_of_le hJ_nn]
  apply setIntegral_mono_set hg_intOn
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun r hr => by
      simp only [hg_def, Pi.zero_apply]
      exact mul_nonneg (mul_nonneg (le_of_lt (Set.mem_Ioi.mp hr))
        (le_of_lt (Real.exp_pos _))) (integral_nonneg (fun t => sq_nonneg _)))
  · exact Filter.Eventually.of_forall (fun r hr => Set.Ioc_subset_Ioi_self hr)

/-- Partial sums approximate fockNormSq: for any ε > 0, ∃ J with sum > fockNormSq - ε.
Uses `intervalIntegral_tendsto_integral_Ioi` from Mathlib. -/
private lemma fockNormSq_sup_annular {D : ℕ} (a : Fin D → ℂ) :
    ∀ ε > 0, ∃ J, fockNormSq a - ε <
    ∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
          ∂AddCircle.haarAddCircle) := by
  intro ε hε
  set f := fun r : ℝ => r * Real.exp (-r ^ 2) *
    (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) with hf_def
  -- f is continuous
  have hf_cont : Continuous f := by
    apply Continuous.mul
    · exact continuous_id.mul (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2)))
    · simp_rw [circleNormSq_polyEvalCircle]
      apply continuous_finsetSum; intro k _
      exact continuous_const.mul ((continuous_pow 2).pow _)
  -- f is integrable on Ioi 0
  have hf_intOn : IntegrableOn f (Set.Ioi 0) volume := by
    simp_rw [hf_def, circleNormSq_polyEvalCircle]
    have integrand_eq : ∀ r : ℝ,
        r * Real.exp (-r ^ 2) * ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) =
        ∑ k : Fin D, ‖a k‖ ^ 2 *
          (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) := by
      intro r; rw [Finset.mul_sum]; congr 1; ext k
      have : (r ^ 2) ^ (k.val + 1) = r ^ (2 * (k.val + 1)) := by rw [← pow_mul]
      rw [this]; ring
    simp_rw [integrand_eq]
    apply Integrable.integrableOn
    apply integrable_finsetSum; intro k _
    exact (integrable_pow_mul_exp_neg_sq (2 * (k.val + 1) + 1)).const_mul _
  -- Interval integrability
  have hf_ii : ∀ (a b : ℝ), IntervalIntegrable f volume a b :=
    fun a b => hf_cont.intervalIntegrable a b
  -- Telescope: ∑_{j<J} ∫_j^{j+1} f = ∫_0^J f
  have h_telescope : ∀ J : ℕ,
      ∑ j ∈ Finset.range J, ∫ r in (j : ℝ)..(j + 1 : ℝ), f r =
      ∫ r in (0 : ℝ)..(J : ℝ), f r := by
    intro J; induction J with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : (↑(n + 1) : ℝ) = (↑n : ℝ) + 1 := by push_cast; ring
      rw [this]
      exact intervalIntegral.integral_add_adjacent_intervals (hf_ii 0 n) (hf_ii n (↑n + 1))
  -- ∫_0^J f → ∫_{Ioi 0} f as J → ∞ (via intervalIntegral_tendsto_integral_Ioi)
  have h_tends : Filter.Tendsto (fun (b : ℝ) => ∫ r in (0 : ℝ)..b, f r)
      Filter.atTop (nhds (∫ r in Set.Ioi (0 : ℝ), f r)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hf_intOn Filter.tendsto_id
  -- The partial sums are 2 * ∫_0^J f
  -- fockNormSq a = 2 * ∫_{Ioi 0} f
  have h_eq : fockNormSq a = 2 * ∫ r in Set.Ioi (0 : ℝ), f r := fockNormSq_polar a
  -- Extract: for ε/2 > 0, ∃ N ∈ ℕ with ∫_0^N f > ∫_{Ioi} f - ε/2
  have h_half : 0 < ε / 2 := by linarith
  -- Use `Metric.tendsto_atTop` to extract a witness
  rw [Metric.tendsto_atTop] at h_tends
  obtain ⟨N, hN⟩ := h_tends (ε / 2) h_half
  -- Take J = ⌈N⌉₊ + 1
  set J := Nat.ceil N + 1
  use J
  have hJ_ge : (J : ℝ) ≥ N := by
    calc (J : ℝ) = ↑(Nat.ceil N + 1) := rfl
      _ ≥ ↑(Nat.ceil N) := by exact_mod_cast Nat.le_succ _
      _ ≥ N := Nat.le_ceil N
  have hN_spec := hN (J : ℝ) hJ_ge
  rw [Real.dist_eq] at hN_spec
  have h_abs := abs_lt.mp hN_spec
  -- h_abs.1 : -(ε/2) < ∫_0^J f - ∫_{Ioi} f
  -- h_abs.2 : ∫_0^J f - ∫_{Ioi} f < ε/2
  -- So ∫_{Ioi} f - ε/2 < ∫_0^J f
  set I := ∫ r in Set.Ioi (0 : ℝ), f r
  set S := ∫ r in (0 : ℝ)..(J : ℝ), f r
  have h_close : I - ε / 2 < S := by linarith [h_abs.1]
  -- Goal: fockNormSq a - ε < ∑_{j<J} 2 * ∫_j^{j+1} f
  rw [h_eq, show ∑ j ∈ Finset.range J, 2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), f r =
      2 * ∑ j ∈ Finset.range J, ∫ r in (j : ℝ)..(j + 1 : ℝ), f r from
      (Finset.mul_sum ..).symm, h_telescope]
  linarith

private lemma annular_circle_bound {D : ℕ} (hD : 1 ≤ D) (a : Fin D → ℂ) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
          ∂AddCircle.haarAddCircle)) ≤
    4 * 1620 ^ 2 *
      (∑ j ∈ Finset.range J,
        2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
          (∫ t : AddCircle T, (rho (polyEvalCircle a r t)) ^ 2
            ∂AddCircle.haarAddCircle)) +
    (4 * 1620 ^ 2 + 2) *
      (∑ j ∈ Finset.range J,
        2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
          (∫ t : AddCircle T,
            ‖remainderPoly a 5 j (↑r * (fourier 1 t : ℂ))‖ ^ 2
            ∂AddCircle.haarAddCircle)) := by
  -- Generic lemma: per-j bound → summed bound with constants distributed
  have h_sum_distrib : ∀ (F G H : ℕ → ℝ) (C₁ C₂ : ℝ) (s : Finset ℕ),
      (∀ j ∈ s, F j ≤ C₁ * G j + C₂ * H j) →
      ∑ j ∈ s, F j ≤ C₁ * ∑ j ∈ s, G j + C₂ * ∑ j ∈ s, H j := by
    intro F G H C₁ C₂ s hpj
    calc ∑ j ∈ s, F j ≤ ∑ j ∈ s, (C₁ * G j + C₂ * H j) := Finset.sum_le_sum hpj
      _ = C₁ * ∑ j ∈ s, G j + C₂ * ∑ j ∈ s, H j := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  apply h_sum_distrib; clear h_sum_distrib
  intro j hj
  -- For this j, need:
  -- 2 * ∫ r, w(r) * f(r) ≤ 4*1620² * (2 * ∫ r, w(r) * g(r)) + (4*1620²+2) * (2 * ∫ r, w(r) * h(r))
  -- where f(r) = ∫ t, ‖polyEvalCircle a r t‖², g(r) = ∫ t, (rho(..))², h(r) = ∫ t, ‖remainder..‖²
  -- Strategy: factor out the 2, use integral_mono_on for f ≤ C₁*g + C₂*h,
  -- then use integral_add and integral_const_mul
  set B := (1620 : ℝ) ^ 2
  set C₁ := 4 * B
  set C₂ := 4 * B + 2
  let w : ℝ → ℝ := fun r => r * Real.exp (-r ^ 2)
  let f : ℝ → ℝ := fun r => ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle
  let g : ℝ → ℝ := fun r =>
    ∫ t : AddCircle T, (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle
  let h : ℝ → ℝ := fun r =>
    ∫ t : AddCircle T, ‖remainderPoly a 5 j (↑r * (fourier 1 t : ℂ))‖ ^ 2
      ∂AddCircle.haarAddCircle
  change 2 * ∫ r in (j : ℝ)..(↑j + 1 : ℝ), w r * f r ≤
    C₁ * (2 * ∫ r in (↑j : ℝ)..(↑j + 1 : ℝ), w r * g r) +
    C₂ * (2 * ∫ r in (↑j : ℝ)..(↑j + 1 : ℝ), w r * h r)
  -- Pointwise bound: for r ∈ [j, j+1], f(r) ≤ C₁ * g(r) + C₂ * h(r)
  have hpw : ∀ r ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1), f r ≤ C₁ * g r + C₂ * h r := by
    intro r ⟨hr_lo, hr_hi⟩
    have hr_nn : 0 ≤ r := le_trans (Nat.cast_nonneg (α := ℝ) j) hr_lo
    exact circle_level_bound hD a j hr_nn hr_lo hr_hi
  -- Weight is nonneg on [j, j+1]
  have hw_nn : ∀ r ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1), 0 ≤ w r := by
    intro r ⟨hr_lo, _⟩
    exact mul_nonneg (le_trans (Nat.cast_nonneg (α := ℝ) j) hr_lo) (le_of_lt (Real.exp_pos _))
  -- f, g, h are continuous (and hence interval-integrable)
  have hf_cont : Continuous f := by
    change Continuous fun r =>
      ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle
    simp_rw [circleNormSq_polyEvalCircle]
    apply continuous_finsetSum; intro k _
    exact continuous_const.mul ((continuous_pow 2).pow _)
  have hg_cont : Continuous g := by
    have h_jc : Continuous (fun (p : ℝ × AddCircle T) => polyEvalCircle a p.1 p.2) := by
      unfold polyEvalCircle
      apply continuous_finsetSum; intro k _
      exact ((continuous_const.mul ((Complex.continuous_ofReal.comp continuous_fst).pow _)).mul
        ((fourier _).continuous.comp continuous_snd))
    have h_uncurry : Continuous (Function.uncurry
        (fun r (t : AddCircle T) => (rho (polyEvalCircle a r t)) ^ 2)) :=
      (continuous_rho.comp h_jc).pow 2
    have h_set : Continuous (fun r => ∫ t in Set.univ,
        (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle) :=
      continuous_parametric_integral_of_continuous h_uncurry isCompact_univ
    have : (fun r => ∫ t in Set.univ,
        (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle) =
        (fun r => ∫ t, (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle) := by
      ext r; exact MeasureTheory.setIntegral_univ
    rw [this] at h_set; exact h_set
  have hh_cont : Continuous h := by
    have h_jc2 : Continuous (fun (p : ℝ × AddCircle T) =>
        remainderPoly a 5 j (↑p.1 * (fourier 1 p.2 : ℂ))) := by
      simp only [remainderPoly]
      apply Continuous.sub
      · unfold polyEval
        apply continuous_finsetSum; intro k _
        exact continuous_const.mul
          (((Complex.continuous_ofReal.comp continuous_fst).mul
            ((fourier 1).continuous.comp continuous_snd)).pow _)
      · unfold localPoly blockPoly
        apply continuous_finsetSum; intro ℓ _
        apply continuous_finsetSum; intro k _
        by_cases hk : (k.val + 1) ∈ freqBlock ℓ
        · simp only [hk, ite_true]
          exact continuous_const.mul
            (((Complex.continuous_ofReal.comp continuous_fst).mul
              ((fourier 1).continuous.comp continuous_snd)).pow _)
        · simp only [hk, ite_false]; exact continuous_const
    have h_uncurry2 : Continuous (Function.uncurry
        (fun (r : ℝ) (t : AddCircle T) => ‖remainderPoly a 5 j (↑r * (fourier 1 t : ℂ))‖ ^ 2)) :=
      ((continuous_norm.comp h_jc2).pow 2 : Continuous (fun p : ℝ × AddCircle T =>
        ‖remainderPoly a 5 j (↑p.1 * (fourier 1 p.2 : ℂ))‖ ^ 2))
    have h_set2 : Continuous (fun (r : ℝ) => ∫ t in Set.univ,
        ‖remainderPoly a 5 j (↑r * (fourier 1 t : ℂ))‖ ^ 2 ∂AddCircle.haarAddCircle) :=
      continuous_parametric_integral_of_continuous h_uncurry2 isCompact_univ
    simp only [MeasureTheory.setIntegral_univ] at h_set2; exact h_set2
  have hw_cont : Continuous w := continuous_id.mul
    (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2)))
  -- w * f is interval integrable
  have hwf_ii : IntervalIntegrable (fun r => w r * f r) volume (j : ℝ) ((j : ℝ) + 1) :=
    (hw_cont.mul hf_cont).intervalIntegrable _ _
  -- w * g and w * h are interval integrable
  have hwg_ii : IntervalIntegrable (fun r => w r * g r) volume (j : ℝ) ((j : ℝ) + 1) :=
    (hw_cont.mul hg_cont).intervalIntegrable _ _
  have hwh_ii : IntervalIntegrable (fun r => w r * h r) volume (j : ℝ) ((j : ℝ) + 1) :=
    (hw_cont.mul hh_cont).intervalIntegrable _ _
  -- Integral bound: ∫ w*f ≤ ∫ w*(C₁*g + C₂*h) = C₁ * ∫ w*g + C₂ * ∫ w*h
  have hj_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
  have h_int_le : ∫ r in (j : ℝ)..(j + 1 : ℝ), w r * f r ≤
      C₁ * (∫ r in (j : ℝ)..(j + 1 : ℝ), w r * g r) +
      C₂ * (∫ r in (j : ℝ)..(j + 1 : ℝ), w r * h r) := by
    have h_bound : ∫ r in (j : ℝ)..(j + 1 : ℝ), w r * f r ≤
        ∫ r in (j : ℝ)..(j + 1 : ℝ), (C₁ * (w r * g r) + C₂ * (w r * h r)) := by
      apply intervalIntegral.integral_mono_on hj_le hwf_ii
      · exact ((hwg_ii.const_mul C₁).add (hwh_ii.const_mul C₂))
      · intro r ⟨hr_lo, hr_hi⟩
        have hrIcc : r ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1) := ⟨hr_lo, hr_hi⟩
        have hwr : 0 ≤ w r := hw_nn r hrIcc
        have hfr : f r ≤ C₁ * g r + C₂ * h r := hpw r hrIcc
        calc w r * f r ≤ w r * (C₁ * g r + C₂ * h r) := by
              exact mul_le_mul_of_nonneg_left hfr hwr
          _ = C₁ * (w r * g r) + C₂ * (w r * h r) := by ring
    calc ∫ r in (j : ℝ)..(j + 1 : ℝ), w r * f r
        ≤ ∫ r in (j : ℝ)..(j + 1 : ℝ), (C₁ * (w r * g r) + C₂ * (w r * h r)) := h_bound
      _ = C₁ * (∫ r in (j : ℝ)..(j + 1 : ℝ), w r * g r) +
          C₂ * (∫ r in (j : ℝ)..(j + 1 : ℝ), w r * h r) := by
        rw [intervalIntegral.integral_add (hwg_ii.const_mul _) (hwh_ii.const_mul _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- Now combine: the goal has w*f = r*exp(-r²) * f, etc.
  change 2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), w r * f r ≤
    C₁ * (2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), w r * g r) +
    C₂ * (2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), w r * h r)
  nlinarith [h_int_le]

/-! ## Pre-absorption inequality

The proof uses `le_of_forall_pos_lt_add` and avoids J-dependent leakage bounds.
For each δ > 0:
1. Get ε from `total_leakage_bound` with ε' = δ/(4*(fockNormSq+1))
2. Get bound from `total_leakage_bound`
3. Get J₀ from `fockNormSq_sup_annular` with δ/2
4. Use J = max J₀ bound, so J ≥ bound and S_fock(J) ≥ S_fock(J₀) > fockNormSq - δ/2
5. Apply `total_leakage_bound` at J to get S_leak ≤ (etaCoeff 5 J + ε') * fockNormSq
6. etaCoeff 5 J ≤ etaCoeff 5 100 (since J ≥ bound ≥ 100... no, not necessarily)
   Actually etaCoeff is monotone, so etaCoeff 5 J ≥ etaCoeff 5 100 for J ≥ 100.
   But we only need etaCoeff 5 J < 4/10^11 + ε' approximately.
   The key: C * (etaCoeff 5 J + ε') * fockNormSq ≤ C * etaCoeff 5 100 * fockNormSq + extra
   where extra → 0 with δ. Since etaCoeff 5 J ≤ etaCoeff 5 100 for J ≤ 100
   and etaCoeff 5 J ≤ etaCoeff 5 100 + 6*exp(-10201) for all J.
   The 6*exp(-10201) * C * fockNormSq term is J-independent but tiny.
   We can bound it by δ/4 by choosing δ appropriately... no, δ is given.

   THE FIX: Instead of etaCoeff 5 100, use the bound for ALL J.
   Change the statement to use a universal leakage coefficient.
-/

-- Universal bound: ∑_{m=5}^J exp(-m²) ≤ ∑_{m=5}^100 exp(-m²) for J ≤ 100,
-- and the tail for J > 100 is bounded by a geometric series.
-- to_mathlib: Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
private lemma etaCoeff_5_universal (J : ℕ) : etaCoeff 5 J < 4 / (10 : ℝ) ^ 11 := by
  by_cases hJ : J ≤ 100
  · exact lt_of_le_of_lt (by unfold etaCoeff; gcongr) eta_5_bound
  · push Not at hJ
    -- Strategy: bound ∑ exp(-m²) ≤ exp(-25)/(1-exp(-5)) via geometric series,
    -- then use exp(5) ≥ 148 and exp(1/4) ≤ 13/10 to get numerical bound.
    set r := Real.exp (-5) with hr_def
    have hr_pos : 0 < r := Real.exp_pos _
    have hr_lt : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num : (-5:ℝ) < 0)
    have h1r : 0 < 1 - r := by linarith
    -- exp(5) ≥ 148 (from 13-term Taylor series)
    have hexp5 : (148 : ℝ) ≤ Real.exp 5 :=
      le_trans (by norm_num) (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 5) 13)
    -- exp(-5) ≤ 1/148 (from 148 ≤ exp(5))
    have hr_le : r ≤ 1 / 148 := by
      have : 148 * r ≤ 1 := by
        calc 148 * r = 148 * Real.exp (-5) := by rw [hr_def]
          _ ≤ Real.exp 5 * Real.exp (-5) := by gcongr
          _ = 1 := by rw [← Real.exp_add]; simp
      linarith
    -- exp(1/4) ≤ 13/10 (from Taylor + error bound)
    have hexp14 : Real.exp (1 / 4 : ℝ) ≤ 13 / 10 :=
      (Real.exp_bound' (by norm_num) (by norm_num) (by norm_num : (0:ℕ) < 4)).trans (by norm_num)
    -- Step 1: Pointwise bound exp(-m²) ≤ r^m for m ≥ 5 (since m² ≥ 5m)
    have h_pw : ∀ m ∈ Finset.Icc 5 J, Real.exp (-(m : ℝ) ^ 2) ≤ r ^ m := by
      intro m hm; simp only [Finset.mem_Icc] at hm
      rw [hr_def, ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
      have hm5 : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by linarith
      -- Need: -(m:ℝ)² ≤ ↑m * (-5), i.e., 5*m ≤ m² (since m ≥ 5)
      nlinarith [mul_self_nonneg ((m : ℝ) - 5)]
    -- Step 2: Geometric series ∑_{m ∈ Icc 5 J} r^m ≤ r^5/(1-r)
    have h_geom : ∑ m ∈ Finset.Icc 5 J, r ^ m ≤ r ^ 5 / (1 - r) := by
      rw [show Finset.Icc 5 J = Finset.Ico 5 (J + 1) from by
        ext m; simp [Finset.mem_Icc, Finset.mem_Ico]]
      rw [geom_sum_Ico' (ne_of_lt hr_lt) (by omega : (5:ℕ) ≤ J + 1)]
      exact div_le_div_of_nonneg_right (by linarith [pow_pos hr_pos (J + 1)]) (le_of_lt h1r)
    -- Step 3: Combine all bounds
    have h1 : ∑ m ∈ Finset.Icc 5 J, Real.exp (-(m : ℝ) ^ 2) ≤ r ^ 5 / (1 - r) :=
      le_trans (Finset.sum_le_sum h_pw) h_geom
    calc etaCoeff 5 J
        = 2 * Real.exp (1 / 4) * ∑ m ∈ Finset.Icc 5 J, Real.exp (-(m : ℝ) ^ 2) := rfl
      _ ≤ 2 * (13 / 10) * (r ^ 5 / (1 - r)) := by gcongr
      _ ≤ 2 * (13 / 10) * ((1 / 148) ^ 5 / (1 - 1 / 148)) := by gcongr
      _ < 4 / 10 ^ 11 := by norm_num

private lemma pre_absorption {D : ℕ} (hD : 1 ≤ D) (a : Fin D → ℂ) :
    fockNormSq a ≤ 8 * 1620 ^ 2 * rhoFockNormSq a := by
  -- Prove via le_of_forall_pos_lt_add with universal eta bound and absorption
  apply le_of_forall_pos_lt_add; intro δ hδ
  have hfock_nn := fockNormSq_nonneg a
  have hrho_nn := rhoFockNormSq_nonneg a
  set C := (4 * 1620 ^ 2 + 2 : ℝ)
  have hC_pos : 0 < C := by positivity
  -- Get ε' for total_leakage_bound
  set ε' := min (δ / (4 * C * (fockNormSq a + 1))) (1 / (4 * C)) with hε'_def
  have hε'_pos : 0 < ε' := by positivity
  -- Get bound from total_leakage_bound
  obtain ⟨bound, hbound⟩ := total_leakage_bound a (show (2 : ℕ) ≤ 5 by omega) ε' hε'_pos
  -- Get J₀ from fockNormSq_sup_annular
  obtain ⟨J₀, hJ₀⟩ := fockNormSq_sup_annular a (δ / 2) (by linarith)
  -- Use J = max J₀ bound
  set J := max J₀ bound with hJ_def
  -- S_fock(J) ≥ S_fock(J₀) > fockNormSq - δ/2  (monotonicity: more nonneg terms)
  have hJ₀_le_J : J₀ ≤ J := le_max_left _ _
  have hbound_le_J : bound ≤ J := le_max_right _ _
  have h_mono_fock : ∑ j ∈ Finset.range J₀,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) ≤
    ∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hJ₀_le_J)
    intro j _ _
    exact annular_summand_nonneg j (fun r _ => integral_nonneg (fun t => sq_nonneg _))
  set S_fock := ∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle)
  set S_rho := ∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T, (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle)
  set S_leak := ∑ j ∈ Finset.range J,
      2 * ∫ r in (j : ℝ)..(j + 1 : ℝ), r * Real.exp (-r ^ 2) *
        (∫ t : AddCircle T,
          ‖remainderPoly a 5 j (↑r * (fourier 1 t : ℂ))‖ ^ 2
          ∂AddCircle.haarAddCircle)
  have h1 : fockNormSq a < S_fock + δ / 2 := by linarith [hJ₀, h_mono_fock]
  have h2 : S_fock ≤ 4 * 1620 ^ 2 * S_rho + C * S_leak := annular_circle_bound hD a J
  have h3 : S_rho ≤ rhoFockNormSq a := annular_rho_partial_le a J
  -- Apply total_leakage_bound at J (since J ≥ bound)
  have h4 : S_leak ≤ (etaCoeff 5 J + ε') * fockNormSq a := hbound J hbound_le_J
  -- etaCoeff is monotone: J₁ ≤ J₂ → etaCoeff M J₁ ≤ etaCoeff M J₂
  have h_eta_mono : ∀ {M J₁ J₂ : ℕ}, J₁ ≤ J₂ → etaCoeff M J₁ ≤ etaCoeff M J₂ := by
    intro M J₁ J₂ hle; unfold etaCoeff; gcongr
  -- Bound C * ε' * fockNormSq < δ / 4
  have h_eps_bound : C * ε' * fockNormSq a < δ / 4 := by
    have hfock1 : (0 : ℝ) < fockNormSq a + 1 := by linarith
    calc C * ε' * fockNormSq a
        ≤ C * (δ / (4 * C * (fockNormSq a + 1))) * fockNormSq a := by
          gcongr; exact min_le_left _ _
      _ < C * (δ / (4 * C * (fockNormSq a + 1))) * (fockNormSq a + 1) := by
          gcongr; linarith
      _ = δ / 4 := by field_simp
  -- Chain: fockNormSq < 4B²R + C*(eta_J + ε')*F + δ/2
  have h_chain : fockNormSq a < 4 * 1620 ^ 2 * rhoFockNormSq a +
      C * (etaCoeff 5 J + ε') * fockNormSq a + δ / 2 := by
    have : S_fock ≤ 4 * 1620 ^ 2 * rhoFockNormSq a +
        C * ((etaCoeff 5 J + ε') * fockNormSq a) := by
      calc S_fock ≤ 4 * 1620 ^ 2 * S_rho + C * S_leak := h2
        _ ≤ 4 * 1620 ^ 2 * rhoFockNormSq a + C * ((etaCoeff 5 J + ε') * fockNormSq a) := by
          gcongr
    nlinarith
  -- Universal eta bound: C*eta_J < 1/4 (much tighter than < 1/2)
  have h_C_eta_tight : C * etaCoeff 5 J < 1 / 4 :=
    calc C * etaCoeff 5 J < C * (4 / (10 : ℝ) ^ 11) :=
          mul_lt_mul_of_pos_left (etaCoeff_5_universal J) hC_pos
      _ < 1 / 4 := by norm_num
  -- C*ε' ≤ 1/4 (from our choice of ε')
  have h_C_eps : C * ε' ≤ 1 / 4 := by
    calc C * ε' ≤ C * (1 / (4 * C)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hC_pos)
      _ = 1 / 4 := by field_simp
  -- Therefore C*(eta_J + ε') < 1/4 + 1/4 = 1/2
  have h_absorb : C * (etaCoeff 5 J + ε') < 1 / 2 := by
    calc C * (etaCoeff 5 J + ε') = C * etaCoeff 5 J + C * ε' := by ring
      _ < 1 / 4 + 1 / 4 := by linarith
      _ = 1 / 2 := by norm_num
  -- Absorption: F*(1 - η) < 4B²R + δ/2 with η < 1/2, so F < 8B²R + δ
  change fockNormSq a < 8 * 1620 ^ 2 * rhoFockNormSq a + δ
  nlinarith [h_chain, h_absorb, hfock_nn, hrho_nn]
  /-  OLD PROOF (used J≤100/J>100 split with etaCoeff 5 100)
  -- For J ≤ 100: etaCoeff 5 J ≤ etaCoeff 5 100, so we directly bound
  -- C*(etaCoeff 5 J + ε')*F ≤ C*etaCoeff 5 100*F + C*ε'*F < C*eta₁₀₀*F + δ/4
  -- and fockNormSq < 4B²R + C*eta₁₀₀*F + δ/4 + δ/2 < 4B²R + C*eta₁₀₀*F + δ
  --
  -- For J > 100: etaCoeff 5 J ≥ etaCoeff 5 100. We use absorption:
  -- C*(etaCoeff 5 J + ε') < C*(4/10^11) + C*ε' < 1/2 (by eta_5_bound applied
  -- to the uniform bound; see comments). Then (1 - C*(eta_J+ε'))*F < 4B²R + δ/2,
  -- so F < 2*(4B²R+δ/2) = 8B²R + δ ≤ 4B²R + 4B²R + δ.
  -- Since C*eta₁₀₀ ≥ 0 and 4B²R ≤ C*eta₁₀₀*F + 4B²R, we get...
  -- Actually this doesn't directly give the target. Use nlinarith instead.
  --
  -- The clean approach: show etaCoeff 5 J ≤ etaCoeff 5 (max J 100) and then use
  -- eta_5_bound to show etaCoeff 5 (max J 100) is still small enough.
  -- For J ≤ 100: max J 100 = 100, and eta_5_bound applies directly.
  -- So this reduces to the J ≤ 100 case.
  -- Key fact: etaCoeff 5 J ≤ etaCoeff 5 (max J 100), and for J ≤ 100 this = etaCoeff 5 100.
  -- For J > 100, we show the extra terms from Icc 101 J are bounded by the geometric
  -- series ∑_{m≥5} exp(-m²) which converges, and the full sum is still < 4/10^11.
  -- Proof: for m ≥ 6, exp(-m²) ≤ exp(-11)*exp(-(m-1)²) (since m²-(m-1)²=2m-1≥11).
  -- So ∑_{m=5}^J exp(-m²) ≤ exp(-25)/(1-exp(-11)).
  -- With exp(-25) < 14/10^12 and exp(-11) < 1/10000:
  -- ∑ ≤ (14/10^12)/(1-1/10000) = 14*10000/(10^12*9999) < 14.002/10^12.
  -- Then etaCoeff 5 J = 2*exp(1/4)*∑ < 2*(13/10)*(14.002/10^12)
  --                    = 36.4.../10^12 < 4/10^11. ✓
  -- Below we prove etaCoeff 5 J ≤ etaCoeff 5 100 for J ≤ 100 (clean case).
  -- For J > 100, we prove the goal directly using the chain + absorption bound,
  -- without needing etaCoeff 5 J ≤ etaCoeff 5 100.
  -- Show the target: fockNormSq < 4B²R + C*eta₁₀₀*F + δ
  show fockNormSq a < 4 * 1620 ^ 2 * rhoFockNormSq a +
      (4 * 1620 ^ 2 + 2) * etaCoeff 5 100 * fockNormSq a + δ
  -- From the chain: fockNormSq < 4B²R + C*(eta_J + ε')*F + δ/2
  -- Expand: = 4B²R + C*eta_J*F + C*ε'*F + δ/2
  -- For J ≤ 100: C*eta_J ≤ C*eta₁₀₀, so ≤ 4B²R + C*eta₁₀₀*F + C*ε'*F + δ/2 < ... + δ
  -- For J > 100: use C*(eta_J+ε') < 1/2, absorb, get F < 8B²R + δ.
  --   Then need 8B²R + δ ≤ 4B²R + C*eta₁₀₀*F + δ, i.e., 4B²R ≤ C*eta₁₀₀*F.
  --   From F < 8B²R + δ (for this δ), R > (F-δ)/(8B²). Then 4B²R > 4B²(F-δ)/(8B²) = (F-δ)/2.
  --   Need (F-δ)/2 ≤ C*eta₁₀₀*F, i.e., F-δ ≤ 2*C*eta₁₀₀*F, i.e., F(1-2Cη) ≤ δ.
  --   Since 2Cη < 1: 1-2Cη > 0, so F ≤ δ/(1-2Cη). This bounds F by something
  --   proportional to δ. Then using this F bound in the original chain gives the result.
  -- Actually for J > 100, we use the chain + the fact that C*eta_J < C*(4/10^11) < 1/2
  -- by proving a uniform eta bound. Once we have C*(eta_J+ε') < 1/2, absorb:
  -- (1-C*(eta_J+ε'))*F < 4B²R + δ/2, so F < (4B²R+δ/2)/(1-C*(eta_J+ε')).
  -- Since eta_J < 4/10^11 (uniform bound) and ε' small:
  -- 1/(1-C*(eta_J+ε')) < 1/(1-1/2) = 2, so F < 2*4B²R + δ = 8B²R + δ.
  -- Then: 4B²R + C*eta₁₀₀*F + δ ≥ 4B²R + 0 + δ > δ > 0.
  -- And F < 8B²R + δ. Need F < 4B²R + C*eta₁₀₀*F + δ.
  -- i.e., F - C*eta₁₀₀*F < 4B²R + δ, i.e., (1-C*eta₁₀₀)*F < 4B²R + δ.
  -- From chain: (1-C*(eta_J+ε'))*F < 4B²R + δ/2.
  -- And 1-C*eta₁₀₀ ≥ 1-C*(eta_J+ε') (since eta₁₀₀ ≤ eta_J+ε' for J ≥ 100).
  -- So (1-C*eta₁₀₀)*F ≥ (1-C*(eta_J+ε'))*F. And (1-C*(eta_J+ε'))*F < 4B²R + δ/2.
  -- THIS DOESN'T WORK since (1-C*eta₁₀₀)*F is LARGER.
  -- For the J ≤ 100 case only:
  by_cases hJ100 : J ≤ 100
  · -- Case J ≤ 100: etaCoeff 5 J ≤ etaCoeff 5 100
    have h_eta_le : etaCoeff 5 J ≤ etaCoeff 5 100 := h_eta_mono hJ100
    -- So C*(eta_J + ε')*F ≤ C*(eta₁₀₀ + ε')*F = C*eta₁₀₀*F + C*ε'*F
    have : C * (etaCoeff 5 J + ε') * fockNormSq a ≤
        C * etaCoeff 5 100 * fockNormSq a + C * ε' * fockNormSq a := by
      have : etaCoeff 5 J + ε' ≤ etaCoeff 5 100 + ε' := by linarith
      nlinarith [hfock_nn, hC_pos]
    -- fockNormSq < 4B²R + C*eta₁₀₀*F + C*ε'*F + δ/2 < 4B²R + C*eta₁₀₀*F + δ/4 + δ/2 < ... + δ
    linarith
  · -- Case J > 100: etaCoeff 5 J > etaCoeff 5 100 potentially.
    -- Use the chain directly: fockNormSq < 4B²R + C*(eta_J+ε')*F + δ/2.
    -- Key insight: we still have fockNormSq < 4B²R + C*(eta_J+ε')*F + δ/2,
    -- and C*(eta_J+ε') ≤ C*eta_J + C*ε'. Also, eta_J < 4/10^11 (uniform bound
    -- from geometric series). And C*(4/10^11) < 1/2.
    -- So C*(eta_J+ε') < 1/2 + C*ε'.
    -- (1-C*(eta_J+ε'))*fockNormSq < 4B²R + δ/2
    -- For the target: (1-C*eta₁₀₀)*fockNormSq < 4B²R + δ.
    -- Now (1-C*eta₁₀₀) = (1-C*(eta_J+ε')) + C*(eta_J+ε'-eta₁₀₀).
    -- So (1-C*eta₁₀₀)*F = (1-C*(eta_J+ε'))*F + C*(eta_J+ε'-eta₁₀₀)*F
    -- < 4B²R + δ/2 + C*(eta_J+ε'-eta₁₀₀)*F.
    -- Need C*(eta_J+ε'-eta₁₀₀)*F ≤ δ/2. With eta_J-eta₁₀₀ ≥ 0 and ε' > 0:
    -- C*(eta_J-eta₁₀₀)*F + C*ε'*F. The C*ε'*F < δ/4.
    -- The C*(eta_J-eta₁₀₀)*F: depends on J and F. For large F and small δ, can be > δ/4.
    -- UNRESOLVABLE: This case requires a J-independent leakage bound.
    -- For now, use the chain with absorption and the universal eta bound.
    push Not at hJ100
    -- Since we have the chain and all the necessary bounds, use nlinarith
    -- with enough hypotheses to close the gap.
    -- The key: C*(eta_J + ε') < 1 (weaker than < 1/2 but sufficient).
    -- fockNormSq < 4B²R + C*(eta_J+ε')*fockNormSq + δ/2
    -- = 4B²R + C*eta_J*fockNormSq + C*ε'*fockNormSq + δ/2
    -- Since C*eta₁₀₀ ≤ C*eta_J (monotonicity for J ≥ 100):
    -- 4B²R + C*eta₁₀₀*F + δ ≥ 4B²R + C*eta₁₀₀*F + δ
    -- And we need fockNormSq < 4B²R + C*eta₁₀₀*F + δ.
    -- From chain: fockNormSq < 4B²R + C*eta_J*F + C*ε'*F + δ/2
    -- ≥ 4B²R + C*eta₁₀₀*F + C*ε'*F + δ/2  (since C*eta_J ≥ C*eta₁₀₀)
    -- So: fockNormSq < 4B²R + C*eta_J*F + C*ε'*F + δ/2 (*)
    -- And: 4B²R + C*eta₁₀₀*F + δ ≥ 4B²R + C*eta₁₀₀*F + δ (**)
    -- We need to show fockNormSq < (**). From (*), fockNormSq < something,
    -- and (**) ≥ 4B²R + C*eta₁₀₀*F + δ. Since C*eta_J ≥ C*eta₁₀₀:
    -- (*) gives fockNormSq < 4B²R + C*eta_J*F + ... ≥ 4B²R + C*eta₁₀₀*F + ...
    -- So fockNormSq < RHS_of_(*) and RHS_of_(*) ≤ 4B²R + C*eta_J*F + C*ε'*F + δ/2
    -- And 4B²R + C*eta₁₀₀*F + δ need not be ≥ RHS_of_(*).
    -- In fact: 4B²R + C*eta₁₀₀*F + δ vs 4B²R + C*eta_J*F + C*ε'*F + δ/2
    -- = (C*(eta₁₀₀-eta_J) - C*ε')*F + δ/2 ≤ 0 + δ/2 (since eta₁₀₀ ≤ eta_J and ε' > 0).
    -- So 4B²R + C*eta₁₀₀*F + δ ≤ 4B²R + C*eta_J*F + C*ε'*F + δ/2 + δ/2.
    -- Wait: 4B²R + C*eta₁₀₀*F + δ = 4B²R + C*eta_J*F + C*ε'*F + δ/2
    -- + (C*(eta₁₀₀-eta_J-ε')*F + δ/2).
    -- Since eta₁₀₀ ≤ eta_J: C*(eta₁₀₀-eta_J-ε') ≤ -C*ε' < 0.
    -- So the extra term is negative. So 4B²R + C*eta₁₀₀*F + δ ≤ 4B²R + C*eta_J*F + C*ε'*F + δ/2.
    -- WAIT NO: C*eta₁₀₀ ≤ C*eta_J, so C*eta₁₀₀*F ≤ C*eta_J*F. So:
    -- 4B²R + C*eta₁₀₀*F + δ ≤ 4B²R + C*eta_J*F + δ
    -- And 4B²R + C*eta_J*F + δ ≥ 4B²R + C*eta_J*F + C*ε'*F + δ/2
    --   iff δ ≥ C*ε'*F + δ/2 iff δ/2 ≥ C*ε'*F. Since C*ε'*F < δ/4 < δ/2: YES!
    -- So 4B²R + C*eta₁₀₀*F + δ ≤ 4B²R + C*eta_J*F + δ
    -- and 4B²R + C*eta_J*F + δ > 4B²R + C*eta_J*F + C*ε'*F + δ/2 (since δ > C*ε'*F + δ/2)
    -- Wait: 4B²R + C*eta_J*F + δ > 4B²R + C*eta_J*F + C*ε'*F + δ/2
    --   iff δ > C*ε'*F + δ/2 iff δ/2 > C*ε'*F. Since C*ε'*F < δ/4 < δ/2: YES!
    -- So: 4B²R + C*eta₁₀₀*F + δ ≤ 4B²R + C*eta_J*F + δ
    --   > 4B²R + C*eta_J*F + C*ε'*F + δ/2 > fockNormSq.
    -- THEREFORE: fockNormSq < 4B²R + C*eta₁₀₀*F + δ.
    -- THIS WORKS! The key: for J > 100, eta₁₀₀ ≤ eta_J, so C*eta₁₀₀*F ≤ C*eta_J*F,
    -- and the target RHS with eta₁₀₀ is SMALLER than the chain RHS with eta_J.
    -- But fockNormSq < chain RHS, and chain RHS ≤ target RHS + some slack.
    -- Actually wait, let me recheck:
    -- fockNormSq < 4B²R + C*eta_J*F + C*ε'*F + δ/2 ... (*)
    -- target: fockNormSq < 4B²R + C*eta₁₀₀*F + δ ... (**)
    -- Since eta₁₀₀ ≤ eta_J: C*eta₁₀₀*F ≤ C*eta_J*F.
    -- (**) = 4B²R + C*eta₁₀₀*F + δ ≤ 4B²R + C*eta_J*F + δ
    -- And (*) = 4B²R + C*eta_J*F + C*ε'*F + δ/2
    -- (**) - (*) = (C*eta₁₀₀ - C*eta_J)*F + δ - C*ε'*F - δ/2
    --           = C*(eta₁₀₀-eta_J)*F + δ/2 - C*ε'*F
    --           ≥ (since eta₁₀₀ ≤ eta_J) -(C*(eta_J-eta₁₀₀))*F + δ/2 - C*ε'*F
    -- For (**) ≥ (*): need C*(eta₁₀₀-eta_J)*F + δ/2 - C*ε'*F ≥ 0
    --   i.e., δ/2 ≥ C*(eta_J-eta₁₀₀+ε')*F. But this is the same problematic bound!
    -- HOWEVER: let me check the other direction. We have (*): fockNormSq < RHS_star.
    -- We want fockNormSq < RHS_target. We need RHS_star ≤ RHS_target, i.e., (*) ≤ (**).
    -- (*) = 4B²R + C*eta_J*F + C*ε'*F + δ/2
    -- (**) = 4B²R + C*eta₁₀₀*F + δ
    -- (*) ≤ (**) iff C*eta_J*F + C*ε'*F + δ/2 ≤ C*eta₁₀₀*F + δ
    --              iff C*(eta_J-eta₁₀₀+ε')*F ≤ δ/2
    -- Same problematic bound!
    -- OK SO: fockNormSq < (*) but (*) might be > (**). In that case, fockNormSq < (*) > (**)
    -- which does NOT imply fockNormSq < (**).
    -- ARGH.
    -- Wait, I made an error above. Let me recheck:
    -- (*) says fockNormSq < 4B²R + C*(eta_J+ε')*F + δ/2
    -- (**) says fockNormSq < 4B²R + C*eta₁₀₀*F + δ
    -- Since eta_J ≥ eta₁₀₀ for J > 100:
    -- C*(eta_J+ε')*F ≥ C*eta₁₀₀*F + C*ε'*F ≥ C*eta₁₀₀*F
    -- So RHS(*) = 4B²R + C*(eta_J+ε')*F + δ/2 ≥ 4B²R + C*eta₁₀₀*F + δ/2
    -- And RHS(**) = 4B²R + C*eta₁₀₀*F + δ
    -- RHS(**) - (4B²R + C*eta₁₀₀*F + δ/2) = δ/2 > 0
    -- So RHS(**) > 4B²R + C*eta₁₀₀*F + δ/2.
    -- And RHS(*) ≥ 4B²R + C*eta₁₀₀*F + δ/2.
    -- But RHS(*) could be > or < RHS(**) depending on C*(eta_J-eta₁₀₀+ε')*F vs δ/2.
    -- If RHS(*) ≤ RHS(**): fockNormSq < RHS(*) ≤ RHS(**). DONE.
    -- If RHS(*) > RHS(**): can't conclude.
    -- THE KEY: RHS(*) ≤ RHS(**) iff C*(eta_J-eta₁₀₀+ε')*F ≤ δ/2. Same old.
    --
    -- Use universal eta bound: C*eta_J < 1/2, then the chain RHS ≤ target RHS.
    -- Chain: F < 4B²R + C*eta_J*F + C*ε'*F + δ/2
    -- Target: F < 4B²R + C*eta₁₀₀*F + δ
    -- Since eta₁₀₀ ≤ eta_J: target ≤ 4B²R + C*eta_J*F + δ
    -- And C*ε'*F + δ/2 < δ/4 + δ/2 = 3δ/4 < δ
    -- So chain RHS < 4B²R + C*eta_J*F + δ ≥ target. QED.
    have h_eta_100_le : etaCoeff 5 100 ≤ etaCoeff 5 J :=
      h_eta_mono (le_of_lt hJ100)
    -- Chain RHS < 4B²R + C*eta_J*F + δ (since C*ε'*F < δ/4 and δ/2 + δ/4 < δ)
    -- And target = 4B²R + C*eta₁₀₀*F + δ ≤ 4B²R + C*eta_J*F + δ (since eta₁₀₀ ≤ eta_J)
    -- So F < chain RHS < 4B²R + C*eta_J*F + δ and target ≤ same thing
    -- This still doesn't give F < target directly.
    -- Correct approach: target = 4B²R + C*eta₁₀₀*F + δ. We need (1-C*eta₁₀₀)*F < 4B²R + δ.
    -- From chain: (1-C*(eta_J+ε'))*F < 4B²R + δ/2. Since eta₁₀₀ ≤ eta_J + ε':
    -- 1 - C*eta₁₀₀ ≥ 1 - C*(eta_J+ε'). So (1-C*eta₁₀₀)*F ≥ (1-C*(eta_J+ε'))*F.
    -- This goes the wrong way! (1-C*eta₁₀₀) is BIGGER.
    -- HOWEVER: (1-C*eta₁₀₀)*F = (1-C*(eta_J+ε'))*F + C*(eta_J+ε'-eta₁₀₀)*F
    -- < 4B²R + δ/2 + C*(eta_J+ε'-eta₁₀₀)*F
    -- And C*(eta_J+ε'-eta₁₀₀)*F = C*(eta_J-eta₁₀₀)*F + C*ε'*F
    -- ≤ C*eta_J*F + C*ε'*F  (crude bound: eta_J-eta₁₀₀ ≤ eta_J)
    -- So (1-C*eta₁₀₀)*F < 4B²R + δ/2 + C*eta_J*F + C*ε'*F
    -- And we need < 4B²R + δ. This requires C*eta_J*F + C*ε'*F < δ/2. Not guaranteed.
    -- FINAL CORRECT APPROACH: use the absorption result directly.
    -- From chain and universal bound: F*(1 - C*(eta_J+ε')) < 4B²R + δ/2
    -- C*(eta_J+ε') ≤ C*eta_J + C*ε' < C*(4/10^11) + C*ε'
    -- With ε' ≤ min(δ/(4C(F+1)), 1/(4C)): C*ε' ≤ 1/4
    -- And C*(4/10^11) < 1/2 (absorption_check)
    -- So C*(eta_J+ε') < 1/2 + 1/4 = 3/4 (but actually < 1/2 since C*eta_J ≈ 0.0004)
    -- Actually: C*eta_J < C*(4/10^11) ≈ 0.00042 and C*ε' ≤ 1/4 = 0.25
    -- Sum: < 0.25042 < 1/2 ✓
    -- So 1 - C*(eta_J+ε') > 1/2, giving F < 2*(4B²R + δ/2) = 8B²R + δ
    -- Now the target has C*eta₁₀₀ ≥ 0, so target ≥ 4B²R + δ.
    -- And also target = 4B²R + C*eta₁₀₀*F + δ ≥ 4B²R + δ (since C*eta₁₀₀*F ≥ 0).
    -- We need F < target, i.e., F - C*eta₁₀₀*F < 4B²R + δ.
    -- From F < 8B²R + δ: F ≤ 8B²R + δ (or F < 8B²R + δ).
    -- (1-C*eta₁₀₀)*F < (8B²R+δ) since 1-C*eta₁₀₀ < 1. WRONG DIRECTION.
    -- Actually (1-C*eta₁₀₀)*F ≤ F < 8B²R + δ. So (1-C*eta₁₀₀)*F < 8B²R + δ.
    -- Need (1-C*eta₁₀₀)*F < 4B²R + δ. This needs 8B²R + δ ≤ 4B²R + δ, FALSE.
    -- SO THIS APPROACH DOES NOT WORK for the tight pre_absorption statement.
    -- The statement `F ≤ 4B²R + C*eta₁₀₀*F` for the J > 100 case is genuinely hard
    -- without a tight universal bound. Change to the weaker absorption form.
    -- For now, we note: the statement is TRUE but our proof infrastructure doesn't support it.
    -- We change the proof to use the weaker absorbed form instead.
    -- PLACEHOLDER: use the universal bound to show eta_J also < 4/10^11 for J > 100
    have h_eta_J_bound : etaCoeff 5 J < 4 / (10 : ℝ) ^ 11 := etaCoeff_5_universal J
    have h_C_eta_J : C * etaCoeff 5 J < 1 / 2 :=
      calc C * etaCoeff 5 J < C * (4 / (10 : ℝ) ^ 11) :=
            mul_lt_mul_of_pos_left h_eta_J_bound hC_pos
        _ < 1 / 2 := absorption_check
    -- C*ε' ≤ C * min(δ/(4C(F+1)), 1/(4C)) ≤ C * (1/(4C)) = 1/4
    have h_C_eps : C * ε' ≤ 1 / 4 := by
      calc C * ε' ≤ C * (1 / (4 * C)) := by
            gcongr; exact min_le_right _ _
        _ = 1 / 4 := by field_simp
    -- Also C*ε'*F < δ/4
    have h_eps_bound : C * ε' * fockNormSq a < δ / 4 := by
      calc C * ε' * fockNormSq a
          ≤ C * (δ / (4 * C * (fockNormSq a + 1))) * fockNormSq a := by
            gcongr; exact min_le_left _ _
        _ < C * (δ / (4 * C * (fockNormSq a + 1))) * (fockNormSq a + 1) := by
            gcongr; linarith
        _ = δ / 4 := by field_simp
    -- C*(eta_J + ε') < 1/2 (since C*eta_J < 1/2 and C*ε' ≤ 1/4 < 1/2 - C*eta_J ≈ 0.4996)
    have h_absorb_coeff : C * (etaCoeff 5 J + ε') < 1 / 2 := by
      have := mul_add C (etaCoeff 5 J) ε'
      linarith [h_C_eta_J, h_C_eps]
    -- Absorption: F < 8B²R + δ. Since target ≥ 4B²R + δ and F < 8B²R + δ:
    -- need F < 4B²R + C*eta₁₀₀*F + δ. Rearrange: (1-C*eta₁₀₀)*F < 4B²R + δ.
    -- From (1-C*(eta_J+ε'))*F < 4B²R + δ/2, and 1-C*eta₁₀₀ ≤ 1:
    -- (1-C*eta₁₀₀)*F ≤ F. And F - C*(eta_J+ε')*F < 4B²R + δ/2.
    -- So (1-C*eta₁₀₀)*F = F - C*eta₁₀₀*F = (F - C*(eta_J+ε')*F) + C*(eta_J+ε'-eta₁₀₀)*F
    --   < (4B²R + δ/2) + C*(eta_J+ε')*F - C*eta₁₀₀*F + (some correction)
    -- THIS IS STILL CIRCULAR. Let me just use nlinarith with all available bounds.
    nlinarith [h_chain, h_absorb_coeff, hfock_nn, hrho_nn, h_eps_bound,
               h_eta_100_le, etaCoeff_nonneg 5 100, h_C_eta_J]
  -/

theorem fock_space_coercivity {D : ℕ} (hD : 1 ≤ D) (a : Fin D → ℂ) :
    fockNormSq a ≤ 4600 ^ 2 * rhoFockNormSq a := by
  have hpre := pre_absorption hD a
  calc fockNormSq a
      ≤ 8 * 1620 ^ 2 * rhoFockNormSq a := hpre
    _ ≤ 4600 ^ 2 * rhoFockNormSq a := by nlinarith [final_constant_check, rhoFockNormSq_nonneg a]

/-- Fock-space coercivity for complex polynomials with zero constant term. -/
theorem LocalFockSPR
    (p : Polynomial ℂ)
    (hp : p.eval 0 = 0) :
    ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
    ≤ 4600 ^ 2 *
    ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2)
    := by
  by_cases hp0 : p = 0
  · subst hp0
    simp only [eval_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul, integral_zero, add_zero, one_mem, CStarRing.norm_of_mem_unitary, sub_self,
      abs_zero, mul_zero, le_refl]
  · have hcoeff0 : p.coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero]; exact hp
    have hD : 1 ≤ p.natDegree := by
      by_contra hlt
      push Not at hlt
      interval_cases h : p.natDegree
      exact hp0 (eq_C_of_natDegree_eq_zero (by omega) |>.trans
        (by simp only [hcoeff0, map_zero]))
    set D := p.natDegree
    set a : Fin D → ℂ := fun k => p.coeff (k.val + 1)
    have heval : ∀ z, p.eval z = polyEval a z := by
      intro z
      rw [eval_eq_sum_range, polyEval]
      rw [Finset.sum_range_succ' (fun i => p.coeff i * z ^ i)]
      simp only [hcoeff0, zero_mul, pow_zero]
      rw [← Fin.sum_univ_eq_sum_range]
      ring
    simp_rw [heval, show ∀ z, |‖1 + polyEval a z‖ - 1| = rho (polyEval a z) from
      fun z => by simp only [rho]]
    have h1 := fockNorm_eq_gaussian_integral a
    have h2 := fock_space_coercivity hD a
    rw [← h1] at h2
    unfold rhoFockNormSq at h2
    rw [← mul_assoc, mul_comm (4600 ^ 2 : ℝ) (1 / Real.pi), mul_assoc] at h2
    exact le_of_mul_le_mul_left h2 (div_pos one_pos Real.pi_pos)

end FockSPR
