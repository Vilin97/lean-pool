/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # LocalCore.lean
  The analytic core of the local Fock-space phase retrieval estimate.

  This file upgrades the orthogonal statement from `MainTheorem.lean` to a local one:
  instead of assuming `p(0) = 0`, we assume that `p` is small in the normalized
  Gaussian `L²` norm and that its constant coefficient is real.
-/
import LeanPool.PhaseRetrieval.Constant.Internal.MainTheorem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # LocalCore -/


open FockSPR MeasureTheory Complex Real Polynomial Finset
open scoped ENNReal ComplexConjugate

noncomputable section

namespace FockSPR

private lemma rho_continuous : Continuous (rho : ℂ → ℝ) :=
  continuous_abs.comp
    (continuous_norm.comp (continuous_const.add continuous_id) |>.sub continuous_const)

/-- Integral over AddCircle with volume = `T • haar`. -/
private lemma integral_addCircle_volume_eq_smul_haar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AddCircle T → E) :
    ∫ t : AddCircle T, f t = T • ∫ t : AddCircle T, f t ∂AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  rw [integral_smul_measure]
  simp [ENNReal.toReal_ofReal T_pos.le]

/-- Integral of a periodic function over `(-π, π)` equals its integral over `AddCircle T`. -/
private lemma integral_Ioo_eq_addCircle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AddCircle T → E) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, f (QuotientAddGroup.mk θ) =
      ∫ t : AddCircle T, f t := by
  rw [← integral_Ioc_eq_integral_Ioo]
  have h : -Real.pi + T = Real.pi := by simp [T]; ring
  rw [show Set.Ioc (-Real.pi) Real.pi = Set.Ioc (-Real.pi) (-Real.pi + T) from by rw [h]]
  exact AddCircle.integral_preimage T (-Real.pi) f

/-- Combining the two interval/add-circle identities. -/
private lemma integral_Ioo_eq_T_smul_haar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AddCircle T → E) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, f (QuotientAddGroup.mk θ) =
      T • ∫ t : AddCircle T, f t ∂AddCircle.haarAddCircle := by
  rw [integral_Ioo_eq_addCircle, integral_addCircle_volume_eq_smul_haar]

private lemma fourier_mk_eq_exp (n : ℤ) (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : AddCircle T) : ℂ) =
    Complex.exp (Complex.I * ↑n * ↑θ) := by
  rw [fourier_coe_apply]
  have harg : (2 * ↑π * Complex.I * ↑n * ↑θ / T : ℂ) = Complex.I * ↑n * ↑θ := by
    rw [show (T : ℂ) = (2 * Real.pi : ℝ) by simp [T]]
    field_simp [Real.pi_ne_zero]
    push_cast
    ring
  rw [harg]

private lemma cos_add_sin_mul_I (θ : ℝ) :
    (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I : ℂ) = Complex.exp (Complex.I * ↑θ) := by
  rw [mul_comm Complex.I, Complex.exp_mul_I]
  simp [Complex.ofReal_cos, Complex.ofReal_sin]

private lemma cos_add_sin_mul_I_pow (θ : ℝ) (n : ℕ) :
    (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I : ℂ) ^ n =
      Complex.exp (Complex.I * ↑(n : ℤ) * ↑θ) := by
  rw [cos_add_sin_mul_I]
  rw [show Complex.I * ↑(n : ℤ) * ↑θ = ↑n * (Complex.I * ↑θ) from by push_cast; ring]
  rw [Complex.exp_nat_mul]

private lemma polarCoord_symm_pow (r θ : ℝ) (n : ℕ) :
    (Complex.polarCoord.symm (r, θ) : ℂ) ^ n =
      (↑r) ^ n * Complex.exp (Complex.I * ↑(n : ℤ) * ↑θ) := by
  rw [Complex.polarCoord_symm_apply, mul_pow, cos_add_sin_mul_I_pow]

private lemma polyEval_polar_eq_polyEvalCircle {D : ℕ} (a : Fin D → ℂ)
    (r θ : ℝ) :
    polyEval a (Complex.polarCoord.symm (r, θ)) =
      polyEvalCircle a r (QuotientAddGroup.mk θ) := by
  rw [polyEval, polyEvalCircle]
  congr 1
  ext k
  rw [polarCoord_symm_pow, fourier_mk_eq_exp]
  ring

private lemma integral_fourier_eq_zero (n : ℤ) (hn : n ≠ 0) :
    ∫ t : AddCircle T, (fourier n) t ∂AddCircle.haarAddCircle = 0 := by
  have h : fourierCoeff (fun t => (fourier (0 : ℤ) : C(AddCircle T, ℂ)) t) (-n) = 0 := by
    rw [show (fun t => (fourier (0 : ℤ) : C(AddCircle T, ℂ)) t) =
        (fourier 0 : C(AddCircle T, ℂ)) from rfl, fourierCoeff_fourier]
    simp [Pi.single, Function.update, hn]
  rw [fourierCoeff] at h
  simp only [fourier_zero, smul_eq_mul, mul_one, neg_neg] at h
  exact h

private lemma integral_polyEvalCircle_eq_zero {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    ∫ t : AddCircle T, polyEvalCircle a r t ∂AddCircle.haarAddCircle = 0 := by
  unfold polyEvalCircle
  rw [integral_finsetSum _ (fun k _ => by
    simpa using (((fourier ((k.val + 1 : ℕ) : ℤ)) : C(AddCircle T, ℂ)).continuous.const_mul
      (a k * (r : ℂ) ^ (k.val + 1))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  apply Finset.sum_eq_zero
  intro k hk
  have hne : (((k.val + 1 : ℕ) : ℤ) ≠ 0) := by exact_mod_cast Nat.succ_ne_zero k.val
  calc
    ∫ t : AddCircle T,
        a k * (r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t
          ∂AddCircle.haarAddCircle
        = (a k * (r : ℂ) ^ (k.val + 1)) *
            ∫ t : AddCircle T, fourier ((k.val + 1 : ℕ) : ℤ) t
              ∂AddCircle.haarAddCircle := by
            simpa [mul_assoc] using integral_const_mul
              (a k * (r : ℂ) ^ (k.val + 1))
              (fun t : AddCircle T => (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ))
    _ = 0 := by rw [integral_fourier_eq_zero _ hne, mul_zero]

private lemma cont_integrable_circle {f : AddCircle T → ℂ} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma real_cont_integrable_circle {f : AddCircle T → ℝ} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma continuous_polyEvalCircle {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    Continuous (polyEvalCircle a r) := by
  unfold polyEvalCircle
  apply continuous_finsetSum
  intro k hk
  exact continuous_const.mul (fourier _).continuous

private lemma integral_re_polyEvalCircle_eq_zero {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    ∫ t : AddCircle T, (polyEvalCircle a r t).re ∂AddCircle.haarAddCircle = 0 := by
  have hint : Integrable (polyEvalCircle a r) AddCircle.haarAddCircle :=
    cont_integrable_circle (continuous_polyEvalCircle a r)
  have hre := integral_re (μ := AddCircle.haarAddCircle) (f := polyEvalCircle a r) hint
  rw [show (∫ t : AddCircle T, (polyEvalCircle a r t).re ∂AddCircle.haarAddCircle) =
    (∫ t : AddCircle T, polyEvalCircle a r t ∂AddCircle.haarAddCircle).re by simpa using hre]
  simp [integral_polyEvalCircle_eq_zero a r]

private lemma integral_im_polyEvalCircle_eq_zero {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    ∫ t : AddCircle T, (polyEvalCircle a r t).im ∂AddCircle.haarAddCircle = 0 := by
  have hint : Integrable (polyEvalCircle a r) AddCircle.haarAddCircle :=
    cont_integrable_circle (continuous_polyEvalCircle a r)
  have him := integral_im (μ := AddCircle.haarAddCircle) (f := polyEvalCircle a r) hint
  rw [show (∫ t : AddCircle T, (polyEvalCircle a r t).im ∂AddCircle.haarAddCircle) =
    (∫ t : AddCircle T, polyEvalCircle a r t ∂AddCircle.haarAddCircle).im by simpa using him]
  simp [integral_polyEvalCircle_eq_zero a r]

private lemma integral_const_add_polyEvalCircle_sq {D : ℕ}
    (a : Fin D → ℂ) (r : ℝ) (c : ℂ) :
    ∫ t : AddCircle T, ‖c + polyEvalCircle a r t‖ ^ 2
      ∂AddCircle.haarAddCircle =
      ‖c‖ ^ 2 + ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
        ∂AddCircle.haarAddCircle := by
  have hcont : Continuous (polyEvalCircle a r) := continuous_polyEvalCircle a r
  have h_int1 :
      Integrable (fun t : AddCircle T => ‖c + polyEvalCircle a r t‖ ^ 2)
        AddCircle.haarAddCircle :=
    real_cont_integrable_circle ((continuous_const.add hcont).norm.pow 2)
  have h_int2 :
      Integrable (fun t : AddCircle T => ‖polyEvalCircle a r t‖ ^ 2)
        AddCircle.haarAddCircle :=
    real_cont_integrable_circle (hcont.norm.pow 2)
  have h_key : ∀ t : AddCircle T,
      ‖c + polyEvalCircle a r t‖ ^ 2 - ‖polyEvalCircle a r t‖ ^ 2 =
        ‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re + 2 * c.im * (polyEvalCircle a r t).im := by
    intro t
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sq_norm, Complex.normSq_apply]
    have hc : c.re ^ 2 + c.im ^ 2 = ‖c‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring_nf
    nlinarith
  have h_int3 :
      Integrable
        (fun t : AddCircle T =>
          ‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re + 2 * c.im * (polyEvalCircle a r t).im)
        AddCircle.haarAddCircle := by
    refine ((real_cont_integrable_circle continuous_const).add ?_).add ?_
    · exact real_cont_integrable_circle ((Complex.continuous_re.comp hcont).const_mul (2 * c.re))
    · exact real_cont_integrable_circle ((Complex.continuous_im.comp hcont).const_mul (2 * c.im))
  have h_diff :
      ∫ t : AddCircle T, ‖c + polyEvalCircle a r t‖ ^ 2
        ∂AddCircle.haarAddCircle -
      ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
        ∂AddCircle.haarAddCircle = ‖c‖ ^ 2 := by
    rw [← integral_sub h_int1 h_int2]
    have h_congr :
        (fun t : AddCircle T =>
          ‖c + polyEvalCircle a r t‖ ^ 2 - ‖polyEvalCircle a r t‖ ^ 2) =
        (fun t =>
          ‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re +
            2 * c.im * (polyEvalCircle a r t).im) := by
      ext t
      exact h_key t
    rw [h_congr]
    have h_split1 :
        ∫ t : AddCircle T,
            ‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re + 2 * c.im * (polyEvalCircle a r t).im
            ∂AddCircle.haarAddCircle =
          ∫ t : AddCircle T, (‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re)
            ∂AddCircle.haarAddCircle +
          ∫ t : AddCircle T, 2 * c.im * (polyEvalCircle a r t).im ∂AddCircle.haarAddCircle := by
      simpa [add_assoc] using
        (integral_add
          ((real_cont_integrable_circle continuous_const).add
            (real_cont_integrable_circle ((Complex.continuous_re.comp hcont).const_mul (2 * c.re))))
          (real_cont_integrable_circle ((Complex.continuous_im.comp hcont).const_mul (2 * c.im))))
    have h_split2 :
        ∫ t : AddCircle T, (‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re)
          ∂AddCircle.haarAddCircle =
          ∫ t : AddCircle T, ‖c‖ ^ 2 ∂AddCircle.haarAddCircle +
          ∫ t : AddCircle T, 2 * c.re * (polyEvalCircle a r t).re ∂AddCircle.haarAddCircle := by
      simpa using
        (integral_add (real_cont_integrable_circle continuous_const)
          (real_cont_integrable_circle ((Complex.continuous_re.comp hcont).const_mul (2 * c.re))))
    rw [h_split1, h_split2]
    rw [integral_const, integral_const_mul, integral_const_mul,
      integral_re_polyEvalCircle_eq_zero, integral_im_polyEvalCircle_eq_zero]
    simp
  linarith

private lemma continuous_mk_addCircle :
    Continuous (fun θ : ℝ => (QuotientAddGroup.mk θ : AddCircle T)) :=
  continuous_quotient_mk'

private lemma continuous_polyEvalCircle_comp {D : ℕ} (a : Fin D → ℂ) :
    Continuous (fun p : ℝ × ℝ => polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)) := by
  unfold polyEvalCircle
  apply continuous_finsetSum
  intro k hk
  exact Continuous.mul (Continuous.mul continuous_const
    ((continuous_ofReal.comp continuous_fst).pow _))
    ((fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ)).continuous.comp
      (continuous_mk_addCircle.comp continuous_snd))

private lemma continuous_polyEval {D : ℕ} (a : Fin D → ℂ) :
    Continuous (fun z : ℂ => polyEval a z) := by
  unfold polyEval
  apply continuous_finsetSum
  intro k hk
  exact continuous_const.mul (continuous_id.pow _)

private lemma integrable_pow_mul_exp_neg_sq (n : ℕ) :
    Integrable (fun r : ℝ => r ^ n * Real.exp (-r ^ 2)) volume := by
  have hs : (-1 : ℝ) < (n : ℝ) := by exact_mod_cast (show -1 < (n : ℤ) by omega)
  have h := integrable_rpow_mul_exp_neg_mul_sq one_pos hs
  refine h.congr ?_
  filter_upwards with r
  rw [rpow_natCast]
  ring_nf

private lemma integrable_abs_pow_mul_exp_neg_sq (n : ℕ) :
    Integrable (fun r : ℝ => |r| ^ n * Real.exp (-r ^ 2)) volume := by
  have :
      (fun r : ℝ => |r| ^ n * Real.exp (-r ^ 2)) =
        fun r => ‖r ^ n * Real.exp (-r ^ 2)‖ := by
    ext r
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  rw [this]
  exact (integrable_pow_mul_exp_neg_sq n).norm

private lemma norm_polyEvalCircle_le {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (t : AddCircle T) :
    ‖polyEvalCircle a r t‖ ≤ ∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1) := by
  unfold polyEvalCircle
  calc
    ‖∑ k : Fin D, a k * (r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t‖
        ≤ ∑ k : Fin D, ‖a k * (r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t‖ :=
          norm_sum_le _ _
    _ ≤ ∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_real]
          calc
            ‖a k‖ * ‖r‖ ^ (k.val + 1) * ‖fourier ((k.val + 1 : ℕ) : ℤ) t‖
                ≤ ‖a k‖ * ‖r‖ ^ (k.val + 1) *
                    ‖(fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ))‖ :=
                  mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _) (by positivity)
            _ = ‖a k‖ * ‖r‖ ^ (k.val + 1) := by rw [fourier_norm]; ring
            _ = ‖a k‖ * |r| ^ (k.val + 1) := by rw [Real.norm_eq_abs]

private lemma norm_sq_polyEvalCircle_le {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (t : AddCircle T) :
    ‖polyEvalCircle a r t‖ ^ 2 ≤
      (∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1)) ^ 2 := by
  have hsumnn : 0 ≤ ∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1) := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg r) _)
  nlinarith [norm_polyEvalCircle_le a r t, hsumnn, norm_nonneg (polyEvalCircle a r t)]

private lemma integrableOn_polar_norm {D : ℕ} (a : Fin D → ℂ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2))) :=
    Continuous.mul continuous_fst (Continuous.mul
      ((continuous_norm.comp (continuous_polyEvalCircle_comp a)).pow 2)
      (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))
  rw [IntegrableOn, ← Measure.prod_restrict (Set.Ioi 0) (Set.Ioo (-Real.pi) Real.pi)]
  rw [integrable_prod_iff hcont.aestronglyMeasurable]
  constructor
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply Filter.Eventually.of_forall
    intro r hr
    have hcont_theta : Continuous (fun θ : ℝ =>
        r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2))) := by
      apply Continuous.mul continuous_const
      apply Continuous.mul
      · exact (continuous_norm.comp (continuous_finsetSum _ (fun k _ =>
          Continuous.mul (Continuous.mul continuous_const continuous_const)
            ((fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ)).continuous.comp
              continuous_mk_addCircle)))).pow 2
      · exact continuous_const
    exact (hcont_theta.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  · set C := ∑ k : Fin D, ‖a k‖
    set bound := fun r : ℝ =>
      T * (4 * C ^ 2) *
        (|r| ^ 3 * Real.exp (-r ^ 2) +
          |r| ^ (2 * D + 1) * Real.exp (-r ^ 2))
    apply Integrable.mono'
      (g := bound)
    · exact (((integrable_abs_pow_mul_exp_neg_sq 3).add
        (integrable_abs_pow_mul_exp_neg_sq (2 * D + 1))).const_mul _).restrict
    · have hcont_int : Continuous (fun r : ℝ =>
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            ‖r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
              Real.exp (-r ^ 2))‖) :=
        continuous_parametric_integral_of_continuous hcont.norm isCompact_Icc
      have hIoo_eq_Icc : ∀ r, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
            Real.exp (-r ^ 2))‖ =
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            ‖r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
              Real.exp (-r ^ 2))‖ := by
        intro r
        exact (integral_Icc_eq_integral_Ioo).symm
      simp_rw [hIoo_eq_Icc]
      exact hcont_int.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · apply (ae_restrict_iff' measurableSet_Ioi).mpr
      apply Filter.Eventually.of_forall
      intro r hr
      simp only [Set.mem_Ioi] at hr
      rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Ioo
        (fun _ _ => norm_nonneg _))]
      have hnorm_eq : ∀ y : ℝ,
          ‖(r, y).1 * (‖polyEvalCircle a (r, y).1 (↑(r, y).2)‖ ^ 2 *
            rexp (-(r, y).1 ^ 2))‖ =
          r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2)) := by
        intro y; simp only []
        rw [Real.norm_of_nonneg (mul_nonneg (le_of_lt hr)
          (mul_nonneg (sq_nonneg _) (exp_pos _).le))]
      simp_rw [hnorm_eq]
      have hr_abs : |r| = r := abs_of_pos hr
      set S := (∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1)) ^ 2 with hS_def
      have hbd : ∀ y : ℝ,
          r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2)) ≤
          r * (S * rexp (-r ^ 2)) :=
        fun y => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_sq_polyEvalCircle_le a r _)
            (exp_pos _).le) (le_of_lt hr)
      calc ∫ y in Set.Ioo (-Real.pi) Real.pi,
            r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2))
          ≤ ∫ _ in Set.Ioo (-Real.pi) Real.pi, r * (S * rexp (-r ^ 2)) := by
            apply setIntegral_mono_on
            · have hcont_y : Continuous (fun y : ℝ =>
                  r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2))) := by
                apply Continuous.mul continuous_const
                apply Continuous.mul
                · exact (continuous_norm.comp (continuous_finsetSum _ (fun k _ =>
                    Continuous.mul (Continuous.mul continuous_const continuous_const)
                      ((fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ)).continuous.comp
                        continuous_mk_addCircle)))).pow 2
                · exact continuous_const
              exact hcont_y.continuousOn.integrableOn_compact isCompact_Icc
                |>.mono_set Set.Ioo_subset_Icc_self
            · exact (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set
                Set.Ioo_subset_Icc_self
            · exact measurableSet_Ioo
            · exact fun y _ => hbd y
        _ = T * (r * (S * rexp (-r ^ 2))) := by
            rw [setIntegral_const]
            simp only [smul_eq_mul]
            rw [Measure.real, Real.volume_Ioo,
              show Real.pi - (-Real.pi) = T by simp [T]; ring,
              ENNReal.toReal_ofReal T_pos.le]
        _ ≤ bound r := by
            have hexp_pos := exp_pos (-r ^ 2)
            have hT := T_pos.le
            suffices h : r * S ≤ 4 * C ^ 2 * (r ^ 3 + r ^ (2 * D + 1)) by
              calc T * (r * (S * rexp (-r ^ 2)))
                  = T * ((r * S) * rexp (-r ^ 2)) := by ring
                _ ≤ T * (4 * C ^ 2 * (r ^ 3 + r ^ (2 * D + 1)) * rexp (-r ^ 2)) := by
                    apply mul_le_mul_of_nonneg_left _ hT
                    exact mul_le_mul_of_nonneg_right h hexp_pos.le
                _ = bound r := by
                    unfold bound
                    rw [hr_abs]
                    ring
            rw [hS_def, hr_abs]
            have hsum_factor : ∑ k : Fin D, ‖a k‖ * r ^ (k.val + 1) =
                r * ∑ k : Fin D, ‖a k‖ * r ^ k.val := by
              rw [Finset.mul_sum]
              congr 1
              ext k
              rw [pow_succ]
              ring
            rw [hsum_factor]
            ring_nf
            have hC_nn : 0 ≤ C := Finset.sum_nonneg (fun k _ => norm_nonneg (a k))
            by_cases hD : D = 0
            · subst hD
              simp
              nlinarith [sq_nonneg C, pow_nonneg (le_of_lt hr) 3]
            · have hD_pos : 0 < D := Nat.pos_of_ne_zero hD
              have hr_nn := (le_of_lt hr)
              have hpow_le : ∀ k : Fin D, r ^ k.val ≤ 1 + r ^ (D - 1) := by
                intro k
                by_cases hr1 : r ≤ 1
                · have : r ^ k.val ≤ 1 := pow_le_one₀ (n := k.val) hr_nn hr1
                  linarith [pow_nonneg hr_nn (D - 1)]
                · push Not at hr1
                  have : r ^ k.val ≤ r ^ (D - 1) :=
                    pow_le_pow_right₀ hr1.le (by omega : k.val ≤ D - 1)
                  linarith
              have hsum_le : ∑ x : Fin D, r ^ x.val * ‖a x‖ ≤
                  (1 + r ^ (D - 1)) * C := by
                calc ∑ x, r ^ x.val * ‖a x‖
                  ≤ ∑ x : Fin D, (1 + r ^ (D - 1)) * ‖a x‖ :=
                      Finset.sum_le_sum (fun k _ =>
                        mul_le_mul_of_nonneg_right (hpow_le k) (norm_nonneg _))
                  _ = (1 + r ^ (D - 1)) * ∑ x : Fin D, ‖a x‖ := by
                    simpa using (Finset.mul_sum (s := Finset.univ)
                      (a := 1 + r ^ (D - 1)) (f := fun x : Fin D => ‖a x‖)).symm
                  _ = _ := by simp [C]
              have hsum_nn : 0 ≤ ∑ x : Fin D, r ^ x.val * ‖a x‖ :=
                Finset.sum_nonneg (fun k _ =>
                  mul_nonneg (pow_nonneg hr_nn k.val) (norm_nonneg _))
              have hfact_nn : 0 ≤ (1 + r ^ (D - 1)) * C :=
                mul_nonneg (by linarith [pow_nonneg hr_nn (D - 1)]) hC_nn
              have hsq : (∑ x : Fin D, r ^ x.val * ‖a x‖) ^ 2 ≤
                  ((1 + r ^ (D - 1)) * C) ^ 2 :=
                sq_le_sq' (by linarith) hsum_le
              have hsq2 : ((1 + r ^ (D - 1)) * C) ^ 2 ≤
                  2 * (1 + (r ^ (D - 1)) ^ 2) * C ^ 2 := by nlinarith [sq_nonneg (1 - r ^ (D - 1))]
              have hpow_eq : r ^ 3 * (r ^ (D - 1)) ^ 2 = r * r ^ (D * 2) := by
                have hexp_eq : 3 + (D - 1) * 2 = 1 + D * 2 := by omega
                rw [← pow_mul, ← pow_add, hexp_eq, pow_add, pow_one]
              calc r ^ 3 * (∑ x, r ^ x.val * ‖a x‖) ^ 2
                  ≤ r ^ 3 * (2 * (1 + (r ^ (D - 1)) ^ 2) * C ^ 2) := by
                    exact mul_le_mul_of_nonneg_left
                      (le_trans hsq hsq2) (pow_nonneg hr_nn 3)
                _ = 2 * C ^ 2 * (r ^ 3 + r ^ 3 * (r ^ (D - 1)) ^ 2) := by ring
                _ = 2 * C ^ 2 * (r ^ 3 + r * r ^ (D * 2)) := by rw [hpow_eq]
                _ ≤ r * r ^ (D * 2) * C ^ 2 * 4 + r ^ 3 * C ^ 2 * 4 := by
                    nlinarith [pow_nonneg hr_nn 3,
                      mul_nonneg hr_nn (pow_nonneg hr_nn (D * 2)),
                      sq_nonneg C]

private lemma gaussian_integral_eq_pi :
    ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  let f : ℝ × ℝ → ℝ := fun p => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)
  have hcomp :
      ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) =
        ∫ p : ℝ × ℝ, f p := by
    have hraw :=
      (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
        measurableEquivRealProd.symm.measurableEmbedding
        (fun z : ℂ => Real.exp (-‖z‖ ^ 2))
    symm
    calc
      ∫ p : ℝ × ℝ, f p
          = ∫ p : ℝ × ℝ, Real.exp (-‖(measurableEquivRealProd.symm p : ℂ)‖ ^ 2) := by
              refine integral_congr_ae ?_
              filter_upwards with p
              rcases p with ⟨x, y⟩
              change Real.exp (-x ^ 2) * Real.exp (-y ^ 2) =
                Real.exp (-‖({ re := x, im := y } : ℂ)‖ ^ 2)
              have hz : ‖({ re := x, im := y } : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
                calc
                  ‖({ re := x, im := y } : ℂ)‖ ^ 2 = Complex.normSq ({ re := x, im := y } : ℂ) := by
                    simpa [pow_two] using
                     (Complex.normSq_eq_norm_sq ({ re := x, im := y } : ℂ)).symm
                  _ = x ^ 2 + y ^ 2 := by simp [Complex.normSq, pow_two]
              rw [hz, show -(x ^ 2 + y ^ 2) = -x ^ 2 + -y ^ 2 by ring, Real.exp_add]
      _ = ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) := by simpa using hraw
  have hprod :
      ∫ p : ℝ × ℝ, f p =
        (∫ x : ℝ, Real.exp (-x ^ 2)) * ∫ y : ℝ, Real.exp (-y ^ 2) := by
    exact integral_prod_mul (fun x : ℝ => Real.exp (-x ^ 2))
      (fun y : ℝ => Real.exp (-y ^ 2))
  rw [hcomp, hprod]
  have hgauss : ∫ x : ℝ, Real.exp (-(1 : ℝ) * x ^ 2) = Real.sqrt Real.pi := by
    simpa using integral_gaussian (1 : ℝ)
  have hgauss' : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by simpa [one_mul] using hgauss
  calc
    (∫ x : ℝ, Real.exp (-x ^ 2)) * ∫ y : ℝ, Real.exp (-y ^ 2)
        = Real.sqrt Real.pi * Real.sqrt Real.pi := by simp [hgauss']
    _ = Real.pi := by nlinarith [Real.sq_sqrt Real.pi_pos.le]

private lemma gaussian_integral_normalized :
    (1 / Real.pi) * ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = 1 := by
  rw [gaussian_integral_eq_pi]
  field_simp [Real.pi_ne_zero]

private lemma norm_add_sq_le (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := parallelogram_law_with_norm ℂ a b
  nlinarith [sq_abs (‖a + b‖), sq_abs (‖a - b‖), sq_abs (‖a‖), sq_abs (‖b‖)]

private lemma integral_cauchy_schwarz {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α}
    {f g : α → ℝ}
    (_hf : Integrable f μ) (_hg : Integrable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  set A := ∫ x, f x ^ 2 ∂μ
  set B := ∫ x, f x * g x ∂μ
  set C := ∫ x, g x ^ 2 ∂μ
  have hA_nn : 0 ≤ A := integral_nonneg (fun _ => sq_nonneg _)
  have hC_nn : 0 ≤ C := integral_nonneg (fun _ => sq_nonneg _)
  have h_quad : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * B + C := by
    intro t
    have h0 : 0 ≤ ∫ x, (t * f x - g x) ^ 2 ∂μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    have h_eq : ∫ x, (t * f x - g x) ^ 2 ∂μ = t ^ 2 * A - 2 * t * B + C := by
      have hI1 : ∫ x, t ^ 2 * f x ^ 2 ∂μ = t ^ 2 * A := integral_const_mul _ _
      have hI2 : ∫ x, (-2 * t) * (f x * g x) ∂μ = (-2 * t) * B := integral_const_mul _ _
      have h_step1 : ∫ x, (t * f x - g x) ^ 2 ∂μ =
          ∫ x, (t ^ 2 * f x ^ 2 + (-2 * t) * (f x * g x)) ∂μ +
          ∫ x, g x ^ 2 ∂μ := by
        conv_lhs => rw [show (fun x => (t * f x - g x) ^ 2) =
            ((fun x => t ^ 2 * f x ^ 2 + (-2 * t) * (f x * g x)) +
             (fun x => g x ^ 2)) from by ext x; simp [Pi.add_apply]; ring]
        exact integral_add ((hf2.const_mul _).add (hfg.const_mul _)) hg2
      have h_step2 : ∫ x, (t ^ 2 * f x ^ 2 + (-2 * t) * (f x * g x)) ∂μ =
          ∫ x, t ^ 2 * f x ^ 2 ∂μ + ∫ x, (-2 * t) * (f x * g x) ∂μ := by
        conv_lhs => rw [show (fun x => t ^ 2 * f x ^ 2 + (-2 * t) * (f x * g x)) =
            ((fun x => t ^ 2 * f x ^ 2) + (fun x => (-2 * t) * (f x * g x))) from by
          ext x; simp [Pi.add_apply]]
        exact integral_add (hf2.const_mul _) (hfg.const_mul _)
      rw [h_step1, h_step2, hI1, hI2]
      ring
    linarith
  by_cases hA_zero : A = 0
  · have hf_ae : ∀ᵐ x ∂μ, f x = 0 := by
      have := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hf2).mp hA_zero
      filter_upwards [this] with x hx
      exact pow_eq_zero_iff (n := 2) (by omega) |>.mp hx
    have hB_zero : B = 0 := by
      have : (fun x => f x * g x) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
        filter_upwards [hf_ae] with x hx; simp [hx]
      simp [show B = ∫ x, f x * g x ∂μ from rfl,
            integral_congr_ae this]
    simp [hB_zero, hA_zero]
  · have hA_pos : 0 < A := lt_of_le_of_ne hA_nn (Ne.symm hA_zero)
    have h_opt := h_quad (B / A)
    have h_simp : (B / A) ^ 2 * A - 2 * (B / A) * B + C = C - B ^ 2 / A := by field_simp; ring
    rw [h_simp] at h_opt
    rwa [sub_nonneg, div_le_iff₀ hA_pos, mul_comm] at h_opt

private lemma integrableOn_polar_const (u : ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ => p.1 * (u ^ 2 * Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  have hcont : Continuous (fun p : ℝ × ℝ => p.1 * (u ^ 2 * Real.exp (-p.1 ^ 2))) :=
    Continuous.mul continuous_fst
      (Continuous.mul continuous_const
        (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))
  rw [IntegrableOn, ← Measure.prod_restrict (Set.Ioi 0) (Set.Ioo (-Real.pi) Real.pi)]
  rw [integrable_prod_iff hcont.aestronglyMeasurable]
  constructor
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply Filter.Eventually.of_forall
    intro r hr
    have hcont_theta : Continuous (fun θ : ℝ => r * (u ^ 2 * Real.exp (-r ^ 2))) := by continuity
    exact (hcont_theta.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  · set bound := fun r : ℝ => T * (u ^ 2 * (|r| ^ 1 * Real.exp (-r ^ 2)))
    have hbound_def : bound = fun r : ℝ => (T * u ^ 2) * (|r| ^ 1 * Real.exp (-r ^ 2)) := by
      funext r
      unfold bound
      ring
    apply Integrable.mono'
      (g := bound)
    · rw [hbound_def]
      exact ((integrable_abs_pow_mul_exp_neg_sq 1).const_mul (T * u ^ 2)).restrict
    · have hcont_int : Continuous (fun r : ℝ =>
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            ‖r * (u ^ 2 * Real.exp (-r ^ 2))‖) :=
        continuous_parametric_integral_of_continuous hcont.norm isCompact_Icc
      have hIoo_eq_Icc : ∀ r, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖r * (u ^ 2 * Real.exp (-r ^ 2))‖ =
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            ‖r * (u ^ 2 * Real.exp (-r ^ 2))‖ := by
        intro r
        exact (integral_Icc_eq_integral_Ioo).symm
      simp_rw [hIoo_eq_Icc]
      exact hcont_int.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · apply (ae_restrict_iff' measurableSet_Ioi).mpr
      apply Filter.Eventually.of_forall
      intro r hr
      simp only [Set.mem_Ioi] at hr
      rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Ioo
        (fun _ _ => norm_nonneg _))]
      have hnorm_eq : ∀ y : ℝ,
          ‖(r, y).1 * (u ^ 2 * Real.exp (-(r, y).1 ^ 2))‖ =
            r * (u ^ 2 * Real.exp (-r ^ 2)) := by
        intro y
        rw [Real.norm_of_nonneg]
        exact mul_nonneg (le_of_lt hr) (mul_nonneg (sq_nonneg u) (le_of_lt (Real.exp_pos _)))
      rw [setIntegral_congr_fun measurableSet_Ioo (by
        intro y hy
        exact hnorm_eq y)]
      have hnn :
          0 ≤ r * (u ^ 2 * Real.exp (-r ^ 2)) :=
        mul_nonneg (le_of_lt hr) (mul_nonneg (sq_nonneg u) (le_of_lt (Real.exp_pos _)))
      calc
        ∫ θ in Set.Ioo (-Real.pi) Real.pi, r * (u ^ 2 * Real.exp (-r ^ 2))
            = T * (r * (u ^ 2 * Real.exp (-r ^ 2))) := by
                rw [setIntegral_const]
                simp only [smul_eq_mul]
                rw [Measure.real, Real.volume_Ioo,
                  show Real.pi - (-Real.pi) = T by simp [T]; ring,
                  ENNReal.toReal_ofReal T_pos.le]
        _ ≤ bound r := by
            unfold bound
            rw [abs_of_pos hr]
            ring_nf
            exact le_rfl

private lemma integrableOn_polar_const_add {D : ℕ} (a : Fin D → ℂ) (c : ℂ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 * (‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  rw [IntegrableOn]
  let μ : Measure (ℝ × ℝ) :=
    (volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
  have hconst :
      Integrable (fun p : ℝ × ℝ => p.1 * (‖c‖ ^ 2 * Real.exp (-p.1 ^ 2))) μ :=
    integrableOn_polar_const ‖c‖
  have hnorm :
      Integrable (fun p : ℝ × ℝ =>
        p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2))) μ := integrableOn_polar_norm a
  set g : ℝ × ℝ → ℝ := fun p =>
    2 * (p.1 * (‖c‖ ^ 2 * Real.exp (-p.1 ^ 2))) +
      2 * (p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2)))
  have hg : Integrable g μ := by
    refine (hconst.const_mul 2).add ?_
    exact hnorm.const_mul 2
  have hcont : Continuous (fun p : ℝ × ℝ =>
      p.1 * (‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2))) :=
    Continuous.mul continuous_fst (Continuous.mul
      ((continuous_const.add (continuous_polyEvalCircle_comp a)).norm.pow 2)
      (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))
  refine Integrable.mono' hg ?_ ?_
  · exact hcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · apply (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioo)).mpr
    apply Filter.Eventually.of_forall
    intro p hp
    rcases hp with ⟨hr, hθ⟩
    simp only [Set.mem_Ioi, Set.mem_Ioo] at hr hθ
    rw [Real.norm_of_nonneg]
    · set q := polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)
      have hbase : ‖c + q‖ ^ 2 ≤ 2 * ‖c‖ ^ 2 + 2 * ‖q‖ ^ 2 := by simpa [q] using norm_add_sq_le c q
      have hmul :
          p.1 * (‖c + q‖ ^ 2 * Real.exp (-p.1 ^ 2))
            ≤ p.1 * ((2 * ‖c‖ ^ 2 + 2 * ‖q‖ ^ 2) * Real.exp (-p.1 ^ 2)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbase (le_of_lt (Real.exp_pos _)))
          (le_of_lt hr)
      calc
        p.1 * (‖c + q‖ ^ 2 * Real.exp (-p.1 ^ 2))
            ≤ p.1 * ((2 * ‖c‖ ^ 2 + 2 * ‖q‖ ^ 2) * Real.exp (-p.1 ^ 2)) := hmul
        _ = g p := by
            unfold g q
            ring
    · exact mul_nonneg (le_of_lt hr)
        (mul_nonneg (sq_nonneg ‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖)
          (le_of_lt (Real.exp_pos _)))

private lemma integrableOn_polar_real_const_add {D : ℕ} (a : Fin D → ℂ) (u : ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 * (‖(u : ℂ) + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) :=
  integrableOn_polar_const_add a (u : ℂ)

private lemma radial_gaussian_integral (n : ℕ) :
    2 * ∫ r in Set.Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-r ^ 2) =
      (n.factorial : ℝ) := by
  have hp : (0 : ℝ) < 2 := two_pos
  have hq : (-1 : ℝ) < (2 * (n : ℝ) + 1) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have pow_eq : ∀ (r : ℝ), r ∈ Set.Ioi (0 : ℝ) →
      r ^ (2 * n + 1) * Real.exp (-r ^ 2) =
      r ^ (2 * (n : ℝ) + 1) * Real.exp (-r ^ (2 : ℝ)) := by
    intro r _
    congr 1
    · rw [← rpow_natCast r (2 * n + 1)]
      congr 1
      push_cast
      ring
    · congr 1
      congr 1
      rw [← rpow_natCast r 2]
      norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi pow_eq]
  rw [integral_rpow_mul_exp_neg_rpow hp hq]
  have h1 : (2 * (n : ℝ) + 1 + 1) / 2 = ↑n + 1 := by ring
  rw [h1, Real.Gamma_nat_eq_factorial]
  ring

private lemma norm_polyEval_eq_norm_polyEvalCircle {D : ℕ} (a : Fin D → ℂ) (r θ : ℝ) :
    ‖polyEval a (Complex.polarCoord.symm (r, θ))‖ =
      ‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ := by rw [polyEval_polar_eq_polyEvalCircle]

private lemma fockNorm_polar_local {D : ℕ} (a : Fin D → ℂ) :
    (1 / Real.pi) * ∫ z : ℂ, ‖polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
    2 * ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
        ∂AddCircle.haarAddCircle) := by
  rw [show (∫ z : ℂ, ‖polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) =
    (∫ p in polarCoord.target, p.1 • (‖polyEval a (Complex.polarCoord.symm p)‖ ^ 2 *
      Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2))
    ) from (Complex.integral_comp_polarCoord_symm _).symm]
  rw [polarCoord_target]
  have integrand_rw : ∀ p : ℝ × ℝ,
      p.1 • (‖polyEval a (Complex.polarCoord.symm p)‖ ^ 2 *
        Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2)) =
      p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2)) := by
    intro ⟨r, θ⟩
    simp only [smul_eq_mul, norm_polyEval_eq_norm_polyEvalCircle, Complex.norm_polarCoord_symm,
      sq_abs]
  simp_rw [integrand_rw]
  have hint : IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := integrableOn_polar_norm a
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod _ hint]
  simp only []
  have inner_eq : ∀ r : ℝ,
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2))) =
      T * (r * Real.exp (-r ^ 2) *
        ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    intro r
    have h1 : ∀ θ : ℝ,
        r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2)) =
          (r * Real.exp (-r ^ 2)) *
            ‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 := by
      intro θ
      ring
    simp_rw [h1]
    rw [MeasureTheory.integral_const_mul]
    have := integral_Ioo_eq_T_smul_haar (fun t : AddCircle T =>
      ‖polyEvalCircle a r t‖ ^ 2)
    simp only [smul_eq_mul] at this
    rw [show (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2) =
        (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (fun t : AddCircle T => ‖polyEvalCircle a r t‖ ^ 2) (QuotientAddGroup.mk θ))
        from by rfl]
    rw [this]
    ring
  simp_rw [inner_eq]
  rw [MeasureTheory.integral_const_mul]
  have hT_eq : (1 / Real.pi) * T = 2 := by
    simp only [T]
    field_simp
  rw [← mul_assoc, hT_eq]

lemma gaussian_integral_const_add_polyEval {D : ℕ} (a : Fin D → ℂ) (c : ℂ) :
    (1 / Real.pi) * ∫ z : ℂ, ‖c + polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      ‖c‖ ^ 2 + fockNormSq a := by
  rw [show (∫ z : ℂ, ‖c + polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) =
    (∫ p in polarCoord.target, p.1 • (‖c + polyEval a (Complex.polarCoord.symm p)‖ ^ 2 *
      Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2))
    ) from (Complex.integral_comp_polarCoord_symm _).symm]
  rw [polarCoord_target]
  have integrand_rw : ∀ p : ℝ × ℝ,
      p.1 • (‖c + polyEval a (Complex.polarCoord.symm p)‖ ^ 2 *
        Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2)) =
      p.1 * (‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2)) := by
    intro ⟨r, θ⟩
    simp only [smul_eq_mul, polyEval_polar_eq_polyEvalCircle, Complex.norm_polarCoord_symm, sq_abs]
  simp_rw [integrand_rw]
  have hint : IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 * (‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := integrableOn_polar_const_add a c
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod _ hint]
  simp only []
  have inner_eq : ∀ r : ℝ,
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * (‖c + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2))) =
      T * (r * Real.exp (-r ^ 2) *
        ∫ t : AddCircle T, ‖c + polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    intro r
    have h1 : ∀ θ : ℝ,
        r * (‖c + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2)) =
          (r * Real.exp (-r ^ 2)) *
            ‖c + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 := by
      intro θ
      ring
    simp_rw [h1]
    rw [MeasureTheory.integral_const_mul]
    have := integral_Ioo_eq_T_smul_haar (fun t : AddCircle T =>
      ‖c + polyEvalCircle a r t‖ ^ 2)
    simp only [smul_eq_mul] at this
    rw [show (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖c + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2) =
        (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (fun t : AddCircle T => ‖c + polyEvalCircle a r t‖ ^ 2)
            (QuotientAddGroup.mk θ))
        from by rfl]
    rw [this]
    ring
  simp_rw [inner_eq, integral_const_add_polyEvalCircle_sq]
  set whole : ℝ → ℝ := fun r =>
    T * (r * Real.exp (-r ^ 2) *
      (‖c‖ ^ 2 + ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle))
  set first : ℝ → ℝ := fun r => T * (r * Real.exp (-r ^ 2) * ‖c‖ ^ 2)
  set second : ℝ → ℝ := fun r =>
    T * (r * Real.exp (-r ^ 2) *
      ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle)
  have hwhole_eq : whole = fun r : ℝ =>
      ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * (‖c + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
          Real.exp (-r ^ 2)) := by
    funext r
    rw [inner_eq]
    unfold whole
    rw [integral_const_add_polyEvalCircle_sq]
  have hwhole_int : Integrable whole (volume.restrict (Set.Ioi 0)) := by
    have hcont_add : Continuous (fun p : ℝ × ℝ =>
        p.1 * (‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2))) :=
      Continuous.mul continuous_fst (Continuous.mul
        ((continuous_const.add (continuous_polyEvalCircle_comp a)).norm.pow 2)
        (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))
    have hint' := integrableOn_polar_const_add a c
    rw [IntegrableOn, ← Measure.prod_restrict (Set.Ioi 0) (Set.Ioo (-Real.pi) Real.pi)] at hint'
    rw [integrable_prod_iff hcont_add.aestronglyMeasurable] at hint'
    refine hint'.2.congr ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with r hr
    have hnorm_eq : ∀ y : ℝ,
        ‖(r, y).1 * (‖c + polyEvalCircle a (r, y).1 (↑(r, y).2)‖ ^ 2 *
          Real.exp (-(r, y).1 ^ 2))‖ =
          r * (‖c + polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 *
            Real.exp (-r ^ 2)) := by
      intro y
      rw [Real.norm_of_nonneg]
      exact mul_nonneg (le_of_lt hr)
        (mul_nonneg (sq_nonneg ‖c + polyEvalCircle a r (QuotientAddGroup.mk y)‖)
          (le_of_lt (Real.exp_pos _)))
    rw [setIntegral_congr_fun measurableSet_Ioo (by
      intro y hy
      exact hnorm_eq y)]
    exact (congrFun hwhole_eq r).symm
  have hfirst_int : Integrable first (volume.restrict (Set.Ioi 0)) := by
    unfold first
    have : IntegrableOn (fun r : ℝ => (T * ‖c‖ ^ 2) * (r ^ 1 * Real.exp (-r ^ 2)))
        (Set.Ioi 0) volume := (integrable_pow_mul_exp_neg_sq 1).integrableOn.const_mul (T * ‖c‖ ^ 2)
    simpa [IntegrableOn, mul_assoc, mul_left_comm, mul_comm, pow_one] using this
  have hsum : whole = first + second := by
    funext r
    simp [whole, first, second]
    ring
  have hsecond_int : Integrable second (volume.restrict (Set.Ioi 0)) := by
    rw [show second = whole - first by
      funext r
      simp [whole, first, second]
      ring]
    exact hwhole_int.sub hfirst_int
  rw [show (∫ r in Set.Ioi (0 : ℝ), whole r) =
      ∫ r in Set.Ioi (0 : ℝ), (first + second) r by rw [hsum]]
  rw [show (∫ r in Set.Ioi (0 : ℝ), (first + second) r) =
      ∫ r in Set.Ioi (0 : ℝ), first r + second r by rfl]
  rw [integral_add hfirst_int hsecond_int]
  have hfirst_eval :
      (1 / Real.pi) * ∫ r in Set.Ioi (0 : ℝ), first r = ‖c‖ ^ 2 := by
    unfold first
    rw [show (fun r : ℝ => T * (r * Real.exp (-r ^ 2) * ‖c‖ ^ 2)) =
      fun r => (T * (r * Real.exp (-r ^ 2))) * ‖c‖ ^ 2 by
        ext r
        ring]
    rw [MeasureTheory.integral_mul_const]
    have hT_eq : (1 / Real.pi) * T = 2 := by
      simp only [T]
      field_simp
    have hrad : 2 * ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) = 1 := by
      simpa using radial_gaussian_integral 0
    calc
      (1 / Real.pi) * ((∫ r in Set.Ioi (0 : ℝ), T * (r * Real.exp (-r ^ 2)) ∂volume) * ‖c‖ ^ 2)
          = (((1 / Real.pi) * T) *
            (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) ∂volume)) * ‖c‖ ^ 2 := by
              rw [integral_const_mul]
              ring
      _ = 2 * (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) ∂volume) * ‖c‖ ^ 2 := by rw [hT_eq]
      _ = ‖c‖ ^ 2 := by nlinarith
  have hsecond_eval :
      (1 / Real.pi) * ∫ r in Set.Ioi (0 : ℝ), second r = fockNormSq a := by
    unfold second
    rw [MeasureTheory.integral_const_mul]
    have hT_eq : (1 / Real.pi) * T = 2 := by
      simp only [T]
      field_simp
    calc
      (1 / Real.pi) * (T * ∫ r in Set.Ioi (0 : ℝ),
          r * Real.exp (-r ^ 2) *
            ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle)
          = ((1 / Real.pi) * T) *
              ∫ r in Set.Ioi (0 : ℝ),
                r * Real.exp (-r ^ 2) *
                  ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
                    ∂AddCircle.haarAddCircle := by ring
      _ = 2 * ∫ r in Set.Ioi (0 : ℝ),
            r * Real.exp (-r ^ 2) *
              ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
                ∂AddCircle.haarAddCircle := by rw [hT_eq]
      _ = (1 / Real.pi) * ∫ z : ℂ, ‖polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
            simpa using (fockNorm_polar_local a).symm
      _ = fockNormSq a := fockNorm_eq_gaussian_integral a
  have hfinal :
      (1 / Real.pi) * (∫ r in Set.Ioi (0 : ℝ), first r) +
        (1 / Real.pi) * ∫ r in Set.Ioi (0 : ℝ), second r = ‖c‖ ^ 2 + fockNormSq a := by
    rw [hfirst_eval, hsecond_eval]
  have hparen2 :
      (1 / Real.pi) *
          ((∫ r in Set.Ioi (0 : ℝ), first r) +
            ∫ r in Set.Ioi (0 : ℝ), second r) =
        (1 / Real.pi) * (∫ r in Set.Ioi (0 : ℝ), first r) +
          (1 / Real.pi) * ∫ r in Set.Ioi (0 : ℝ), second r := by ring
  exact hparen2.trans hfinal

private lemma gaussian_integral_real_const_add_polyEval {D : ℕ} (a : Fin D → ℂ) (u : ℝ) :
    (1 / Real.pi) * ∫ z : ℂ, ‖(u : ℂ) + polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      u ^ 2 + fockNormSq a := by simpa using gaussian_integral_const_add_polyEval a (u : ℂ)

private lemma integrable_gaussian_sq_real_const_add_polyEval {D : ℕ}
    (a : Fin D → ℂ) (u : ℝ) :
    Integrable
      (fun z : ℂ => ‖(u : ℂ) + polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))
      volume := by
  let F : ℂ → ℝ := fun z => ‖(u : ℂ) + polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
  have hF_cont : Continuous F := by
    unfold F
    exact Continuous.mul
      ((continuous_const.add (continuous_polyEval a)).norm.pow 2)
      (Real.continuous_exp.comp (Continuous.neg (continuous_norm.pow 2)))
  have hF_meas : AEStronglyMeasurable F volume := hF_cont.aestronglyMeasurable
  have hF_nonneg : 0 ≤ᵐ[volume] F := Filter.Eventually.of_forall (fun z => by
    unfold F
    exact mul_nonneg (sq_nonneg ‖(u : ℂ) + polyEval a z‖) (le_of_lt (Real.exp_pos _)))
  refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hF_meas hF_nonneg).1 ?_
  rw [← Complex.lintegral_comp_polarCoord_symm (fun z => ENNReal.ofReal (F z))]
  rw [polarCoord_target]
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
  let G : ℝ × ℝ → ℝ := fun p =>
    p.1 * (‖(u : ℂ) + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
      Real.exp (-p.1 ^ 2))
  have hFG :
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • ENNReal.ofReal (F (Complex.polarCoord.symm p))) =ᵐ[
        (volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)]
      fun p => ENNReal.ofReal (G p) := by
    apply (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioo)).mpr
    filter_upwards with p hp
    rcases p with ⟨r, θ⟩
    rcases hp with ⟨hr, hθ⟩
    simp only [Set.mem_Ioi, Set.mem_Ioo] at hr hθ
    unfold F G
    simp only [smul_eq_mul]
    have hr_abs : |r| = r := abs_of_pos hr
    have hnorm_nonneg : 0 ≤ ‖(u : ℂ) + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 :=
      sq_nonneg _
    rw [polyEval_polar_eq_polyEvalCircle, Complex.norm_polarCoord_symm, hr_abs]
    rw [ENNReal.ofReal_mul (le_of_lt hr), ENNReal.ofReal_mul hnorm_nonneg]
  rw [lintegral_congr_ae hFG]
  have hG_int :
      Integrable G ((volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)) := by
    simpa [G, IntegrableOn] using integrableOn_polar_real_const_add a u
  have hG_nonneg :
      0 ≤ᵐ[(volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)] G := by
    apply (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioo)).mpr
    filter_upwards with p hp
    rcases hp with ⟨hr, hθ⟩
    simp only [Set.mem_Ioi, Set.mem_Ioo] at hr hθ
    unfold G
    exact mul_nonneg (le_of_lt hr)
      (mul_nonneg
        (sq_nonneg ‖(u : ℂ) + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖)
        (le_of_lt (Real.exp_pos _)))
  exact ((MeasureTheory.hasFiniteIntegral_iff_ofReal hG_nonneg).1 hG_int.hasFiniteIntegral).ne

private def gaussianWeight (z : ℂ) : ℝ :=
  (1 / Real.pi) * Real.exp (-‖z‖ ^ 2)

private def gaussianMeasure : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (gaussianWeight z))

private lemma measurable_gaussianWeight : Measurable gaussianWeight := by
  unfold gaussianWeight
  fun_prop

private lemma gaussianWeight_ae_lt_top :
    ∀ᵐ z : ℂ ∂volume, ENNReal.ofReal (gaussianWeight z) < ∞ := by
  filter_upwards with z
  simp [gaussianWeight]

private lemma integrable_gaussianWeight :
    Integrable gaussianWeight volume := by
  let a : Fin 0 → ℂ := fun i => nomatch i
  convert (integrable_gaussian_sq_real_const_add_polyEval a 1).const_mul (1 / Real.pi) using 1
  ext z
  simp [gaussianWeight, polyEval]

private lemma gaussianMeasure_isFinite : IsFiniteMeasure gaussianMeasure := by
  simpa [gaussianMeasure, gaussianWeight] using
    (MeasureTheory.isFiniteMeasure_withDensity_ofReal
      (μ := (volume : Measure ℂ)) integrable_gaussianWeight.hasFiniteIntegral)

private lemma integral_gaussianMeasure_eq (f : ℂ → ℝ) :
    ∫ z, f z ∂gaussianMeasure =
      (1 / Real.pi) * ∫ z, f z * Real.exp (-‖z‖ ^ 2) := by
  rw [gaussianMeasure,
    integral_withDensity_eq_integral_toReal_smul
      measurable_gaussianWeight.ennreal_ofReal gaussianWeight_ae_lt_top]
  calc
    ∫ z : ℂ, (ENNReal.ofReal (gaussianWeight z)).toReal • f z
        = ∫ z : ℂ, gaussianWeight z * f z := by
            apply integral_congr_ae
            filter_upwards with z
            have hgw : 0 ≤ gaussianWeight z := by
              unfold gaussianWeight
              positivity
            simp [smul_eq_mul, hgw]
    _ = ∫ z : ℂ, gaussianWeight z * f z
        := rfl
    _
        = ∫ z : ℂ, (1 / Real.pi) * (f z * Real.exp (-‖z‖ ^ 2)) := by
            apply integral_congr_ae
            filter_upwards with z
            unfold gaussianWeight
            ring
    _ = (1 / Real.pi) * ∫ z : ℂ, f z * Real.exp (-‖z‖ ^ 2) := by rw [integral_const_mul]

private lemma integral_one_gaussianMeasure :
    ∫ _ : ℂ, (1 : ℝ) ∂gaussianMeasure = 1 := by
  calc
    ∫ z, (1 : ℝ) ∂gaussianMeasure
        = (1 / Real.pi) * ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) := by
            simpa using integral_gaussianMeasure_eq (fun _ : ℂ => (1 : ℝ))
    _ = 1 := gaussian_integral_normalized

private lemma integrable_sq_gaussianMeasure_real_const_add_polyEval {D : ℕ}
    (a : Fin D → ℂ) (u : ℝ) :
    Integrable (fun z : ℂ => ‖(u : ℂ) + polyEval a z‖ ^ 2) gaussianMeasure := by
  rw [gaussianMeasure]
  refine (MeasureTheory.integrable_withDensity_iff_integrable_smul'
    (μ := (volume : Measure ℂ))
    (f := fun z => ENNReal.ofReal (gaussianWeight z))
    measurable_gaussianWeight.ennreal_ofReal gaussianWeight_ae_lt_top).2 ?_
  convert (integrable_gaussian_sq_real_const_add_polyEval a u).const_mul (1 / Real.pi) using 1
  ext z
  have hgw : 0 ≤ gaussianWeight z := by
    unfold gaussianWeight
    positivity
  rw [show (ENNReal.ofReal (gaussianWeight z)).toReal = gaussianWeight z by simp [hgw]]
  simp [gaussianWeight, smul_eq_mul]
  ring_nf

private lemma integrable_sq_gaussianMeasure_rho_real_const_add_polyEval {D : ℕ}
    (a : Fin D → ℂ) (u : ℝ) :
    Integrable (fun z : ℂ => rho ((u : ℂ) + polyEval a z) ^ 2) gaussianMeasure := by
  haveI : IsFiniteMeasure gaussianMeasure := gaussianMeasure_isFinite
  refine MeasureTheory.Integrable.mono'
    (integrable_sq_gaussianMeasure_real_const_add_polyEval a u)
    (((rho_continuous.comp
      (continuous_const.add (continuous_polyEval a))).pow 2).aestronglyMeasurable) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hle := rho_le_norm ((u : ℂ) + polyEval a z)
  have hrho_nonneg : 0 ≤ rho ((u : ℂ) + polyEval a z) := abs_nonneg _
  have hnorm_nonneg : 0 ≤ ‖(u : ℂ) + polyEval a z‖ := norm_nonneg _
  nlinarith

private lemma integrable_sq_gaussianMeasure_norm_add_one_real_const_add_polyEval {D : ℕ}
    (a : Fin D → ℂ) (u : ℝ) :
    Integrable
      (fun z : ℂ => (‖(1 : ℂ) + ((u : ℂ) + polyEval a z)‖ + 1) ^ 2)
      gaussianMeasure := by
  haveI : IsFiniteMeasure gaussianMeasure := gaussianMeasure_isFinite
  refine MeasureTheory.Integrable.mono'
    ((MeasureTheory.integrable_const (8 : ℝ)).add
      ((integrable_sq_gaussianMeasure_real_const_add_polyEval a u).const_mul 2))
    ((((continuous_const.add (continuous_const.add (continuous_polyEval a))).norm.add
      continuous_const).pow 2).aestronglyMeasurable) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have htri : ‖(1 : ℂ) + ((u : ℂ) + polyEval a z)‖ + 1 ≤ 2 + ‖(u : ℂ) + polyEval a z‖ := by
    have hnorm := norm_add_le (1 : ℂ) ((u : ℂ) + polyEval a z)
    calc
      ‖(1 : ℂ) + ((u : ℂ) + polyEval a z)‖ + 1 ≤ (1 + ‖(u : ℂ) + polyEval a z‖) + 1 := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hnorm 1
      _ = 2 + ‖(u : ℂ) + polyEval a z‖ := by ring
  have hsq :
      (2 + ‖(u : ℂ) + polyEval a z‖) ^ 2 ≤
        8 + 2 * ‖(u : ℂ) + polyEval a z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖(u : ℂ) + polyEval a z‖ - 2)]
  have htri_sq : (‖(1 : ℂ) + ((u : ℂ) + polyEval a z)‖ + 1) ^ 2 ≤
      (2 + ‖(u : ℂ) + polyEval a z‖) ^ 2 := by
    have hnn1 : 0 ≤ ‖(1 : ℂ) + ((u : ℂ) + polyEval a z)‖ + 1 := by positivity
    have hnn2 : 0 ≤ 2 + ‖(u : ℂ) + polyEval a z‖ := by positivity
    nlinarith
  exact le_trans htri_sq hsq

private lemma integrable_of_sq_gaussian {f : ℂ → ℝ}
    (hfm : AEStronglyMeasurable f gaussianMeasure)
    (hf2 : Integrable (fun z => f z ^ 2) gaussianMeasure) :
    Integrable f gaussianMeasure := by
  haveI : IsFiniteMeasure gaussianMeasure := gaussianMeasure_isFinite
  refine MeasureTheory.Integrable.mono'
    ((MeasureTheory.integrable_const (1 : ℝ)).add hf2) hfm ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  have hbound : |f z| ≤ |f z| ^ 2 + 1 := by nlinarith [sq_nonneg (|f z| - (1 / 2 : ℝ))]
  simpa [sq_abs, add_comm, add_left_comm, add_assoc] using hbound

private lemma integrable_mul_of_sq_gaussian {f g : ℂ → ℝ}
    (hfgm : AEStronglyMeasurable (fun z => f z * g z) gaussianMeasure)
    (hf2 : Integrable (fun z => f z ^ 2) gaussianMeasure)
    (hg2 : Integrable (fun z => g z ^ 2) gaussianMeasure) :
    Integrable (fun z => f z * g z) gaussianMeasure := by
  refine MeasureTheory.Integrable.mono' (hf2.add hg2) hfgm ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  rw [abs_mul]
  have hbound : |f z| * |g z| ≤ |f z| ^ 2 + |g z| ^ 2 := by nlinarith [sq_nonneg (|f z| - |g z|)]
  simpa [sq_abs] using hbound

private lemma gaussian_l1_sq_le {f : ℂ → ℝ}
    (hfm : AEStronglyMeasurable f gaussianMeasure)
    (hf2 : Integrable (fun z => f z ^ 2) gaussianMeasure) :
    (∫ z, f z ∂gaussianMeasure) ^ 2 ≤ ∫ z, f z ^ 2 ∂gaussianMeasure := by
  haveI : IsFiniteMeasure gaussianMeasure := gaussianMeasure_isFinite
  have hf : Integrable f gaussianMeasure := integrable_of_sq_gaussian hfm hf2
  have h1 : Integrable (fun _ : ℂ => (1 : ℝ)) gaussianMeasure := MeasureTheory.integrable_const 1
  have h1sq : Integrable (fun _ : ℂ => (1 : ℝ) ^ 2) gaussianMeasure := by
    simpa only [one_pow] using h1
  have hfg : Integrable (fun z => f z * 1) gaussianMeasure := by simpa using hf
  have hcs := integral_cauchy_schwarz hf h1 hf2 h1sq hfg
  have hmass : gaussianMeasure.real Set.univ = 1 := by simpa using integral_one_gaussianMeasure
  simpa [hmass] using hcs

private lemma rho_factor (w : ℂ) :
    |‖(1 : ℂ) + w‖ ^ 2 - 1| = rho w * (‖(1 : ℂ) + w‖ + 1) := by
  have hnn : 0 ≤ ‖(1 : ℂ) + w‖ + 1 := by positivity
  unfold rho
  rw [show ‖(1 : ℂ) + w‖ ^ 2 - 1 =
      (‖(1 : ℂ) + w‖ - 1) * (‖(1 : ℂ) + w‖ + 1) by ring]
  rw [abs_mul, abs_of_nonneg hnn]

private lemma rho_const_add_le (u : ℝ) (w : ℂ) :
    rho w ≤ |u| + rho ((u : ℂ) + w) := by
  unfold rho
  have hnorm :
      |‖(1 : ℂ) + w‖ - ‖(1 : ℂ) + ((u : ℂ) + w)‖| ≤ |u| := by
    calc
      |‖(1 : ℂ) + w‖ - ‖(1 : ℂ) + ((u : ℂ) + w)‖|
          ≤ ‖((1 : ℂ) + w) - ((1 : ℂ) + ((u : ℂ) + w))‖ := abs_norm_sub_norm_le _ _
      _ = |u| := by simp [Complex.norm_real]
  have htri :
      |‖(1 : ℂ) + w‖ - 1| ≤
        |‖(1 : ℂ) + w‖ - ‖(1 : ℂ) + ((u : ℂ) + w)‖| +
          |‖(1 : ℂ) + ((u : ℂ) + w)‖ - 1| := by
    simpa using abs_sub_le ‖(1 : ℂ) + w‖ ‖(1 : ℂ) + ((u : ℂ) + w)‖ 1
  exact le_trans htri (add_le_add hnorm le_rfl)

/-- The Gaussian integral of `(rho ∘ q.eval)²` is bounded by `(|u| + m)²`, where
`R` is the (nonnegative) `rho`-magnitude of the recentred polynomial and `m` its
Gaussian `L²` norm.  Phrased generically over the magnitude functions to keep the
elaboration cost of the main estimate within the default heartbeat budget. -/
private lemma rho_centered_integral_bound
    {G R : ℂ → ℝ} {u m rq2 : ℝ}
    (hR_nonneg : ∀ z, 0 ≤ R z)
    (hG_nonneg : ∀ z, 0 ≤ G z)
    (hRm : AEStronglyMeasurable R gaussianMeasure)
    (hR_int : Integrable R gaussianMeasure)
    (hR2_int : Integrable (fun z => R z ^ 2) gaussianMeasure)
    (hG2_int : Integrable (fun z => G z ^ 2) gaussianMeasure)
    (hpt : ∀ z, G z ≤ |u| + R z)
    (hrq_mu : ∫ z, G z ^ 2 ∂gaussianMeasure = rq2)
    (hm_mu : ∫ z, R z ^ 2 ∂gaussianMeasure = m ^ 2)
    (hR_l1_le : ∫ z, R z ∂gaussianMeasure ≤ m) :
    rq2 ≤ (|u| + m) ^ 2 := by
  haveI : IsFiniteMeasure gaussianMeasure := gaussianMeasure_isFinite
  have hsum_sq_int : Integrable (fun z => (|u| + R z) ^ 2) gaussianMeasure := by
    refine MeasureTheory.Integrable.mono'
      ((MeasureTheory.integrable_const (2 * |u| ^ 2)).add (hR2_int.const_mul 2))
      ((hRm.const_add |u|).pow 2) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hmul : 2 * |u| * R z ≤ |u| ^ 2 + R z ^ 2 := by nlinarith [sq_nonneg (|u| - R z)]
    have hsq : (|u| + R z) ^ 2 ≤ 2 * |u| ^ 2 + 2 * R z ^ 2 := by nlinarith [hmul]
    exact hsq
  have hmono : rq2 ≤ ∫ z, (|u| + R z) ^ 2 ∂gaussianMeasure := by
    rw [← hrq_mu]
    refine MeasureTheory.integral_mono_ae hG2_int hsum_sq_int ?_
    refine Filter.Eventually.of_forall ?_
    intro z
    have hsum_nn : 0 ≤ |u| + R z := by nlinarith [abs_nonneg u, hR_nonneg z]
    nlinarith [hpt z, hG_nonneg z, hsum_nn]
  have hsum_eval :
      ∫ z, (|u| + R z) ^ 2 ∂gaussianMeasure =
        |u| ^ 2 + 2 * |u| * ∫ z, R z ∂gaussianMeasure + m ^ 2 := by
    have hmass : gaussianMeasure.real Set.univ = 1 := by simpa using integral_one_gaussianMeasure
    have habs_sq : |u| ^ 2 = u ^ 2 := by rw [sq_abs]
    have hsplit1 :
        ∫ z, (u ^ 2 + 2 * |u| * R z + R z ^ 2) ∂gaussianMeasure =
          ∫ z, (u ^ 2 + 2 * |u| * R z) ∂gaussianMeasure +
            ∫ z, R z ^ 2 ∂gaussianMeasure := by
      simpa [add_assoc] using
        (integral_add ((MeasureTheory.integrable_const (u ^ 2)).add
          (hR_int.const_mul (2 * |u|))) hR2_int)
    have hsplit2 :
        ∫ z, (u ^ 2 + 2 * |u| * R z) ∂gaussianMeasure =
          ∫ z, (u ^ 2 : ℝ) ∂gaussianMeasure +
            ∫ z, 2 * |u| * R z ∂gaussianMeasure := by
      simpa using
        (integral_add (MeasureTheory.integrable_const (u ^ 2))
          (hR_int.const_mul (2 * |u|)))
    calc
      ∫ z, (|u| + R z) ^ 2 ∂gaussianMeasure
          = ∫ z, (u ^ 2 + 2 * |u| * R z + R z ^ 2) ∂gaussianMeasure := by
              apply integral_congr_ae
              filter_upwards with z
              calc
                (|u| + R z) ^ 2 = |u| ^ 2 + 2 * |u| * R z + R z ^ 2 := by ring
                _ = u ^ 2 + 2 * |u| * R z + R z ^ 2 := by rw [sq_abs]
      _ = ∫ z, (u ^ 2 + 2 * |u| * R z) ∂gaussianMeasure +
            ∫ z, R z ^ 2 ∂gaussianMeasure := hsplit1
      _ = |u| ^ 2 + 2 * |u| * ∫ z, R z ∂gaussianMeasure + m ^ 2 := by
            rw [hsplit2, integral_const, integral_const_mul, hm_mu]
            simp [hmass, habs_sq]
  have hsum_bound : ∫ z, (|u| + R z) ^ 2 ∂gaussianMeasure ≤ (|u| + m) ^ 2 := by
    rw [hsum_eval]
    nlinarith [hR_l1_le, abs_nonneg u]
  exact le_trans hmono hsum_bound

/-- The scalar lower bound `|2u + x2| ≤ ∫ rho(u + polyEval a) · (‖1+u+polyEval a‖+1)`
underlying the Cauchy–Schwarz step.  Factored out of the main estimate (and the
integrability/`fockNormSq` rewrites) to respect the proof size limit. -/
private lemma scalar_raw_bound {D : ℕ} (a : Fin D → ℂ) {u x2 q2 : ℝ}
    (hq2_fock : q2 = fockNormSq a) (hx2_eq : x2 = u ^ 2 + q2) :
    |2 * u + x2| ≤
      ∫ z, rho ((u : ℂ) + polyEval a z) *
        (‖(1 : ℂ) + ((u : ℂ) + polyEval a z)‖ + 1) ∂gaussianMeasure := by
  haveI : IsFiniteMeasure gaussianMeasure := gaussianMeasure_isFinite
  set G : ℂ → ℂ := fun z => (u : ℂ) + polyEval a z with hG
  have hOne2_int : Integrable (fun z => ‖(1 : ℂ) + G z‖ ^ 2) gaussianMeasure := by
    simpa [G, add_assoc, add_left_comm, add_comm] using
      integrable_sq_gaussianMeasure_real_const_add_polyEval a (u + 1)
  have hplus_sq : ∫ z, ‖(1 : ℂ) + G z‖ ^ 2 ∂gaussianMeasure = (u + 1) ^ 2 + q2 := by
    calc
      ∫ z, ‖(1 : ℂ) + G z‖ ^ 2 ∂gaussianMeasure
          = (1 / Real.pi) * ∫ z : ℂ, ‖(1 : ℂ) + G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
              simpa using integral_gaussianMeasure_eq (fun z : ℂ => ‖(1 : ℂ) + G z‖ ^ 2)
      _ = (u + 1) ^ 2 + fockNormSq a := by
            simpa [G, add_assoc, add_left_comm, add_comm] using
              gaussian_integral_real_const_add_polyEval a (u + 1)
      _ = (u + 1) ^ 2 + q2 := by rw [← hq2_fock]
  have h_int_eq : ∫ z, (‖(1 : ℂ) + G z‖ ^ 2 - 1) ∂gaussianMeasure = 2 * u + x2 := by
    calc
      ∫ z, (‖(1 : ℂ) + G z‖ ^ 2 - 1) ∂gaussianMeasure
          = ∫ z, ‖(1 : ℂ) + G z‖ ^ 2 ∂gaussianMeasure -
              ∫ z, (1 : ℝ) ∂gaussianMeasure := by
                rw [integral_sub hOne2_int (MeasureTheory.integrable_const 1)]
      _ = ((u + 1) ^ 2 + q2) - 1 := by rw [hplus_sq, integral_one_gaussianMeasure]
      _ = u ^ 2 + 2 * u + q2 := by ring
      _ = 2 * u + x2 := by rw [hx2_eq]; ring
  calc
    |2 * u + x2|
        = |∫ z, (‖(1 : ℂ) + G z‖ ^ 2 - 1) ∂gaussianMeasure| := by rw [h_int_eq]
    _ ≤ ∫ z, |‖(1 : ℂ) + G z‖ ^ 2 - 1| ∂gaussianMeasure := by
          have h := norm_integral_le_integral_norm (μ := gaussianMeasure)
            (f := fun z : ℂ => ‖(1 : ℂ) + G z‖ ^ 2 - 1)
          simp only [Real.norm_eq_abs] at h
          exact h
    _ = ∫ z, rho (G z) * (‖(1 : ℂ) + G z‖ + 1) ∂gaussianMeasure := by
          apply integral_congr_ae
          filter_upwards with z
          rw [rho_factor]

/-- The auxiliary `s2` bound: if a nonnegative `B` is pointwise dominated by
`2 + N` (with `N` the integrand of `x2`), then `∫ B² ≤ 4 + 4·∫N + x2`.  Factored
out of the main local-stability estimate to keep its proof under the size limit. -/
private lemma s2_le_aux {N B : ℂ → ℝ} {x2 : ℝ}
    (hB2_int : Integrable (fun z => B z ^ 2) gaussianMeasure)
    (hN_int : Integrable N gaussianMeasure)
    (hN2_int : Integrable (fun z => N z ^ 2) gaussianMeasure)
    (hx_mu : ∫ z, N z ^ 2 ∂gaussianMeasure = x2)
    (hB_le : ∀ z, B z ≤ 2 + N z) (hB_nonneg : ∀ z, 0 ≤ B z) :
    ∫ z, B z ^ 2 ∂gaussianMeasure ≤ 4 + 4 * ∫ z, N z ∂gaussianMeasure + x2 := by
  haveI : IsFiniteMeasure gaussianMeasure := gaussianMeasure_isFinite
  have hrhs_int : Integrable (fun z => 4 + 4 * N z + N z ^ 2) gaussianMeasure := by
    have h := (MeasureTheory.integrable_const (4 : ℝ)).add ((hN_int.const_mul 4).add hN2_int)
    refine h.congr ?_
    filter_upwards with z
    simp only [Pi.add_apply]
    ring
  have hmono : ∫ z, B z ^ 2 ∂gaussianMeasure ≤
      ∫ z, (4 + 4 * N z + N z ^ 2) ∂gaussianMeasure := by
    refine MeasureTheory.integral_mono_ae hB2_int hrhs_int
      (Filter.Eventually.of_forall fun z => ?_)
    have htri_sq : B z ^ 2 ≤ (2 + N z) ^ 2 := by nlinarith [hB_le z, hB_nonneg z]
    nlinarith [htri_sq]
  have hsplit1 :
      ∫ z, (4 + 4 * N z + N z ^ 2) ∂gaussianMeasure =
        ∫ z, (4 + 4 * N z) ∂gaussianMeasure + ∫ z, N z ^ 2 ∂gaussianMeasure := by
    simpa [add_assoc] using
      (integral_add ((MeasureTheory.integrable_const (4 : ℝ)).add (hN_int.const_mul 4)) hN2_int)
  have hsplit2 :
      ∫ z, (4 + 4 * N z) ∂gaussianMeasure =
        ∫ z, (4 : ℝ) ∂gaussianMeasure + ∫ z, 4 * N z ∂gaussianMeasure := by
    simpa using
      (integral_add (MeasureTheory.integrable_const (4 : ℝ)) (hN_int.const_mul 4))
  calc
    ∫ z, B z ^ 2 ∂gaussianMeasure ≤ ∫ z, (4 + 4 * N z + N z ^ 2) ∂gaussianMeasure := hmono
    _ = 4 + 4 * ∫ z, N z ∂gaussianMeasure + x2 := by
        rw [hsplit1, hsplit2, integral_const, integral_const_mul, hx_mu]
        have hmass : gaussianMeasure.real Set.univ = 1 := by
          simpa using integral_one_gaussianMeasure
        simp [hmass]

/-- The closing real-arithmetic step of the local-stability estimate: from the
scalar Cauchy–Schwarz bound, the `s2` bound and the smallness hypothesis it
derives `x2 ≤ 23003² · m2`.  Kept purely real-arithmetic so it elaborates within
the default heartbeat budget. -/
private lemma local_fock_closing_arith
    {x2 m2 q2 rq2 s2 u x m y : ℝ}
    (hx2_eq : x2 = u ^ 2 + q2)
    (hx_sq : x ^ 2 = x2) (hm_sq : m ^ 2 = m2) (hy_sq : y ^ 2 = q2)
    (hx_nonneg : 0 ≤ x) (hm_nonneg : 0 ≤ m) (hy_nonneg : 0 ≤ y)
    (hx2_nonneg : 0 ≤ x2) (hm2_nonneg : 0 ≤ m2)
    (hscalar_sq : |2 * u + x2| ^ 2 ≤ m2 * s2)
    (hs2_le : s2 ≤ (2 + x) ^ 2)
    (hx2_small : x2 ≤ (1 / 4601 : ℝ) ^ 2)
    (hq_basic : q2 ≤ 4600 ^ 2 * rq2)
    (hrq2_le : rq2 ≤ (|u| + m) ^ 2) :
    x2 ≤ 23003 ^ 2 * m2 := by
  have hx_le_delta : x ≤ (1 / 4601 : ℝ) := by
    have hx_sq_small : x ^ 2 ≤ (1 / 4601 : ℝ) ^ 2 := by rw [hx_sq]; exact hx2_small
    exact le_of_sq_le_sq hx_sq_small (by norm_num)
  have hscalar_main : |2 * u + x2| ≤ (2 + x) * m := by
    have h_rhs_nonneg : 0 ≤ (2 + x) * m := by nlinarith [hx_nonneg, hm_nonneg]
    have hsq' : |2 * u + x2| ^ 2 ≤ ((2 + x) * m) ^ 2 := by
      have hms2 : m2 * s2 ≤ ((2 + x) * m) ^ 2 := by
        calc
          m2 * s2 ≤ m2 * (2 + x) ^ 2 := mul_le_mul_of_nonneg_left hs2_le hm2_nonneg
          _ = ((2 + x) * m) ^ 2 := by rw [← hm_sq]; ring
      exact le_trans hscalar_sq hms2
    exact le_of_sq_le_sq hsq' h_rhs_nonneg
  have hu_bound : |u| ≤ ((2 + x) / 2) * m + x2 / 2 := by
    have htwo : |2 * u| ≤ |2 * u + x2| + x2 := by
      calc
        |2 * u| = |(2 * u + x2) + (-x2)| := by congr 1; ring
        _ ≤ |2 * u + x2| + |-x2| := abs_add_le _ _
        _ = |2 * u + x2| + x2 := by rw [abs_neg, abs_of_nonneg hx2_nonneg]
    have htwo' : 2 * |u| ≤ (2 + x) * m + x2 := by
      calc
        2 * |u| = |2 * u| := by rw [abs_mul]; norm_num
        _ ≤ |2 * u + x2| + x2 := htwo
        _ ≤ (2 + x) * m + x2 := by gcongr
    nlinarith [htwo']
  have hu_bound_delta : |u| ≤ ((2 + (1 / 4601 : ℝ)) / 2) * m + x ^ 2 / 2 := by
    nlinarith [hu_bound, hx_le_delta, hx_sq, hx_nonneg]
  have hy_le : y ≤ 4600 * (|u| + m) := by
    have h_rhs_nonneg : 0 ≤ 4600 * (|u| + m) := by nlinarith [hm_nonneg, abs_nonneg u]
    have hq2_le : y ^ 2 ≤ (4600 * (|u| + m)) ^ 2 := by
      rw [hy_sq]
      calc
        q2 ≤ (4600 : ℝ) ^ 2 * (|u| + m) ^ 2 := by
          calc
            q2 ≤ (4600 : ℝ) ^ 2 * rq2 := by simpa using hq_basic
            _ ≤ (4600 : ℝ) ^ 2 * (|u| + m) ^ 2 := mul_le_mul_of_nonneg_left hrq2_le (by positivity)
        _ = (4600 * (|u| + m)) ^ 2 := by ring
    exact le_of_sq_le_sq hq2_le h_rhs_nonneg
  have hx_le_uy : x ≤ |u| + y := by
    have h_rhs_nonneg : 0 ≤ |u| + y := by nlinarith [abs_nonneg u, hy_nonneg]
    have hx2_le : x ^ 2 ≤ (|u| + y) ^ 2 := by
      rw [hx_sq]
      calc
        x2 = u ^ 2 + y ^ 2 := by rw [hx2_eq, ← hy_sq]
        _ ≤ |u| ^ 2 + 2 * |u| * y + y ^ 2 := by nlinarith [abs_nonneg u, hy_nonneg, sq_abs u]
        _ = (|u| + y) ^ 2 := by ring
    exact le_of_sq_le_sq hx2_le h_rhs_nonneg
  have hpre :
      x ≤ (4600 + 4601 * ((2 + (1 / 4601 : ℝ)) / 2)) * m + (4601 / 2) * x ^ 2 := by
    nlinarith [hx_le_uy, hy_le, hu_bound_delta]
  have hx_sq_small : x ^ 2 ≤ (1 / 4601 : ℝ) * x := by nlinarith [hx_le_delta, hx_nonneg]
  have habsorb :
      x ≤ (4600 + 4601 * ((2 + (1 / 4601 : ℝ)) / 2)) * m + (1 / 2 : ℝ) * x := by
    nlinarith [hpre, hx_sq_small]
  have hx_final : x ≤ 23003 * m := by
    have hconst :
        2 * (4600 + 4601 * ((2 + (1 / 4601 : ℝ)) / 2)) ≤ (23003 : ℝ) := by norm_num
    nlinarith
  have hsq : x ^ 2 ≤ (23003 * m) ^ 2 := pow_le_pow_left₀ hx_nonneg hx_final 2
  calc
    x2 = x ^ 2 := hx_sq.symm
    _ ≤ (23003 * m) ^ 2 := hsq
    _ = 23003 ^ 2 * m2 := by rw [← hm_sq]; ring

theorem LocalFockSPR_of_small_norm
    (p : Polynomial ℂ)
    (hp_real : Complex.im (p.eval 0) = 0)
    (hsmall :
      (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        (1 / 4601 : ℝ) ^ 2) :
    ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
      23003 ^ 2 *
        ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  haveI : IsFiniteMeasure gaussianMeasure := gaussianMeasure_isFinite
  set u : ℝ := (p.eval 0).re
  have hp0 : p.eval 0 = (u : ℂ) := by apply Complex.ext <;> simp [u, hp_real]
  set q : Polynomial ℂ := p - Polynomial.C (u : ℂ)
  have hq0 : q.eval 0 = 0 := by simp [q, hp0]
  have hcoeff0 : q.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact hq0
  set D := q.natDegree
  set a : Fin D → ℂ := fun k => q.coeff (k.val + 1)
  have hq_eval : ∀ z, q.eval z = polyEval a z := by
    intro z
    rw [eval_eq_sum_range, polyEval]
    rw [Finset.sum_range_succ' (fun i => q.coeff i * z ^ i)]
    simp only [hcoeff0, zero_mul, pow_zero]
    rw [← Fin.sum_univ_eq_sum_range]
    ring
  have hq_sub : ∀ z, q.eval z = p.eval z - (u : ℂ) := by
    intro z
    simp [q]
  have hp_eval : ∀ z, p.eval z = (u : ℂ) + polyEval a z := by
    intro z
    calc
      p.eval z = q.eval z + (u : ℂ) := by
        rw [hq_sub z]
        ring
      _ = (u : ℂ) + polyEval a z := by
        rw [hq_eval]
        ring
  let x2 : ℝ := (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
  let m2 : ℝ := (1 / Real.pi) * ∫ z : ℂ, (rho (p.eval z)) ^ 2 * Real.exp (-‖z‖ ^ 2)
  let q2 : ℝ := (1 / Real.pi) * ∫ z : ℂ, ‖q.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
  let rq2 : ℝ := (1 / Real.pi) * ∫ z : ℂ, (rho (q.eval z)) ^ 2 * Real.exp (-‖z‖ ^ 2)
  let x : ℝ := Real.sqrt x2
  let m : ℝ := Real.sqrt m2
  let y : ℝ := Real.sqrt q2
  let N : ℂ → ℝ := fun z => ‖p.eval z‖
  let R : ℂ → ℝ := fun z => rho (p.eval z)
  let B : ℂ → ℝ := fun z => ‖(1 : ℂ) + p.eval z‖ + 1
  let s2 : ℝ := ∫ z, B z ^ 2 ∂gaussianMeasure
  have hq2_eq_fock : q2 = fockNormSq a := by
    simpa [q2, hq_eval] using fockNorm_eq_gaussian_integral a
  have hq2_nonneg : 0 ≤ q2 := by rw [hq2_eq_fock]; unfold fockNormSq; positivity
  have hm2_nonneg : 0 ≤ m2 := by
    unfold m2; refine mul_nonneg (by positivity) ?_
    exact integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _)))
  have hx2_eq : x2 = u ^ 2 + q2 := by
    rw [hq2_eq_fock]
    simpa [x2, hp_eval] using gaussian_integral_real_const_add_polyEval a u
  have hx2_nonneg : 0 ≤ x2 := by rw [hx2_eq]; positivity
  have hx_sq : x ^ 2 = x2 := by unfold x; rw [Real.sq_sqrt hx2_nonneg]
  have hm_sq : m ^ 2 = m2 := by unfold m; rw [Real.sq_sqrt hm2_nonneg]
  have hy_sq : y ^ 2 = q2 := by unfold y; rw [Real.sq_sqrt hq2_nonneg]
  have hx_mu : ∫ z, N z ^ 2 ∂gaussianMeasure = x2 := by
    simpa [N, x2] using integral_gaussianMeasure_eq (fun z : ℂ => ‖p.eval z‖ ^ 2)
  have hm_mu : ∫ z, R z ^ 2 ∂gaussianMeasure = m2 := by
    simpa [R, m2] using integral_gaussianMeasure_eq (fun z : ℂ => rho (p.eval z) ^ 2)
  have hq_mu : ∫ z, ‖q.eval z‖ ^ 2 ∂gaussianMeasure = q2 := by
    simpa [q2] using integral_gaussianMeasure_eq (fun z : ℂ => ‖q.eval z‖ ^ 2)
  have hrq_mu : ∫ z, rho (q.eval z) ^ 2 ∂gaussianMeasure = rq2 := by
    simpa [rq2] using integral_gaussianMeasure_eq (fun z : ℂ => rho (q.eval z) ^ 2)
  have hN_meas : AEStronglyMeasurable N gaussianMeasure := by
    have hcont : Continuous N := by
      simpa [N, hp_eval] using
        ((continuous_const.add (continuous_polyEval a)).norm :
          Continuous (fun z : ℂ => ‖(u : ℂ) + polyEval a z‖))
    exact hcont.aestronglyMeasurable
  have hR_meas : AEStronglyMeasurable R gaussianMeasure := by
    have hcont : Continuous R := by
      have h := rho_continuous.comp
        (continuous_const.add (continuous_polyEval a) :
          Continuous (fun z : ℂ => (u : ℂ) + polyEval a z))
      refine h.congr ?_
      intro z
      simp only [R, Function.comp_apply, Pi.add_apply, hp_eval]
    exact hcont.aestronglyMeasurable
  have hB_meas : AEStronglyMeasurable B gaussianMeasure := by
    have hcont : Continuous B := by
      have h : Continuous (fun z : ℂ => ‖(1 : ℂ) + ((u : ℂ) + polyEval a z)‖ + 1) :=
        ((continuous_const.add
          (continuous_const.add (continuous_polyEval a) :
            Continuous (fun z : ℂ => (u : ℂ) + polyEval a z))).norm).add continuous_const
      refine h.congr ?_
      intro z
      simp only [B, hp_eval]
    exact hcont.aestronglyMeasurable
  have hN2_int : Integrable (fun z => N z ^ 2) gaussianMeasure := by
    simpa [N, hp_eval] using integrable_sq_gaussianMeasure_real_const_add_polyEval a u
  have hR2_int : Integrable (fun z => R z ^ 2) gaussianMeasure := by
    simpa [R, hp_eval] using integrable_sq_gaussianMeasure_rho_real_const_add_polyEval a u
  have hB2_int : Integrable (fun z => B z ^ 2) gaussianMeasure := by
    simpa [B, hp_eval, add_assoc, add_left_comm, add_comm] using
      integrable_sq_gaussianMeasure_norm_add_one_real_const_add_polyEval a u
  have hN_int : Integrable N gaussianMeasure :=
    integrable_of_sq_gaussian hN_meas hN2_int
  have hR_int : Integrable R gaussianMeasure :=
    integrable_of_sq_gaussian hR_meas hR2_int
  have hB_int : Integrable B gaussianMeasure :=
    integrable_of_sq_gaussian hB_meas hB2_int
  have hRB_meas : AEStronglyMeasurable (fun z => R z * B z) gaussianMeasure :=
    hR_meas.mul hB_meas
  have hRB_int : Integrable (fun z => R z * B z) gaussianMeasure :=
    integrable_mul_of_sq_gaussian hRB_meas hR2_int hB2_int
  have hN_l1_sq :
      (∫ z, N z ∂gaussianMeasure) ^ 2 ≤ x2 := by
    simpa [hx_mu] using gaussian_l1_sq_le hN_meas hN2_int
  have hR_l1_sq :
      (∫ z, R z ∂gaussianMeasure) ^ 2 ≤ m2 := by
    simpa [hm_mu] using gaussian_l1_sq_le hR_meas hR2_int
  have hN_l1_nonneg : 0 ≤ ∫ z, N z ∂gaussianMeasure := integral_nonneg (fun z => norm_nonneg _)
  have hR_l1_nonneg : 0 ≤ ∫ z, R z ∂gaussianMeasure := by
    exact integral_nonneg (fun z => by unfold R; exact abs_nonneg _)
  have hx_nonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hm_nonneg : 0 ≤ m := Real.sqrt_nonneg _
  have hN_l1_le : ∫ z, N z ∂gaussianMeasure ≤ x := by
    nlinarith [hN_l1_sq, hx_sq, hN_l1_nonneg, hx_nonneg]
  have hR_l1_le : ∫ z, R z ∂gaussianMeasure ≤ m := by
    nlinarith [hR_l1_sq, hm_sq, hR_l1_nonneg, hm_nonneg]
  have hB_nonneg : ∀ z, 0 ≤ B z := fun z => by unfold B; positivity
  have hB_le : ∀ z, B z ≤ 2 + N z := by
    intro z
    unfold B N
    calc
      ‖(1 : ℂ) + p.eval z‖ + 1 ≤ (1 + ‖p.eval z‖) + 1 := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_right (norm_add_le (1 : ℂ) (p.eval z)) 1
      _ = 2 + ‖p.eval z‖ := by ring
  have hs2_le_aux : s2 ≤ 4 + 4 * ∫ z, N z ∂gaussianMeasure + x2 :=
    s2_le_aux hB2_int hN_int hN2_int hx_mu hB_le hB_nonneg
  have hs2_le : s2 ≤ (2 + x) ^ 2 := by nlinarith [hs2_le_aux, hN_l1_le, hx_sq]
  have hscalar_raw :
      |2 * u + x2| ≤ ∫ z, R z * B z ∂gaussianMeasure := by
    refine le_trans (scalar_raw_bound a hq2_eq_fock hx2_eq) (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with z
    simp only [R, B, hp_eval z]
  have hprod_nonneg : 0 ≤ ∫ z, R z * B z ∂gaussianMeasure :=
    integral_nonneg (fun z =>
      mul_nonneg (by unfold R; exact abs_nonneg _) (by unfold B; positivity))
  have hscalar_sq : |2 * u + x2| ^ 2 ≤ m2 * s2 := by
    have hraw_sq : |2 * u + x2| ^ 2 ≤ (∫ z, R z * B z ∂gaussianMeasure) ^ 2 := by
      simpa [pow_two] using
        mul_le_mul hscalar_raw hscalar_raw (abs_nonneg (2 * u + x2)) hprod_nonneg
    refine le_trans hraw_sq ?_
    simpa [hm_mu, s2] using integral_cauchy_schwarz hR_int hB_int hR2_int hB2_int hRB_int
  have hx2_small : x2 ≤ (1 / 4601 : ℝ) ^ 2 := by simpa [x2] using hsmall
  have hq_basic : q2 ≤ 4600 ^ 2 * rq2 := by
    unfold q2 rq2
    have hmain :
        ∫ z : ℂ, ‖q.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
          4600 ^ 2 * ∫ z : ℂ, (rho (q.eval z)) ^ 2 * Real.exp (-‖z‖ ^ 2) := by
      simpa [rho] using LocalFockSPR q hq0
    have hscaled := mul_le_mul_of_nonneg_left hmain (show 0 ≤ 1 / Real.pi by positivity)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hRq2_int : Integrable (fun z => rho (q.eval z) ^ 2) gaussianMeasure := by
    simpa [hq_eval] using integrable_sq_gaussianMeasure_rho_real_const_add_polyEval a 0
  have hG_nonneg : ∀ z, 0 ≤ rho (q.eval z) := fun z => abs_nonneg _
  have hR_nonneg : ∀ z, 0 ≤ R z := fun z => by unfold R rho; exact abs_nonneg _
  have hpt : ∀ z, rho (q.eval z) ≤ |u| + R z := by
    intro z
    unfold R
    calc
      rho (q.eval z) = rho (polyEval a z) := by rw [hq_eval]
      _ ≤ |u| + rho ((u : ℂ) + polyEval a z) := rho_const_add_le u (polyEval a z)
      _ = |u| + rho (p.eval z) := by rw [hp_eval]
  have hm_mu' : ∫ z, R z ^ 2 ∂gaussianMeasure = m ^ 2 := by rw [hm_mu, hm_sq]
  have hrq2_le : rq2 ≤ (|u| + m) ^ 2 :=
    rho_centered_integral_bound hR_nonneg hG_nonneg hR_meas hR_int hR2_int hRq2_int
      hpt hrq_mu hm_mu' hR_l1_le
  have hy_nonneg : 0 ≤ y := Real.sqrt_nonneg _
  have hx_final_sq : x2 ≤ 23003 ^ 2 * m2 :=
    local_fock_closing_arith hx2_eq hx_sq hm_sq hy_sq hx_nonneg hm_nonneg hy_nonneg
      hx2_nonneg hm2_nonneg hscalar_sq hs2_le hx2_small hq_basic hrq2_le
  have hfinal_rho :
      ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        23003 ^ 2 * ∫ z : ℂ, (rho (p.eval z)) ^ 2 * Real.exp (-‖z‖ ^ 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hx_final_sq Real.pi_pos.le
    calc
      ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) = Real.pi * x2 := by
        unfold x2; field_simp [Real.pi_ne_zero]
      _ ≤ Real.pi * (23003 ^ 2 * m2) := hscaled
      _ = 23003 ^ 2 * ∫ z : ℂ, (rho (p.eval z)) ^ 2 * Real.exp (-‖z‖ ^ 2) := by
        unfold m2; field_simp [Real.pi_ne_zero]
  simpa [rho] using hfinal_rho

end FockSPR
