/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # LocalCircleEstimate.lean
  Quantitative local estimate on S¹.
  Scaffolding notes: LocalCircleEstimate/local_circle_estimate.md

  Dependencies: Definitions, SafeSquare

  Public API:
  - `local_circle_estimate` (Theorem 3.1)
-/
import LeanPool.PhaseRetrieval.Constant.Internal.Definitions
import LeanPool.PhaseRetrieval.Constant.Internal.SafeSquare

/-! # LocalCircleEstimate -/


open MeasureTheory Complex Real Finset

noncomputable section

namespace FockSPR

/-! ## Theorem 3.1: Quantitative local estimate on S¹ -/

/-! ### Utility lemmas -/

private lemma cont_integrable {f : AddCircle T → ℂ} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma real_cont_integrable {f : AddCircle T → ℝ} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma P_continuous {E : Finset ℕ} (b : ℕ → ℂ) :
    Continuous (fun t : AddCircle T => ∑ n ∈ E, b n * (fourier (n : ℤ)) t) :=
  continuous_finsetSum _ (fun _ _ => (map_continuous (fourier _)).const_mul _)

private lemma rho_continuous : Continuous (rho : ℂ → ℝ) :=
  continuous_abs.comp
    (continuous_norm.comp (continuous_const.add continuous_id) |>.sub continuous_const)

/-! ### Fourier orthogonality -/

private lemma integral_fourier_eq_zero (n : ℤ) (hn : n ≠ 0) :
    ∫ t : AddCircle T, (fourier n) t ∂AddCircle.haarAddCircle = 0 := by
  have h : fourierCoeff (fun t => (fourier (0 : ℤ) : C(AddCircle T, ℂ)) t) (-n) = 0 := by
    rw [show (fun t => (fourier (0 : ℤ) : C(AddCircle T, ℂ)) t) =
        (fourier 0 : C(AddCircle T, ℂ)) from rfl, fourierCoeff_fourier]
    simp [Pi.single, Function.update, hn]
  rw [fourierCoeff] at h
  simp only [fourier_zero, smul_eq_mul, mul_one, neg_neg] at h; exact h

private lemma integral_P_eq_zero {E : Finset ℕ}
    (hE_pos : ∀ n ∈ E, 1 ≤ n) (b : ℕ → ℂ) :
    ∫ t : AddCircle T, (∑ n ∈ E, b n * (fourier (n : ℤ)) t)
      ∂AddCircle.haarAddCircle = 0 := by
  rw [integral_finsetSum _
    (fun n _ => cont_integrable ((map_continuous (fourier _)).const_mul _))]
  apply Finset.sum_eq_zero; intro n hn
  have : ∫ t : AddCircle T, b n * (fourier (n : ℤ)) t ∂AddCircle.haarAddCircle =
      b n * ∫ t : AddCircle T, (fourier (n : ℤ)) t ∂AddCircle.haarAddCircle :=
    integral_const_mul _ _
  rw [this, integral_fourier_eq_zero _ (by have := hE_pos n hn; omega), mul_zero]

-- Helper: ∫ Re(P) = 0 for positive-frequency P
private lemma integral_re_P_eq_zero {E : Finset ℕ}
    (hE_pos : ∀ n ∈ E, 1 ≤ n) (b : ℕ → ℂ)
    (P : AddCircle T → ℂ)
    (hP : P = fun t => ∑ n ∈ E, b n * fourier (n : ℤ) t) :
    ∫ t : AddCircle T, (P t).re ∂AddCircle.haarAddCircle = 0 := by
  have hP_cont : Continuous P := by rw [hP]; exact P_continuous b
  have hP_int : Integrable P AddCircle.haarAddCircle := cont_integrable hP_cont
  have h0 : ∫ t : AddCircle T, P t ∂AddCircle.haarAddCircle = 0 := by
    conv_lhs => rw [hP]; exact integral_P_eq_zero hE_pos b
  change ∫ t, RCLike.re (P t) ∂AddCircle.haarAddCircle = 0
  rw [integral_re hP_int]; exact congrArg RCLike.re h0

/-! ### Parseval identity for finite Fourier sums -/

-- Parseval: circleNormSq P = ∑ ‖b(n)‖²
-- The `Lp`/orthonormal-basis rewriting below generates a large elaboration term.
private lemma parseval_finite {E : Finset ℕ} (b : ℕ → ℂ) :
    circleNormSq (fun t : AddCircle T => ∑ n ∈ E, b n * (fourier (n : ℤ)) t) =
    ∑ n ∈ E, ‖b n‖ ^ 2 := by
  let Pcont : C(AddCircle T, ℂ) := ∑ n ∈ E, b n • fourier (n : ℤ)
  let PLp := (ContinuousMap.toLp (α := AddCircle T) 2 AddCircle.haarAddCircle ℂ) Pcont
  let E' := E.map ⟨(Nat.cast : ℕ → ℤ), Nat.cast_injective⟩
  let c : ℤ → ℂ := fun k => b (Int.toNat k)
  have hPLp : PLp = ∑ k ∈ E', c k • fourierLp 2 k := by
    simp only [PLp, Pcont, E', c, fourierLp, map_sum, map_smul]
    rw [Finset.sum_map]; simp
  have hinner_orth :
      @inner ℂ _ _ PLp PLp = Complex.ofReal (∑ n ∈ E, ‖b n‖ ^ 2) := by
    rw [hPLp, orthonormal_fourier.inner_sum c c E']
    rw [show E' = E.map ⟨(Nat.cast : ℕ → ℤ), Nat.cast_injective⟩ from rfl]
    rw [Finset.sum_map, Complex.ofReal_sum]; congr 1; ext n
    simp only [Function.Embedding.coeFn_mk, c, Int.toNat_natCast]
    rw [mul_comm, mul_conj]; congr 1; exact (Complex.sq_norm (b n)).symm
  have hinner_L2 := L2.inner_def (𝕜 := ℂ) PLp PLp
  have hcombine := hinner_L2.symm.trans hinner_orth
  have hae := ContinuousMap.coeFn_toLp
    (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) (p := 2) Pcont
  have hPcont_eq : ∀ t : AddCircle T, (Pcont : AddCircle T → ℂ) t =
      ∑ n ∈ E, b n * (fourier (n : ℤ)) t := by
    intro t
    simp [Pcont, ContinuousMap.coe_sum, ContinuousMap.coe_smul, smul_eq_mul]
  calc circleNormSq (fun t : AddCircle T => ∑ n ∈ E, b n * (fourier (n : ℤ)) t)
      = ∫ t : AddCircle T, ‖(↑↑PLp : AddCircle T → ℂ) t‖ ^ 2
          ∂AddCircle.haarAddCircle := by
          unfold circleNormSq; symm; apply integral_congr_ae
          filter_upwards [hae] with t ht
          show ‖(↑↑PLp : AddCircle T → ℂ) t‖ ^ 2 =
            ‖∑ n ∈ E, b n * (fourier (n : ℤ)) t‖ ^ 2
          rw [show (↑↑PLp : AddCircle T → ℂ) t = Pcont t from ht, hPcont_eq t]
    _ = (∫ t : AddCircle T, @inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
            ((↑↑PLp : AddCircle T → ℂ) t) ∂AddCircle.haarAddCircle).re := by
          have hint := L2.integrable_inner (𝕜 := ℂ) PLp PLp; symm
          calc (∫ t, @inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
                ((↑↑PLp : AddCircle T → ℂ) t) ∂AddCircle.haarAddCircle).re
              = Complex.reCLM (∫ t, @inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
                ((↑↑PLp : AddCircle T → ℂ) t) ∂AddCircle.haarAddCircle) := rfl
            _ = ∫ t, Complex.reCLM (@inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
                ((↑↑PLp : AddCircle T → ℂ) t)) ∂AddCircle.haarAddCircle :=
                (ContinuousLinearMap.integral_comp_comm _ hint).symm
            _ = ∫ t, ‖(↑↑PLp : AddCircle T → ℂ) t‖ ^ 2
                ∂AddCircle.haarAddCircle := by
                congr 1; ext t
                exact @inner_self_eq_norm_sq ℂ ℂ _ _ _
                  ((↑↑PLp : AddCircle T → ℂ) t)
    _ = ∑ n ∈ E, ‖b n‖ ^ 2 := by
          rw [show (∫ t : AddCircle T, @inner ℂ ℂ _
              ((↑↑PLp : AddCircle T → ℂ) t)
              ((↑↑PLp : AddCircle T → ℂ) t)
              ∂AddCircle.haarAddCircle) =
              Complex.ofReal (∑ n ∈ E, ‖b n‖ ^ 2) from hcombine,
            Complex.ofReal_re]

/-! ### Private Lemma 3.1a: L∞ bound -/

private lemma circle_linfty_bound {L : ℕ} (_hL : 1 ≤ L) {E : Finset ℕ}
    (hE : E.card = L) (_hE_pos : ∀ n ∈ E, 1 ≤ n)
    (b : ℕ → ℂ) (P : AddCircle T → ℂ)
    (hP : P = fun t => ∑ n ∈ E, b n * fourier (n : ℤ) t) :
    ∀ t : AddCircle T,
      ‖P t‖ ≤ Real.sqrt L * Real.sqrt (circleNormSq P) := by
  intro t
  have h1 : ‖P t‖ ≤ ∑ n ∈ E, ‖b n‖ := by
    rw [hP]; simp only
    calc ‖∑ n ∈ E, b n * (fourier (n : ℤ)) t‖
        ≤ ∑ n ∈ E, ‖b n * (fourier (n : ℤ)) t‖ := norm_sum_le _ _
      _ = ∑ n ∈ E, ‖b n‖ := by congr 1; ext n; rw [norm_mul, fourier_apply]; simp
  have h2 : (∑ n ∈ E, ‖b n‖) ≤
      Real.sqrt L * Real.sqrt (∑ n ∈ E, ‖b n‖ ^ 2) := by
    have hcs := Real.sum_sqrt_mul_sqrt_le (s := E)
      (f := fun _ => (1 : ℝ)) (g := fun n => ‖b n‖ ^ 2)
      (fun _ => zero_le_one) (fun n => sq_nonneg _)
    simp only [Real.sqrt_one, one_mul] at hcs
    calc ∑ n ∈ E, ‖b n‖
        = ∑ n ∈ E, Real.sqrt (‖b n‖ ^ 2) := by congr 1; ext n; rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt (∑ n ∈ E, 1) * Real.sqrt (∑ n ∈ E, ‖b n‖ ^ 2) := hcs
      _ = Real.sqrt L * Real.sqrt (∑ n ∈ E, ‖b n‖ ^ 2) := by congr 1; simp [hE]
  have h3 : ∑ n ∈ E, ‖b n‖ ^ 2 = circleNormSq P := by rw [hP]; exact (parseval_finite b).symm
  calc ‖P t‖ ≤ ∑ n ∈ E, ‖b n‖ := h1
    _ ≤ Real.sqrt L * Real.sqrt (∑ n ∈ E, ‖b n‖ ^ 2) := h2
    _ = Real.sqrt L * Real.sqrt (circleNormSq P) := by rw [h3]

/-! ### ∫ P² = 0 for positive-frequency sums -/

-- Expanding the square of a finite Fourier sum produces a sizeable nested sum.
private lemma integral_fourier_sum_sq_eq_zero {E : Finset ℕ}
    (hE_pos : ∀ n ∈ E, 1 ≤ n) (b : ℕ → ℂ) :
    ∫ t : AddCircle T,
      (∑ n ∈ E, b n * (fourier (n : ℤ)) t) ^ 2
        ∂AddCircle.haarAddCircle = 0 := by
  have hsq : ∀ t : AddCircle T,
      (∑ n ∈ E, b n * (fourier (n : ℤ)) t) ^ 2 =
      ∑ n ∈ E, ∑ m ∈ E,
        (b n * b m) * (fourier ((n : ℤ) + (m : ℤ))) t := by
    intro t; rw [sq, Finset.sum_mul]
    congr 1; ext n; rw [Finset.mul_sum]
    congr 1; ext m; rw [fourier_add (x := t)]; ring
  simp_rw [hsq]
  rw [integral_finsetSum _ (fun n _ =>
    cont_integrable (continuous_finsetSum _ (fun m _ =>
      (map_continuous (fourier _)).const_mul _)))]
  apply Finset.sum_eq_zero; intro n hn
  rw [integral_finsetSum _ (fun m _ =>
    cont_integrable ((map_continuous (fourier _)).const_mul _))]
  apply Finset.sum_eq_zero; intro m hm
  have key :
      ∫ t : AddCircle T,
        (b n * b m) * (fourier ((n : ℤ) + (m : ℤ))) t
          ∂AddCircle.haarAddCircle =
      (b n * b m) *
        ∫ t : AddCircle T,
          (fourier ((n : ℤ) + (m : ℤ))) t ∂AddCircle.haarAddCircle :=
    integral_const_mul _ _
  rw [key]
  rw [integral_fourier_eq_zero _
    (by have := hE_pos n hn; have := hE_pos m hm; omega)]
  exact mul_zero _

/-! ### Private Lemma 3.1b: Equal L² masses -/

-- The real/imaginary mass comparison combines `∫ P^2 = 0` with integral bookkeeping.
private lemma equal_l2_masses {L : ℕ} (_hL : 1 ≤ L) {E : Finset ℕ}
    (_hE : E.card = L) (hE_pos : ∀ n ∈ E, 1 ≤ n) (b : ℕ → ℂ)
    (P : AddCircle T → ℂ)
    (hP : P = fun t => ∑ n ∈ E, b n * fourier (n : ℤ) t) :
    ∫ t : AddCircle T, (P t).re ^ 2 ∂AddCircle.haarAddCircle =
    ∫ t : AddCircle T, (P t).im ^ 2 ∂AddCircle.haarAddCircle := by
  have hP_cont : Continuous P := by rw [hP]; exact P_continuous b
  have h_int_sq :
      ∫ t : AddCircle T, (P t) ^ 2 ∂AddCircle.haarAddCircle = 0 := by
    rw [hP]; exact integral_fourier_sum_sq_eq_zero hE_pos b
  have hP_int : Integrable (fun t => (P t) ^ 2) AddCircle.haarAddCircle :=
    by rw [hP]; exact cont_integrable ((P_continuous b).pow 2)
  have h_re_sq : ∀ t : AddCircle T,
      (P t).re ^ 2 - (P t).im ^ 2 = ((P t) ^ 2).re := by intro t; simp [sq, Complex.mul_re]
  have h_re_zero :
      ∫ t : AddCircle T, ((P t).re ^ 2 - (P t).im ^ 2)
        ∂AddCircle.haarAddCircle = 0 := by
    simp_rw [h_re_sq]
    change ∫ t, RCLike.re ((P t) ^ 2) ∂AddCircle.haarAddCircle = 0
    rw [integral_re hP_int]
    exact congrArg RCLike.re h_int_sq
  have h_re_int :
      Integrable (fun t => (P t).re ^ 2) AddCircle.haarAddCircle := by
    rw [hP]; exact (Complex.continuous_re.comp (P_continuous b)).pow 2
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_im_int :
      Integrable (fun t => (P t).im ^ 2) AddCircle.haarAddCircle := by
    rw [hP]; exact (Complex.continuous_im.comp (P_continuous b)).pow 2
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  linarith [integral_sub h_re_int h_im_int ▸ h_re_zero]

/-! ### Pointwise bound: rho(w)² ≥ w.re²/2 - ‖w‖⁴ -/

-- The nonlinear `rho` estimate is discharged by a large `nlinarith` certificate.
private lemma rho_sq_lower_bound (w : ℂ) (hw : ‖w‖ ≤ 1 / 4) :
    (rho w) ^ 2 ≥ w.re ^ 2 / 2 - ‖w‖ ^ 4 := by
  unfold rho; rw [sq_abs]
  set u := w.re; set v := w.im
  set r := ‖(1 : ℂ) + w‖
  have hr_sq : r ^ 2 = (1 + u) ^ 2 + v ^ 2 := by
    have := Complex.sq_norm ((1 : ℂ) + w)
    rw [this, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im]; ring
  have hw_sq : ‖w‖ ^ 2 = u ^ 2 + v ^ 2 := by
    have := Complex.sq_norm w; rw [this, Complex.normSq_apply]; ring
  have hr_nn : 0 ≤ r := norm_nonneg _
  have hs_le : u ^ 2 + v ^ 2 ≤ 1 / 16 := by
    rw [← hw_sq]
    exact le_trans
      (sq_le_sq' (by linarith [norm_nonneg w]) hw) (by norm_num)
  set s := u ^ 2 + v ^ 2
  have hA_sq :
      (2 + 2 * u + s - u ^ 2 / 2 + s ^ 2) ^ 2 ≥
        4 * ((1 + u) ^ 2 + v ^ 2) := by
    nlinarith [sq_nonneg (2 * u + u ^ 2 / 2 + v ^ 2 +
        (u ^ 2 + v ^ 2) ^ 2),
      sq_nonneg u, sq_nonneg v, sq_nonneg (u * v),
      sq_nonneg (u ^ 2 + v ^ 2 - u),
      sq_nonneg (u + v ^ 2),
      sq_nonneg (u ^ 2 - v ^ 2)]
  have hA_nn : 0 ≤ 2 + 2 * u + s - u ^ 2 / 2 + s ^ 2 := by
    have : u ^ 2 ≤ s := by simp [s]; nlinarith [sq_nonneg v]
    nlinarith
  have h2r :
      2 * r ≤ 2 + 2 * u + s - u ^ 2 / 2 + s ^ 2 := by
    by_contra h_neg; push Not at h_neg
    have h1 :
        (2 * r) ^ 2 >
          (2 + 2 * u + s - u ^ 2 / 2 + s ^ 2) ^ 2 :=
      sq_lt_sq' (by linarith) h_neg
    rw [show (2 * r) ^ 2 = 4 * r ^ 2 from by ring, hr_sq] at h1
    linarith
  have hw4 : ‖w‖ ^ 4 = s ^ 2 := by
    have : ‖w‖ ^ 4 = (‖w‖ ^ 2) ^ 2 := by ring
    rw [this, hw_sq]
  rw [hw4]; nlinarith [sq_nonneg (r - 1)]

/-! ### ∫ ‖P‖⁴ bound -/

private lemma integral_norm_pow4_le {P : AddCircle T → ℂ}
    (hP_cont : Continuous P) (M : ℝ) (_hM_nn : 0 ≤ M)
    (hM : ∀ t, ‖P t‖ ≤ M) :
    ∫ t : AddCircle T, ‖P t‖ ^ 4 ∂AddCircle.haarAddCircle ≤
      M ^ 2 * circleNormSq P := by
  unfold circleNormSq
  calc ∫ t, ‖P t‖ ^ 4 ∂AddCircle.haarAddCircle
      ≤ ∫ t, M ^ 2 * ‖P t‖ ^ 2 ∂AddCircle.haarAddCircle := by
        apply integral_mono
        · exact (hP_cont.norm.pow 4).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        · exact ((hP_cont.norm.pow 2).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).const_mul _
        · intro t
          have : ‖P t‖ ^ 2 ≤ M ^ 2 :=
            sq_le_sq' (by linarith [norm_nonneg (P t)]) (hM t)
          nlinarith [sq_nonneg (‖P t‖)]
    _ = M ^ 2 * ∫ t, ‖P t‖ ^ 2 ∂AddCircle.haarAddCircle :=
        integral_const_mul _ _

/-! ### Private Lemma 3.1c: Small-amplitude regime -/

-- This theorem threads several quantitative lemmas and a final absorption argument.
private lemma small_amplitude {L : ℕ} (hL : 1 ≤ L) {E : Finset ℕ}
    (hE : E.card = L) (hE_pos : ∀ n ∈ E, 1 ≤ n)
    (b : ℕ → ℂ) (P : AddCircle T → ℂ)
    (hP : P = fun t => ∑ n ∈ E, b n * fourier (n : ℤ) t)
    (hx : Real.sqrt (circleNormSq P) ≤ 1 / (4 * Real.sqrt L)) :
    ∫ t : AddCircle T, (rho (P t)) ^ 2 ∂AddCircle.haarAddCircle ≥
      3 / 16 * circleNormSq P := by
  set cns := circleNormSq P
  have hcns_nn : 0 ≤ cns := integral_nonneg (fun _ => by positivity)
  have hP_cont : Continuous P := by rw [hP]; exact P_continuous b
  -- Step 1: ‖P t‖ ≤ 1/4
  have hP_bound : ∀ t : AddCircle T, ‖P t‖ ≤ 1 / 4 := by
    intro t
    have hLinfty := circle_linfty_bound hL hE hE_pos b P hP t
    have hL_sqrt : 0 < Real.sqrt L :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
    calc ‖P t‖ ≤ Real.sqrt L * Real.sqrt cns := hLinfty
      _ ≤ Real.sqrt L * (1 / (4 * Real.sqrt L)) :=
          mul_le_mul_of_nonneg_left hx (le_of_lt hL_sqrt)
      _ = 1 / 4 := by field_simp
  -- Step 2: ∫ rho² ≥ ∫ (re²/2 - ‖P‖⁴)
  have h_lower :
      ∫ t : AddCircle T, rho (P t) ^ 2 ∂AddCircle.haarAddCircle ≥
      ∫ t : AddCircle T, ((P t).re ^ 2 / 2 - ‖P t‖ ^ 4)
        ∂AddCircle.haarAddCircle := by
    apply ge_iff_le.mpr; apply integral_mono
    · apply Integrable.sub
      · exact real_cont_integrable
          ((Complex.continuous_re.comp hP_cont).pow 2 |>.div_const _)
      · exact real_cont_integrable (hP_cont.norm.pow 4)
    · exact real_cont_integrable ((rho_continuous.comp hP_cont).pow 2)
    · intro t; exact rho_sq_lower_bound (P t) (hP_bound t)
  -- Step 3: ∫ re² = cns/2
  have h_re_eq_im := equal_l2_masses hL hE hE_pos b P hP
  have h_norm_sq : ∀ t : AddCircle T,
      ‖P t‖ ^ 2 = (P t).re ^ 2 + (P t).im ^ 2 := by
    intro t; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h_cns_split :
      cns = ∫ t : AddCircle T, (P t).re ^ 2 ∂AddCircle.haarAddCircle +
        ∫ t : AddCircle T, (P t).im ^ 2 ∂AddCircle.haarAddCircle := by
    change ∫ t : AddCircle T, ‖P t‖ ^ 2 ∂AddCircle.haarAddCircle = _
    have h_add := integral_add
      (real_cont_integrable ((Complex.continuous_re.comp hP_cont).pow 2))
      (real_cont_integrable ((Complex.continuous_im.comp hP_cont).pow 2))
    trans (∫ t, ((P t).re ^ 2 + (P t).im ^ 2) ∂AddCircle.haarAddCircle)
    · congr 1; ext t; exact h_norm_sq t
    · exact h_add
  have h_re_half :
      ∫ t : AddCircle T, (P t).re ^ 2 ∂AddCircle.haarAddCircle =
        cns / 2 := by linarith
  -- Step 4: ∫ ‖P‖⁴ ≤ (1/4)² · cns
  have h_norm4 :
      ∫ t : AddCircle T, ‖P t‖ ^ 4 ∂AddCircle.haarAddCircle ≤
        (1 / 4) ^ 2 * cns :=
    integral_norm_pow4_le hP_cont (1 / 4) (by norm_num) hP_bound
  -- Step 5: ∫ (re²/2 - ‖P‖⁴) = (∫ re²)/2 - ∫ ‖P‖⁴
  have h_integral_sub :
      ∫ t : AddCircle T,
        ((P t).re ^ 2 / 2 - ‖P t‖ ^ 4) ∂AddCircle.haarAddCircle =
      ∫ t : AddCircle T, (P t).re ^ 2 / 2 ∂AddCircle.haarAddCircle -
      ∫ t : AddCircle T, ‖P t‖ ^ 4 ∂AddCircle.haarAddCircle :=
    integral_sub
      (real_cont_integrable
        ((Complex.continuous_re.comp hP_cont).pow 2 |>.div_const _))
      (real_cont_integrable (hP_cont.norm.pow 4))
  have h_div :
      ∫ t : AddCircle T, (P t).re ^ 2 / 2 ∂AddCircle.haarAddCircle =
      (∫ t : AddCircle T, (P t).re ^ 2 ∂AddCircle.haarAddCircle) / 2 := by
    simp_rw [div_eq_mul_inv]; exact integral_mul_const 2⁻¹ _
  rw [h_integral_sub, h_div, h_re_half] at h_lower
  -- cns/2/2 - ∫ ‖P‖⁴ ≥ cns/4 - cns/16 = 3cns/16
  linarith

/-! ### ∫ ‖1+P‖² = 1 + circleNormSq P -/

-- Expanding `‖1 + P‖²` and integrating term-by-term is elaboration-heavy here.
private lemma integral_one_plus_P_sq {E : Finset ℕ}
    (hE_pos : ∀ n ∈ E, 1 ≤ n) (b : ℕ → ℂ)
    (P : AddCircle T → ℂ)
    (hP : P = fun t => ∑ n ∈ E, b n * fourier (n : ℤ) t) :
    ∫ t : AddCircle T, ‖(1 : ℂ) + P t‖ ^ 2
      ∂AddCircle.haarAddCircle = 1 + circleNormSq P := by
  have hP_cont : Continuous P := by rw [hP]; exact P_continuous b
  have h_re_P := integral_re_P_eq_zero hE_pos b P hP
  have key : ∀ t : AddCircle T,
      ‖(1 : ℂ) + P t‖ ^ 2 - ‖P t‖ ^ 2 = 1 + 2 * (P t).re := by
    intro t
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
        Complex.add_im, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.one_re, Complex.one_im]; ring
  have h_int1 : Integrable (fun t : AddCircle T => ‖(1 : ℂ) + P t‖ ^ 2)
      AddCircle.haarAddCircle :=
    real_cont_integrable ((continuous_const.add hP_cont).norm.pow 2)
  have h_int2 : Integrable (fun t : AddCircle T => ‖P t‖ ^ 2)
      AddCircle.haarAddCircle :=
    real_cont_integrable (hP_cont.norm.pow 2)
  have h_diff :
      ∫ t : AddCircle T, ‖(1 : ℂ) + P t‖ ^ 2
        ∂AddCircle.haarAddCircle -
      ∫ t : AddCircle T, ‖P t‖ ^ 2 ∂AddCircle.haarAddCircle = 1 := by
    rw [← integral_sub h_int1 h_int2]
    have h_congr :
        (fun t : AddCircle T =>
          ‖(1 : ℂ) + P t‖ ^ 2 - ‖P t‖ ^ 2) =
        (fun t => (1 : ℝ) + (2 : ℝ) * (P t).re) := by ext t; exact key t
    rw [h_congr]
    -- ∫ (1 + 2Re(P)) = ∫ 1 + 2·∫ Re(P) = 1 + 0 = 1
    have h1_int : Integrable (fun _ : AddCircle T => (1 : ℝ))
        AddCircle.haarAddCircle :=
      real_cont_integrable continuous_const
    have h2_int : Integrable (fun t : AddCircle T => (2 : ℝ) * (P t).re)
        AddCircle.haarAddCircle :=
      real_cont_integrable
        (Complex.continuous_re.comp hP_cont |>.const_mul 2)
    have h_split := integral_add h1_int h2_int
    trans (∫ _ : AddCircle T, (1 : ℝ) ∂AddCircle.haarAddCircle +
      ∫ t, (2 : ℝ) * (P t).re ∂AddCircle.haarAddCircle)
    · exact h_split
    · rw [integral_const_mul, h_re_P, mul_zero, add_zero]
      simp [integral_const]
  unfold circleNormSq; linarith

/-! ### Integral Cauchy-Schwarz for real-valued functions -/

-- to_mathlib: Mathlib.MeasureTheory.Integral.Bochner
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
  -- For all t: 0 ≤ ∫ (t·f(x) - g(x))²
  have h_quad : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * B + C := by
    intro t
    have h0 : 0 ≤ ∫ x, (t * f x - g x) ^ 2 ∂μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    have h_eq : ∫ x, (t * f x - g x) ^ 2 ∂μ = t ^ 2 * A - 2 * t * B + C := by
      have hI1 : ∫ x, t ^ 2 * f x ^ 2 ∂μ = t ^ 2 * A := integral_const_mul _ _
      have hI2 : ∫ x, (-2 * t) * (f x * g x) ∂μ = (-2 * t) * B := integral_const_mul _ _
      -- First combine: ∫ (tf-g)² = ∫ (t²f² + (-2t)fg) + ∫ g²
      have h_step1 : ∫ x, (t * f x - g x) ^ 2 ∂μ =
          ∫ x, (t ^ 2 * f x ^ 2 + (-2 * t) * (f x * g x)) ∂μ +
          ∫ x, g x ^ 2 ∂μ := by
        conv_lhs => rw [show (fun x => (t * f x - g x) ^ 2) =
            ((fun x => t ^ 2 * f x ^ 2 + (-2 * t) * (f x * g x)) +
             (fun x => g x ^ 2)) from by ext x; simp [Pi.add_apply]; ring]
        exact integral_add ((hf2.const_mul _).add (hfg.const_mul _)) hg2
      -- Then split the first integral
      have h_step2 : ∫ x, (t ^ 2 * f x ^ 2 + (-2 * t) * (f x * g x)) ∂μ =
          ∫ x, t ^ 2 * f x ^ 2 ∂μ + ∫ x, (-2 * t) * (f x * g x) ∂μ := by
        conv_lhs => rw [show (fun x => t ^ 2 * f x ^ 2 + (-2 * t) * (f x * g x)) =
            ((fun x => t ^ 2 * f x ^ 2) + (fun x => (-2 * t) * (f x * g x))) from by
          ext x; simp [Pi.add_apply]]
        exact integral_add (hf2.const_mul _) (hfg.const_mul _)
      rw [h_step1, h_step2, hI1, hI2]; ring
    linarith
  -- Non-negative quadratic ⟹ discriminant ≤ 0 ⟹ B² ≤ AC
  -- Case A = 0: quad at t=1 gives 0 ≤ -2B+C, at t=-1 gives 0 ≤ 2B+C, so |B| ≤ C/2.
  -- Also A=0 ⟹ AC=0, need B²≤0, i.e. B=0.
  -- A=0 means f=0 a.e., so fg=0 a.e., so B=0. ✓
  -- Case A > 0: quad at t=B/A gives 0 ≤ -B²/A + C, so B² ≤ AC. ✓
  by_cases hA_zero : A = 0
  · -- A = 0 ⟹ f = 0 a.e. ⟹ B = 0 ⟹ B² = 0 ≤ 0 = AC
    have hf_ae : ∀ᵐ x ∂μ, f x = 0 := by
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

/-! ### Private Lemma 3.1d: Large-amplitude regime -/

private lemma large_amplitude {L : ℕ} (hL : 1 ≤ L) {E : Finset ℕ}
    (hE : E.card = L) (hE_pos : ∀ n ∈ E, 1 ≤ n)
    (b : ℕ → ℂ) (P : AddCircle T → ℂ)
    (hP : P = fun t => ∑ n ∈ E, b n * fourier (n : ℤ) t)
    (hx : Real.sqrt (circleNormSq P) > 1 / (4 * Real.sqrt L)) :
    ∫ t : AddCircle T, (rho (P t)) ^ 2 ∂AddCircle.haarAddCircle ≥
      circleNormSq P / (144 * L) := by
  set cns := circleNormSq P
  set y := ∫ t : AddCircle T, rho (P t) ^ 2 ∂AddCircle.haarAddCircle
  have hP_cont : Continuous P := by rw [hP]; exact P_continuous b
  have hcns_nn : 0 ≤ cns := integral_nonneg (fun _ => by positivity)
  have hy_nn : 0 ≤ y := integral_nonneg (fun _ => by positivity)
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr (by omega)
  have hL_sqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
  -- From hypothesis: cns > 1/(16L)
  have h_cns_lower : cns > 1 / (16 * L) := by
    have hsq : Real.sqrt cns ^ 2 = cns := Real.sq_sqrt hcns_nn
    have hsqL : Real.sqrt L ^ 2 = (L : ℝ) :=
      Real.sq_sqrt (le_of_lt hL_pos)
    have h_sq_ineq : cns > (1 / (4 * Real.sqrt L)) ^ 2 := by
      rw [← hsq]
      exact (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)).mpr hx
    rw [div_pow, one_pow, mul_pow, hsqL] at h_sq_ineq
    linarith
  -- Step 1: Pointwise identity rho(w)·(‖1+w‖+1) = |‖1+w‖²-1|
  have h_rho_factor : ∀ w : ℂ,
      rho w * (‖(1 : ℂ) + w‖ + 1) = |‖(1 : ℂ) + w‖ ^ 2 - 1| := by
    intro w; unfold rho
    set a := ‖(1 : ℂ) + w‖
    have ha1 : 0 ≤ a + 1 := by positivity
    rw [show |a - 1| * (a + 1) = |a - 1| * |a + 1| from by
      rw [abs_of_nonneg ha1]]
    rw [← abs_mul]; congr 1; ring
  -- Continuity/integrability setup
  have h_1pP_cont : Continuous (fun t : AddCircle T => (1 : ℂ) + P t) :=
    continuous_const.add hP_cont
  have h_g_cont : Continuous (fun t : AddCircle T => ‖(1 : ℂ) + P t‖ + 1) :=
    h_1pP_cont.norm.add continuous_const
  have h_rho_comp : Continuous (fun t : AddCircle T => rho (P t)) :=
    rho_continuous.comp hP_cont
  have h_fg_int : Integrable (fun t : AddCircle T =>
      rho (P t) * (‖(1 : ℂ) + P t‖ + 1)) AddCircle.haarAddCircle :=
    real_cont_integrable (h_rho_comp.mul h_g_cont)
  -- Step 2: ∫ ‖1+P‖² = 1 + cns
  have h_int_1pP := integral_one_plus_P_sq hE_pos b P hP
  -- Step 3: cns ≤ ∫ ρ(P)·(‖1+P‖+1)
  have h_cns_le : cns ≤ ∫ t : AddCircle T,
      rho (P t) * (‖(1 : ℂ) + P t‖ + 1) ∂AddCircle.haarAddCircle := by
    -- cns = ∫ (‖1+P‖² - 1) ≤ ∫ |‖1+P‖² - 1| = ∫ ρ·(‖1+P‖+1)
    have h_int_norm_sq : Integrable (fun t : AddCircle T => ‖(1 : ℂ) + P t‖ ^ 2)
        AddCircle.haarAddCircle :=
      real_cont_integrable (h_1pP_cont.norm.pow 2)
    have h_sub : cns = ∫ t : AddCircle T, (‖(1 : ℂ) + P t‖ ^ 2 - 1)
        ∂AddCircle.haarAddCircle := by
      have h1 : ∫ t : AddCircle T, (1 : ℝ) ∂AddCircle.haarAddCircle = 1 := by simp [integral_const]
      rw [integral_sub h_int_norm_sq (integrable_const (1 : ℝ)), h_int_1pP, h1]; ring
    rw [h_sub]
    apply le_trans (integral_mono
      (h_int_norm_sq.sub (integrable_const 1))
      (real_cont_integrable (h_1pP_cont.norm.pow 2 |>.sub continuous_const |>.abs))
      (fun t => le_abs_self _))
    apply le_of_eq
    congr 1; ext t; exact (h_rho_factor (P t)).symm
  -- Step 4: Cauchy-Schwarz: (∫ ρ·g)² ≤ (∫ ρ²)·(∫ g²)
  have h_cs : (∫ t : AddCircle T,
      rho (P t) * (‖(1 : ℂ) + P t‖ + 1) ∂AddCircle.haarAddCircle) ^ 2 ≤
      y * ∫ t : AddCircle T, (‖(1 : ℂ) + P t‖ + 1) ^ 2
        ∂AddCircle.haarAddCircle :=
    integral_cauchy_schwarz
      (real_cont_integrable h_rho_comp)
      (real_cont_integrable h_g_cont)
      (real_cont_integrable (h_rho_comp.pow 2))
      (real_cont_integrable (h_g_cont.pow 2))
      h_fg_int
  -- Step 5: ∫ (‖1+P‖+1)² ≤ 2(1+cns) + 2 = 2cns + 4
  have h_g_sq_bound : ∫ t : AddCircle T, (‖(1 : ℂ) + P t‖ + 1) ^ 2
      ∂AddCircle.haarAddCircle ≤ 2 * cns + 4 := by
    have h_pw : ∀ t : AddCircle T,
        (‖(1 : ℂ) + P t‖ + 1) ^ 2 ≤
        2 * ‖(1 : ℂ) + P t‖ ^ 2 + 2 := by intro t; nlinarith [sq_nonneg (‖(1 : ℂ) + P t‖ - 1)]
    calc ∫ t, (‖(1 : ℂ) + P t‖ + 1) ^ 2 ∂AddCircle.haarAddCircle
        ≤ ∫ t, (2 * ‖(1 : ℂ) + P t‖ ^ 2 + 2) ∂AddCircle.haarAddCircle :=
          integral_mono
            (real_cont_integrable (h_g_cont.pow 2))
            (real_cont_integrable
              (h_1pP_cont.norm.pow 2 |>.const_mul 2 |>.add continuous_const))
            h_pw
      _ = 2 * ∫ t, ‖(1 : ℂ) + P t‖ ^ 2 ∂AddCircle.haarAddCircle + 2 := by
          rw [integral_add
            ((real_cont_integrable (h_1pP_cont.norm.pow 2)).const_mul 2)
            (integrable_const (2 : ℝ)),
            integral_const_mul, integral_const]
          simp
      _ = 2 * (1 + cns) + 2 := by rw [h_int_1pP]
      _ = 2 * cns + 4 := by ring
  -- Step 6: Combine: cns² ≤ y · (2cns + 4)
  have h_cns_sq_le : cns ^ 2 ≤ y * (2 * cns + 4) := by
    calc cns ^ 2
        ≤ (∫ t : AddCircle T,
          rho (P t) * (‖(1 : ℂ) + P t‖ + 1)
            ∂AddCircle.haarAddCircle) ^ 2 := sq_le_sq' (by nlinarith) h_cns_le
      _ ≤ y * ∫ t, (‖(1 : ℂ) + P t‖ + 1) ^ 2 ∂AddCircle.haarAddCircle := h_cs
      _ ≤ y * (2 * cns + 4) := mul_le_mul_of_nonneg_left h_g_sq_bound hy_nn
  -- Step 7: y ≥ cns / (144L)
  -- From cns² ≤ y(2cns+4) and cns > 1/(16L), deduce y ≥ cns/(144L).
  -- Equivalently: 144L·y ≥ cns.
  -- Since cns² ≤ y(2cns+4) and 144L·cns ≥ 2cns+4 (proved below), we get
  -- cns² ≤ y·(144L·cns), so cns ≤ 144L·y (for cns > 0).
  rw [ge_iff_le, div_le_iff₀ (by positivity : (0 : ℝ) < 144 * ↑L)]
  -- Need: cns ≤ 144 * L * y
  have hL_ge : (1 : ℝ) ≤ (↑L : ℝ) := Nat.one_le_cast.mpr hL
  have h_key : 2 * cns + 4 ≤ 144 * ↑L * cns := by
    -- (144L-2)·cns > (144L-2)/(16L) ≥ 142/16 > 4
    have h142 : (0 : ℝ) < 144 * ↑L - 2 := by nlinarith
    have h1 : (144 * ↑L - 2) * cns > (144 * ↑L - 2) * (1 / (16 * ↑L)) :=
      mul_lt_mul_of_pos_left h_cns_lower h142
    have h2 : (144 * (↑L : ℝ) - 2) * (1 / (16 * ↑L)) ≥ 142 / 16 := by
      rw [ge_iff_le, mul_one_div, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 16) (by positivity)]
      nlinarith
    nlinarith
  nlinarith [sq_nonneg cns]

/-! ### Theorem 3.1 (Main statement) -/

theorem local_circle_estimate {L : ℕ} (hL : 1 ≤ L) {E : Finset ℕ}
    (hE : E.card = L) (hE_pos : ∀ n ∈ E, 1 ≤ n)
    (b : ℕ → ℂ) (P : AddCircle T → ℂ)
    (hP : P = fun t => ∑ n ∈ E, b n * fourier (n : ℤ) t) :
    circleNormSq P ≤ 144 * L *
      (∫ t : AddCircle T, (rho (P t)) ^ 2
        ∂AddCircle.haarAddCircle) := by
  have hcns : 0 ≤ circleNormSq P := by unfold circleNormSq; apply integral_nonneg; intro; positivity
  by_cases hx : Real.sqrt (circleNormSq P) ≤ 1 / (4 * Real.sqrt L)
  · have h := small_amplitude hL hE hE_pos b P hP hx
    have hL_real : (1 : ℝ) ≤ (L : ℝ) := Nat.one_le_cast.mpr hL
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (3 : ℝ) / 16 * circleNormSq P ≤
      ∫ t, rho (P t) ^ 2 ∂AddCircle.haarAddCircle)
      (show (0 : ℝ) ≤ 144 * L from by nlinarith)]
  · push Not at hx
    have h := large_amplitude hL hE hE_pos b P hP hx
    have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (by omega)
    have h144L : (0 : ℝ) < 144 * (L : ℝ) := by positivity
    rw [ge_iff_le] at h
    calc circleNormSq P
        = 144 * ↑L * (circleNormSq P / (144 * ↑L)) := by field_simp
      _ ≤ 144 * ↑L *
          ∫ t : AddCircle T, rho (P t) ^ 2 ∂AddCircle.haarAddCircle :=
        mul_le_mul_of_nonneg_left h (le_of_lt h144L)

end FockSPR
