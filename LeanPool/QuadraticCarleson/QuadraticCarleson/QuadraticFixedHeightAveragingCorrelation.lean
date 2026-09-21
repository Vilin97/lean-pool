/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingFinite
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Annular amplitude products in the fixed-height quadratic correlation

These lemmas instantiate the proved quadratic oscillatory estimate for the
actual product of two annular convolution amplitudes. Their uniform amplitude
and derivative bounds are kept explicit, to be supplied by the dyadic cutoff
lemmas rather than assumed in a headline theorem.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson

/-- Modulation of an annular amplitude by the paper's quadratic phase. -/
noncomputable def annularQuadraticKernel (a : ℝ → ℂ) (lam t : ℝ) : ℂ :=
  a t * phase (lam * t ^ 2)

theorem phase_sub_eq_mul_conj (s t : ℝ) : phase (s - t) = phase s * conj (phase t) := by
  unfold phase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The correlation of the modulated kernels has exactly the quadratic
phase from `QuadraticTTStar`, with the product of the two amplitudes. -/
theorem annularQuadraticKernel_mul_conj (a b : ℝ → ℂ) (lam μ x y t : ℝ) :
    annularQuadraticKernel a lam (x - t) * conj (annularQuadraticKernel b μ (y - t)) =
      (a (x - t) * conj (b (y - t))) * phase (quadraticTTStarPhase lam μ x y t) := by
  rw [quadraticTTStarPhase, phase_sub_eq_mul_conj]
  simp only [annularQuadraticKernel, map_mul]
  ring

/-- The ordered-scale annular correlation estimate. All amplitude-product
bounds and derivative bounds required by the oscillatory theorem are derived
here from the two individual annular amplitude estimates. -/
theorem annularQuadraticKernel_correlation_le_ordered
    {a a' b b' : ℝ → ℂ} {R S H D u lam μ : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hRS : R ≤ S) (hH : 0 < H) (hD : 0 ≤ D)
    (hu : 0 < u) (hu1 : u ≤ 1) (hdecay : 1 ≤ H * u ^ 5)
    (hlam : H ≤ lam * R ^ 2) (hlam' : lam * R ^ 2 ≤ 4 * H)
    (hμ : 0 ≤ μ) (hμ' : μ * S ^ 2 ≤ 4 * H)
    (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a')
    (hb : ∀ t, HasDerivAt b (b' t) t) (hb' : Continuous b')
    (hasupp : Function.support a ⊆ Icc (R / 4) R)
    (hbsupp : Function.support b ⊆ Icc (S / 4) S)
    (hab : ∀ t, ‖a t‖ ≤ D / R) (hab' : ∀ t, ‖a' t‖ ≤ D / R ^ 2)
    (hbb : ∀ t, ‖b t‖ ≤ D / S) (hbb' : ∀ t, ‖b' t‖ ≤ D / S ^ 2)
    (x y : ℝ) :
    ‖∫ t, annularQuadraticKernel a lam (x - t) *
      conj (annularQuadraticKernel b μ (y - t))‖ ≤
      quadraticFixedHeightMajorant (2 * D ^ 2) u S (x - y) := by
  let p : ℝ → ℂ := fun t ↦ a (x - t) * conj (b (y - t))
  let p' : ℝ → ℂ := fun t ↦
    (-a' (x - t)) * conj (b (y - t)) + a (x - t) * conj (-b' (y - t))
  let P : ℝ := 2 * D ^ 2 / (R * S)
  have hac : Continuous a := continuous_iff_continuousAt.mpr (fun t ↦ (ha t).continuousAt)
  have hbc : Continuous b := continuous_iff_continuousAt.mpr (fun t ↦ (hb t).continuousAt)
  have hpa (t : ℝ) : HasDerivAt (fun t ↦ a (x - t)) (-a' (x - t)) t := by
    simpa only [Function.comp_def, zero_sub, neg_one_smul] using
      (ha (x - t)).scomp t ((hasDerivAt_const t x).sub (hasDerivAt_id t))
  have hpb (t : ℝ) : HasDerivAt (fun t ↦ b (y - t)) (-b' (y - t)) t := by
    simpa only [Function.comp_def, zero_sub, neg_one_smul] using
      (hb (y - t)).scomp t ((hasDerivAt_const t y).sub (hasDerivAt_id t))
  have hp (t : ℝ) : HasDerivAt p (p' t) t := (hpa t).mul (hpb t).star
  have hp' : Continuous p' := by
    exact ((ha'.comp (continuous_const.sub continuous_id)).neg.mul
      (Complex.continuous_conj.comp (hbc.comp (continuous_const.sub continuous_id)))).add
      ((hac.comp (continuous_const.sub continuous_id)).mul
        (Complex.continuous_conj.comp (hb'.comp (continuous_const.sub continuous_id)).neg))
  have hsupp : Function.support p ⊆
      {t | R / 4 ≤ x - t ∧ x - t ≤ R ∧ 0 ≤ y - t ∧ y - t ≤ S} := by
    intro t ht
    have hat : a (x - t) ≠ 0 := by
      intro hz
      exact ht (by simp [p, hz])
    have hbt : b (y - t) ≠ 0 := by
      intro hz
      exact ht (by simp [p, hz])
    exact ⟨(hasupp hat).1, (hasupp hat).2,
      (by linarith [(hbsupp hbt).1]), (hbsupp hbt).2⟩
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpnorm (t : ℝ) : ‖p t‖ ≤ P := by
    calc
      ‖p t‖ = ‖a (x - t)‖ * ‖b (y - t)‖ := by simp [p, norm_mul]
      _ ≤ (D / R) * (D / S) :=
        mul_le_mul (hab _) (hbb _) (norm_nonneg _) (by positivity)
      _ = D ^ 2 / (R * S) := by ring
      _ ≤ P := by
        dsimp [P]
        rw [mul_div_assoc]
        nlinarith [div_nonneg (sq_nonneg D) (mul_pos hR hS).le]
  have hpdnorm (t : ℝ) : ‖p' t‖ ≤ P / R := by
    calc
      ‖p' t‖ ≤ ‖(-a' (x - t)) * conj (b (y - t))‖ +
          ‖a (x - t) * conj (-b' (y - t))‖ := norm_add_le _ _
      _ = ‖a' (x - t)‖ * ‖b (y - t)‖ + ‖a (x - t)‖ * ‖b' (y - t)‖ := by
        simp only [norm_mul, norm_neg, RCLike.norm_conj]
      _ ≤ (D / R ^ 2) * (D / S) + (D / R) * (D / S ^ 2) := by
        apply add_le_add
        · exact mul_le_mul (hab' _) (hbb _) (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hab _) (hbb' _) (norm_nonneg _) (by positivity)
      _ = (D ^ 2 / (R * S)) * (1 / R + 1 / S) := by field_simp
      _ ≤ (D ^ 2 / (R * S)) * (1 / R + 1 / R) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (one_div_le_one_div_of_le hR hRS))
          (by positivity)
      _ = P / R := by dsimp [P]; field_simp; ring
  have h := norm_integral_quadraticTTStar_fixed_height_supported lam μ x y hR hS hH hu hu1
    hdecay hμ hRS hlam hlam' hμ' hp hp' hP hsupp hpnorm hpdnorm
  have hPR : P * R = (2 * D ^ 2) / S := by dsimp [P]; field_simp
  simp_rw [annularQuadraticKernel_mul_conj]
  simpa only [quadraticFixedHeightMajorant, hPR, abs_sub_comm y x, p] using h

/-- Conjugate symmetry of the whole-line correlation, without any extra
integrability hypothesis. -/
theorem norm_integral_mul_conj_symm (f g : ℝ → ℂ) :
    ‖∫ t, f t * conj (g t)‖ = ‖∫ t, g t * conj (f t)‖ := by
  calc
    _ = ‖conj (∫ t, g t * conj (f t))‖ := by
      rw [← integral_conj]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [map_mul, starRingEnd_self_apply]
      ring
    _ = _ := RCLike.norm_conj _

/-- Symmetric two-scale form of the fixed-height annular correlation bound.
Positivity of both modulations follows from their common positive height. -/
theorem annularQuadraticKernel_correlation_le
    {a a' b b' : ℝ → ℂ} {R S H D u lam μ : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hH : 0 < H) (hD : 0 ≤ D)
    (hu : 0 < u) (hu1 : u ≤ 1) (hdecay : 1 ≤ H * u ^ 5)
    (hlam : H ≤ lam * R ^ 2) (hlam' : lam * R ^ 2 ≤ 4 * H)
    (hμ : H ≤ μ * S ^ 2) (hμ' : μ * S ^ 2 ≤ 4 * H)
    (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a')
    (hb : ∀ t, HasDerivAt b (b' t) t) (hb' : Continuous b')
    (hasupp : Function.support a ⊆ Icc (R / 4) R)
    (hbsupp : Function.support b ⊆ Icc (S / 4) S)
    (hab : ∀ t, ‖a t‖ ≤ D / R) (hab' : ∀ t, ‖a' t‖ ≤ D / R ^ 2)
    (hbb : ∀ t, ‖b t‖ ≤ D / S) (hbb' : ∀ t, ‖b' t‖ ≤ D / S ^ 2)
    (x y : ℝ) :
    ‖∫ t, annularQuadraticKernel a lam (x - t) *
      conj (annularQuadraticKernel b μ (y - t))‖ ≤
      quadraticFixedHeightMajorant (2 * D ^ 2) u (max R S) (x - y) := by
  have hμpos : 0 < μ := (mul_pos_iff_of_pos_right (sq_pos_of_pos hS)).mp (hH.trans_le hμ)
  have hlampos : 0 < lam := (mul_pos_iff_of_pos_right (sq_pos_of_pos hR)).mp (hH.trans_le hlam)
  by_cases hRS : R ≤ S
  · rw [max_eq_right hRS]
    exact annularQuadraticKernel_correlation_le_ordered hR hS hRS hH hD hu hu1 hdecay
      hlam hlam' hμpos.le hμ' ha ha' hb hb' hasupp hbsupp hab hab' hbb hbb' x y
  · rw [norm_integral_mul_conj_symm, max_eq_left (le_of_not_ge hRS)]
    have h := annularQuadraticKernel_correlation_le_ordered hS hR (le_of_not_ge hRS)
      hH hD hu hu1 hdecay hμ hμ' hlampos.le hlam' hb hb' ha ha'
      hbsupp hasupp hbb hbb' hab hab' y x
    simpa only [quadraticFixedHeightMajorant, abs_sub_comm y x] using h

/-- A complete finite maximal theorem for smooth positive-annular quadratic
kernels at one common height. The concrete dyadic specialization supplies
the displayed amplitude estimates from the fixed cutoff. -/
theorem finite_annularQuadraticKernel_maximal_sq_lintegral_le
    (n : ℕ) (a a' : Fin (n + 1) → ℝ → ℂ) (r lam : Fin (n + 1) → ℝ)
    {H D u : ℝ} (hr : ∀ i, 0 < r i) (hH : 0 < H) (hD : 0 ≤ D)
    (hu : 0 < u) (hu1 : u ≤ 1) (hdecay : 1 ≤ H * u ^ 5)
    (hheight : ∀ i, H ≤ lam i * r i ^ 2 ∧ lam i * r i ^ 2 ≤ 4 * H)
    (ha : ∀ i t, HasDerivAt (a i) (a' i t) t) (ha' : ∀ i, Continuous (a' i))
    (hsupp : ∀ i, Function.support (a i) ⊆ Icc (r i / 4) (r i))
    (hb : ∀ i t, ‖a i t‖ ≤ D / r i) (hb' : ∀ i t, ‖a' i t‖ ≤ D / r i ^ 2)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal (fun i ↦ annularQuadraticKernel (a i) (lam i)) f x ^ 2) ≤
      ENNReal.ofReal (4437295368 * D ^ 2 * u) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  have hc (i : Fin (n + 1)) : Continuous (annularQuadraticKernel (a i) (lam i)) := by
    have hai : Continuous (a i) := continuous_iff_continuousAt.mpr (fun t ↦ (ha i t).continuousAt)
    unfold annularQuadraticKernel phase
    fun_prop
  have hs (i : Fin (n + 1)) : HasCompactSupport (annularQuadraticKernel (a i) (lam i)) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (r i / 4) (r i)))
    intro t ht
    apply hsupp i
    intro hz
    exact ht (by simp [annularQuadraticKernel, hz])
  have h := finiteConvolutionMaximal_sq_lintegral_le_of_quadraticFixedHeightMajorant
    n (fun i ↦ annularQuadraticKernel (a i) (lam i)) hc hs r hr
    (show 0 ≤ 2 * D ^ 2 by positivity) hu (fun i j x y ↦
      annularQuadraticKernel_correlation_le (hr i) (hr j) hH hD hu hu1 hdecay
        (hheight i).1 (hheight i).2 (hheight j).1 (hheight j).2
        (ha i) (ha' i) (ha j) (ha' j) (hsupp i) (hsupp j) (hb i) (hb' i) (hb j) (hb' j) x y) hf
  convert h using 1 <;> congr 2 <;> ring

end QuadraticCarleson
