/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodization
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Mollifier

/-!
# Position-space form of the Riemann sum (Bridge Lemma 2)
# Convex-combination scalar coefficient

The position-space Riemann-sum operator and its identification with
the momentum-side `riemannSumDistrib` (Bridge Lemma 2). Also the
real-valued scalar coefficient `convexComboScalar` used in the
convex-combination approximation of smooth metrics, together with
its smoothness, periodicity, and non-negativity properties.

## Main contents

* `positionSpaceRiemann n φ u M` — `r_M^φ u(x) = δⁿ ∑_z φ^per(x - z) ǔ(z)`.
* `periodicExtension_eq_self_of_mem`,
  `integral_periodicExtension_mul_fourierExp` — for `supp φ ⊂ (-π,π)ⁿ`,
  `φ^per = φ` on `[-π,π]ⁿ` and `∫_{[0,2π]ⁿ} φ^per · e_{-m} = φ̂(m)`.
* `riemann_positionSpace` (Bridge Lemma 2) — `riemannSumDistrib n φ u M
  = integrationEmbed n (positionSpaceRiemann n φ u M)` for
  `φ ∈ C^∞_c` with `supp φ ⊂ (-π,π)ⁿ`, `2s > n`, `u ∈ MemSobolevDistrib n s`.
* `riemannSumDistrib_memSobolevDistrib` — `riemannSumDistrib n φ u M ∈ H^s_*`
  when `φ` has rapid Fourier decay and `u ∈ H^s_*`.
* `convexComboScalar n φ M k x` — the scalar
  `δⁿ · (periodicExtension n φ (x - z_k)).re`.
* `convexComboScalar_contDiff`, `convexComboScalar_isPeriodic2Pi`,
  `convexComboScalar_nonneg` — properties of the scalar coefficient.
-/

open scoped BigOperators ContDiff
open Complex Real MeasureTheory

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Definition: position-space Riemann sum -/

/-- The position-space Riemann-sum operator
    `r_M^φ u(x) = δⁿ ∑_z φ^per(x - z) · ǔ(z)`,
    where `δ = 2π/M` and `ǔ` is the continuous representative of `u`. -/
def positionSpaceRiemann (n : ℕ) (φ : (Fin n → ℝ) → ℂ)
    (u : TrigPolyDual n) (M : ℕ) (x : Fin n → ℝ) : ℂ :=
  let δ := (2 * Real.pi / (M : ℝ))
  ((δ ^ n : ℝ) : ℂ) * ∑ k : Fin n → Fin M,
    periodicExtension n φ (fun j => x j - meshPoint n M k j) *
    fourierSynthesis n (fourierCoeffDistrib u) (meshPoint n M k)

/-! ## Periodization on `[-π,π]ⁿ` and the Fourier transform at integer points -/

lemma periodicExtension_eq_self_of_mem {φ : (Fin n → ℝ) → ℂ}
    (hsupp : ∀ x, φ x ≠ 0 → ∀ j : Fin n, |x j| < π)
    {θ : Fin n → ℝ} (hθ : θ ∈ Set.Icc (-(π • (1 : Fin n → ℝ))) (π • (1 : Fin n → ℝ))) :
    periodicExtension n φ θ = φ θ := by
  unfold periodicExtension
  rw [tsum_eq_single 0]
  · have h0 : periodicShift n 0 = 0 := by funext i; simp [periodicShift]
    rw [h0, add_zero]
  · intro l hl
    obtain ⟨j, hj⟩ : ∃ j, l j ≠ 0 := by
      by_contra h
      push Not at h
      exact hl (funext h)
    by_contra hne
    have hb := hsupp _ hne j
    have hθj : |θ j| ≤ π := by
      obtain ⟨h1, h2⟩ := hθ
      have := h1 j; have := h2 j
      simp only [Pi.neg_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at *
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hl1 : (1 : ℝ) ≤ |(l j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
    simp only [Pi.add_apply, periodicShift] at hb
    have := abs_sub_abs_le_abs_sub (2 * π * (l j : ℝ)) (-(θ j))
    rw [abs_neg, sub_neg_eq_add, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π),
      add_comm (2 * π * (l j : ℝ)) (θ j)] at this
    have h2 : 2 * π ≤ 2 * π * |(l j : ℝ)| := by nlinarith [Real.pi_pos]
    linarith

lemma fourierExp_neg_eq_exp (m : Fin n → ℤ) (y : Fin n → ℝ) :
    fourierExp n (-m) y = Complex.exp (-(Complex.I * ((∑ j, (m j : ℝ) * y j : ℝ) : ℂ))) := by
  unfold fourierExp
  congr 1
  push_cast
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]

/-- The period-cube Fourier coefficient of the periodization is the `ℝⁿ` Fourier transform at the
integer point, for `φ` supported in `(-π,π)ⁿ`. -/
lemma integral_periodicExtension_mul_fourierExp {φ : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ φ) (hsuppC : HasCompactSupport φ)
    (hsupp : ∀ x, φ x ≠ 0 → ∀ j : Fin n, |x j| < π) (m : Fin n → ℤ) :
    ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)),
        periodicExtension n φ θ * fourierExp n (-m) θ
      = ftRn n φ (fun j => (m j : ℝ)) := by
  have hc : Continuous (fun θ => periodicExtension n φ θ * fourierExp n (-m) θ) :=
    (periodicExtension_contDiff hsmooth hsuppC).continuous.mul (fourierExp_contDiff _).continuous
  have hp : IsPeriodic2Pi (fun θ => periodicExtension n φ θ * fourierExp n (-m) θ) := by
    intro x k
    simp only [periodicExtension_isPeriodic2Pi φ x k, fourierExp_isPeriodic2Pi (-m) x k]
  rw [← integral_periodCube_translate hc hp (-(π • (1 : Fin n → ℝ)))]
  have hbox : -(π • (1 : Fin n → ℝ)) + 2 * π • (1 : Fin n → ℝ) = π • (1 : Fin n → ℝ) := by
    funext i; simp; ring
  rw [hbox]
  rw [setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => by rw [periodicExtension_eq_self_of_mem hsupp hθ])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · unfold ftRn
    simp_rw [fourierExp_neg_eq_exp]
  · intro θ hθ
    have : φ θ = 0 := by
      by_contra hne
      apply hθ
      refine ⟨fun j => ?_, fun j => ?_⟩ <;>
        simp only [Pi.neg_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] <;>
        linarith [abs_lt.mp (hsupp θ hne j)]
    simp [this]

/-! ## Bridge Lemma 2: position-space form of the Riemann sum -/

/-- For `φ ∈ C^∞_c(ℝⁿ; ℂ)` with `supp(φ) ⊂ (-π,π)ⁿ`, `2s > n`,
    `u ∈ MemSobolevDistrib n s`, and `M ≥ 1`,
    `riemannSumDistrib n φ u M = integrationEmbed n (positionSpaceRiemann n φ u M)`
    in `X_n^*`. -/
theorem riemann_positionSpace
    {φ : (Fin n → ℝ) → ℂ} (hsmooth : ContDiff ℝ ∞ φ) (hsuppC : HasCompactSupport φ)
    (hsupp : ∀ x, φ x ≠ 0 → ∀ j : Fin n, |x j| < Real.pi)
    (u : TrigPolyDual n) (M : ℕ) :
    riemannSumDistrib n φ u M = integrationEmbed n (positionSpaceRiemann n φ u M) := by
  unfold riemannSumDistrib integrationEmbed
  congr 1
  funext m
  unfold stdFourierCoeff positionSpaceRiemann riemannK
  dsimp only
  have hpec : Continuous (periodicExtension n φ) :=
    (periodicExtension_contDiff hsmooth hsuppC).continuous
  have hpep : IsPeriodic2Pi (periodicExtension n φ) := periodicExtension_isPeriodic2Pi φ
  -- per-mesh-point identity
  have hk : ∀ k : Fin n → Fin M,
      ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)),
          periodicExtension n φ (fun j => θ j - meshPoint n M k j) * fourierExp n (-m) θ
        = fourierExp n (-m) (meshPoint n M k) * ftRn n φ (fun j => (m j : ℝ)) := by
    intro k
    have h1 : ∀ θ : Fin n → ℝ,
        periodicExtension n φ (fun j => θ j - meshPoint n M k j) * fourierExp n (-m) θ
          = (fun θ' => periodicExtension n φ θ' * fourierExp n (-m) θ') (θ + (-(meshPoint n M k)))
            * fourierExp n (-m) (meshPoint n M k) := by
      intro θ
      have h : (fun j => θ j - meshPoint n M k j) = θ + (-(meshPoint n M k)) := by
        funext j; simp [sub_eq_add_neg]
      rw [h]
      simp only []
      rw [mul_assoc, ← fourierExp_add_point, neg_add_cancel_right]
    simp_rw [h1]
    have hti := integral_periodCube_add_right
      (g := fun θ' => periodicExtension n φ θ' * fourierExp n (-m) θ')
      (hpec.mul (fourierExp_contDiff _).continuous)
      (fun x l => by simp only [hpep x l, fourierExp_isPeriodic2Pi (-m) x l]) (-(meshPoint n M k))
    rw [integral_mul_const, hti, integral_periodicExtension_mul_fourierExp hsmooth hsuppC hsupp m,
      mul_comm]
  -- pull the finite sum out of the integral
  have h2 : ∀ θ : Fin n → ℝ,
      (((((2 * π / (M : ℝ)) ^ n : ℝ)) : ℂ) *
          ∑ k : Fin n → Fin M, periodicExtension n φ (fun j => θ j - meshPoint n M k j) *
            fourierSynthesis n (fourierCoeffDistrib u) (meshPoint n M k)) * fourierExp n (-m) θ
        = ∑ k : Fin n → Fin M, ((((2 * π / (M : ℝ)) ^ n : ℝ)) : ℂ) *
            fourierSynthesis n (fourierCoeffDistrib u) (meshPoint n M k) *
            (periodicExtension n φ (fun j => θ j - meshPoint n M k j) * fourierExp n (-m) θ) := by
    intro θ
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [h2]
  rw [integral_finsetSum _ (fun k _ => ?_)]
  · simp_rw [integral_const_mul, hk]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · refine (Continuous.continuousOn ?_).integrableOn_compact isCompact_Icc
    refine continuous_const.mul ((hpec.comp ?_).mul (fourierExp_contDiff _).continuous)
    fun_prop

/-
The Riemann-sum distribution preserves `MemSobolevDistrib` membership when
    `φ` has rapid Fourier decay.
-/
lemma riemannSumDistrib_memSobolevDistrib {φ : (Fin n → ℝ) → ℂ}
    (hφ_rd : FTRapidDecay n φ) (hn : 0 < n)
    {s : ℝ} (hs : (n : ℝ) < 2 * s)
    {u : TrigPolyDual n} (hu : MemSobolevDistrib n s u) (M : ℕ) :
    MemSobolevDistrib n s (riemannSumDistrib n φ u M) := by
  convert memSobolevDistrib_riemannSumDistrib φ hφ_rd hn hs hu M using 1

/-! ## Convex-combination scalar coefficient -/

/-- The real-valued scalar coefficient
    `f_k(x) = δⁿ · (periodicExtension n φ (x - z_k)).re`,
    where `δ = 2π/M` and `z_k = meshPoint n M k`.
    For real-valued non-negative `φ` (viewed via `Complex.ofReal`),
    `f_k` is non-negative, smooth, and `2πℤⁿ`-periodic — yielding the
    scalar weights in the convex-combination approximation of smooth
    metrics. -/
def convexComboScalar (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (M : ℕ)
    (k : Fin n → Fin M) (x : Fin n → ℝ) : ℝ :=
  (2 * Real.pi / (M : ℝ)) ^ n
    * (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re

/-- `convexComboScalar n φ M k` is smooth on `ℝⁿ` whenever `φ` is. -/
lemma convexComboScalar_contDiff {φ : (Fin n → ℝ) → ℂ}
    (hφ_sm : ContDiff ℝ ∞ φ) (hφ_supp : HasCompactSupport φ)
    (M : ℕ) (k : Fin n → Fin M) :
    ContDiff ℝ ∞ (convexComboScalar n φ M k) := by
  have h_pe : ContDiff ℝ ∞ (periodicExtension n φ) :=
    periodicExtension_contDiff hφ_sm hφ_supp
  have h_shift : ContDiff ℝ ∞
      (fun x : (Fin n → ℝ) => fun j => x j - meshPoint n M k j) := by
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_apply ℝ ℝ j).sub contDiff_const
  have h_comp : ContDiff ℝ ∞
      (fun x : (Fin n → ℝ) =>
        periodicExtension n φ (fun j => x j - meshPoint n M k j)) :=
    h_pe.comp h_shift
  have h_re_clm : ContDiff ℝ ∞ ((Complex.reCLM : ℂ →L[ℝ] ℝ) : ℂ → ℝ) :=
    ContinuousLinearMap.contDiff _
  have h_re : ContDiff ℝ ∞ (fun x : (Fin n → ℝ) =>
      (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re) :=
    h_re_clm.comp h_comp
  exact (contDiff_const :
    ContDiff ℝ ∞ (fun _ : (Fin n → ℝ) => (2 * Real.pi / (M : ℝ)) ^ n)).mul h_re

/-- `convexComboScalar n φ M k` is `2πℤⁿ`-periodic. -/
lemma convexComboScalar_isPeriodic2Pi (φ : (Fin n → ℝ) → ℂ) (M : ℕ)
    (k : Fin n → Fin M) :
    IsPeriodic2Pi (convexComboScalar n φ M k) := by
  intro x kk
  show (2 * Real.pi / (M : ℝ)) ^ n
        * (periodicExtension n φ
            (fun j => (x + periodicShift n kk) j - meshPoint n M k j)).re
    = (2 * Real.pi / (M : ℝ)) ^ n
        * (periodicExtension n φ
            (fun j => x j - meshPoint n M k j)).re
  have h_arg : (fun j => (x + periodicShift n kk) j - meshPoint n M k j)
      = (fun j => x j - meshPoint n M k j) + periodicShift n kk := by
    funext j
    simp [Pi.add_apply]
    ring
  rw [h_arg, periodicExtension_isPeriodic2Pi φ]

/-- `convexComboScalar n φ M k x ≥ 0`, provided `0 < M`, `φ` has compact
    support, and `φ` has pointwise non-negative real part. -/
lemma convexComboScalar_nonneg {φ : (Fin n → ℝ) → ℂ}
    (hφ_supp : HasCompactSupport φ) (hφ_re_nn : ∀ x, 0 ≤ (φ x).re)
    {M : ℕ} (hM : 0 < M) (k : Fin n → Fin M) (x : Fin n → ℝ) :
    0 ≤ convexComboScalar n φ M k x := by
  have hδ_pos : (0 : ℝ) < 2 * Real.pi / (M : ℝ) := by positivity
  show 0 ≤ (2 * Real.pi / (M : ℝ)) ^ n
        * (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
  exact mul_nonneg (pow_nonneg hδ_pos.le n)
    (periodicExtension_re_nonneg hφ_supp hφ_re_nn _)

end NashEmbedding.Sobolev

end
