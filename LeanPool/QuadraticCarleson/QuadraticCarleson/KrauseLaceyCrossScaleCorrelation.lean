/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPositiveCorrelation

/-!
# Separated-scale quadratic correlation

This proves the degree-two kernel estimate in Krause--Lacey (2.6).
The phase becomes linear. With small radius at least one, the existing
first-derivative integration-by-parts estimate already gives the required
large-radius squared decay; no unproved second-derivative bound is needed.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ComplexConjugate Interval

namespace QuadraticCarleson


/-- Two positively supported, separated annuli have a uniformly
nonstationary quadratic correlation phase. -/
theorem krauseLacey_twoScaleCorrelation_le
    {r R P : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R / 8) (hP : 0 ≤ P)
    {p p' : ℝ → ℂ} (hp : ∀ t, HasDerivAt p (p' t) t) (hp' : Continuous p')
    (x y : ℝ)
    (hsupport : Function.support p ⊆
      {t | R / 4 ≤ x - t ∧ x - t ≤ R ∧ r / 4 ≤ y - t ∧ y - t ≤ r})
    (hbound : ∀ t, ‖p t‖ ≤ P) (hbound' : ∀ t, ‖p' t‖ ≤ P / r) :
    ‖∫ t, p t * phase (quadraticTTStarPhase 1 1 x y t)‖ ≤
      if |y - x| ≤ 2 * R then 3 * P / R else 0 := by
  let l : ℝ := max (x - R) (y - r)
  let u : ℝ := min (x - R / 4) (y - r / 4)
  have hsupp (t : ℝ) (ht : p t ≠ 0) : t ∈ Icc l u := by
    have hh := hsupport ht
    change max (x - R) (y - r) ≤ t ∧ t ≤ min (x - R / 4) (y - r / 4)
    rw [max_le_iff, le_min_iff]
    constructor <;> constructor <;> linarith [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2]
  by_cases hspatial : |y - x| ≤ 2 * R
  · simp only [hspatial, ↓reduceIte]
    by_cases hlu : l ≤ u
    · have hzero (t : ℝ) (ht : t ∉ Icc l u) : p t = 0 := by
        by_contra hn
        exact ht (hsupp t hn)
      have hid : (∫ t, p t * phase (quadraticTTStarPhase 1 1 x y t)) =
          ∫ t in l..u, p t * phase (quadraticTTStarPhase 1 1 x y t) := by
        calc
          _ = ∫ t in Icc l u, p t * phase (quadraticTTStarPhase 1 1 x y t) :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero
              (fun t ht ↦ by rw [hzero t ht, zero_mul])).symm
          _ = ∫ t in Ioc l u, p t * phase (quadraticTTStarPhase 1 1 x y t) :=
            integral_Icc_eq_integral_Ioc
          _ = _ := (intervalIntegral.integral_of_le hlu).symm
      have hlen : u - l ≤ r := by
        have hlower : y - r ≤ l := le_max_right _ _
        have hupper : u ≤ y - r / 4 := min_le_right _ _
        linarith
      have hsep : R / 8 ≤ x - y := by
        have hlower : y - r ≤ l := le_max_right _ _
        have hupper : u ≤ x - R / 4 := min_le_left _ _
        linarith
      have hslope (t : ℝ) (_ht : t ∈ Icc l u) :
          R ≤ |quadraticTTStarSlope (2 * Real.pi) (2 * Real.pi) x y t| := by
        have heq : quadraticTTStarSlope (2 * Real.pi) (2 * Real.pi) x y t =
            4 * Real.pi * (y - x) := by
          unfold quadraticTTStarSlope
          ring
        rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 4 * Real.pi),
          abs_sub_comm y x, abs_of_nonneg (by linarith : 0 ≤ x - y)]
        nlinarith [Real.pi_gt_three]
      rw [hid, integral_quadraticTTStar_eq_angularQuadraticCorrelation]
      have hh := angularQuadraticCorrelation_norm_le_nonstationary_scaled
        (R := r) (B := 0) (2 * Real.pi) (2 * Real.pi) x y l u hlu hr hlen
        (fun t _ ↦ hp t) hp'.continuousOn hR hP (by norm_num)
        hslope (by simp) (fun t _ ↦ hbound t) (fun t _ ↦ hbound' t)
      simpa only [add_zero, mul_one] using hh
    · have hzero : p = 0 := by
        funext t
        by_contra hn
        have ht := hsupp t hn
        exact hlu (ht.1.trans ht.2)
      rw [hzero]
      simp only [Pi.zero_apply, zero_mul, integral_zero, norm_zero]
      positivity
  · simp only [hspatial, ↓reduceIte]
    have hzero : p = 0 := by
      funext t
      by_contra hn
      have hh := hsupport hn
      apply hspatial
      rw [abs_le]
      constructor <;> linarith [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2]
    rw [hzero]
    simp

/-- Uniform two-scale decay for two concrete smooth positive-annular
amplitudes, retaining the additional small-radius gain. -/
theorem annularQuadraticKernel_correlation_le_separated
    {a a' b b' : ℝ → ℂ} {r R D : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R / 8) (hD : 0 ≤ D)
    (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a')
    (hb : ∀ t, HasDerivAt b (b' t) t) (hb' : Continuous b')
    (hasupp : Function.support a ⊆ Icc (R / 4) R)
    (hbsupp : Function.support b ⊆ Icc (r / 4) r)
    (hab : ∀ t, ‖a t‖ ≤ D / R) (hab' : ∀ t, ‖a' t‖ ≤ D / R ^ 2)
    (hbb : ∀ t, ‖b t‖ ≤ D / r) (hbb' : ∀ t, ‖b' t‖ ≤ D / r ^ 2)
    (x y : ℝ) :
    ‖∫ t, annularQuadraticKernel a 1 (x - t) *
      conj (annularQuadraticKernel b 1 (y - t))‖ ≤
      if |y - x| ≤ 2 * R then 6 * D ^ 2 / (r * R ^ 2) else 0 := by
  let p : ℝ → ℂ := fun t ↦ a (x - t) * conj (b (y - t))
  let p' : ℝ → ℂ := fun t ↦
    (-a' (x - t)) * conj (b (y - t)) + a (x - t) * conj (-b' (y - t))
  let P : ℝ := 2 * D ^ 2 / (r * R)
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
      {t | R / 4 ≤ x - t ∧ x - t ≤ R ∧ r / 4 ≤ y - t ∧ y - t ≤ r} := by
    intro t ht
    have hat : a (x - t) ≠ 0 := by
      intro hz
      exact ht (by simp [p, hz])
    have hbt : b (y - t) ≠ 0 := by
      intro hz
      exact ht (by simp [p, hz])
    exact ⟨(hasupp hat).1, (hasupp hat).2, (hbsupp hbt).1, (hbsupp hbt).2⟩
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpnorm (t : ℝ) : ‖p t‖ ≤ P := by
    calc
      ‖p t‖ = ‖a (x - t)‖ * ‖b (y - t)‖ := by simp [p]
      _ ≤ (D / R) * (D / r) :=
        mul_le_mul (hab _) (hbb _) (norm_nonneg _) (by positivity)
      _ = D ^ 2 / (r * R) := by ring
      _ ≤ P := by
        dsimp [P]
        rw [mul_div_assoc]
        nlinarith [div_nonneg (sq_nonneg D) (mul_pos hr hR).le]
  have hpdnorm (t : ℝ) : ‖p' t‖ ≤ P / r := by
    calc
      ‖p' t‖ ≤ ‖(-a' (x - t)) * conj (b (y - t))‖ +
          ‖a (x - t) * conj (-b' (y - t))‖ := norm_add_le _ _
      _ = ‖a' (x - t)‖ * ‖b (y - t)‖ + ‖a (x - t)‖ * ‖b' (y - t)‖ := by
        simp only [norm_mul, norm_neg, RCLike.norm_conj]
      _ ≤ (D / R ^ 2) * (D / r) + (D / R) * (D / r ^ 2) := by
        apply add_le_add
        · exact mul_le_mul (hab' _) (hbb _) (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hab _) (hbb' _) (norm_nonneg _) (by positivity)
      _ = (D ^ 2 / (r * R)) * (1 / R + 1 / r) := by field_simp
      _ ≤ (D ^ 2 / (r * R)) * (1 / r + 1 / r) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (one_div_le_one_div_of_le hr (by linarith)) le_rfl) (by positivity)
      _ = P / r := by dsimp [P]; field_simp; ring
  have h := krauseLacey_twoScaleCorrelation_le hr hR hrR hP hp hp' x y hsupp hpnorm hpdnorm
  have hconst : 3 * P / R = 6 * D ^ 2 / (r * R ^ 2) := by dsimp [P]; ring
  simp_rw [annularQuadraticKernel_mul_conj]
  simpa only [p, hconst] using h

/-- KL18 (2.6), proved for the project's actual positive dyadic quadratic
kernel. The scale gap is three and the small index is at least one. -/
theorem krauseLacey_crossScalePositiveDyadicCorrelation_le
    (j k : ℤ) (hj : 1 ≤ j) (hjk : j + 3 ≤ k) (x y : ℝ) :
    let R := (2 : ℝ) ^ (k - 1)
    ‖∫ t, annularQuadraticKernel (positiveDyadicAmplitude k) 1 (x - t) *
      conj (annularQuadraticKernel (positiveDyadicAmplitude j) 1 (y - t))‖ ≤
      if |y - x| ≤ 2 * R then 6 * positiveDyadicAmplitudeBound ^ 2 / R ^ 2 else 0 := by
  dsimp only
  let r : ℝ := (2 : ℝ) ^ (j - 1)
  let R : ℝ := (2 : ℝ) ^ (k - 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hrone : 1 ≤ r := by
    change (2 : ℝ) ^ (0 : ℤ) ≤ (2 : ℝ) ^ (j - 1)
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hrR : r ≤ R / 8 := by
    have heq : R / 8 = (2 : ℝ) ^ (k - 4) := by
      dsimp [R]
      rw [show k - 1 = (k - 4) + 3 by ring, zpow_add₀ (by norm_num)]
      norm_num
    rw [heq]
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have h := annularQuadraticKernel_correlation_le_separated hr hR hrR
    positiveDyadicAmplitudeBound_nonneg
    (hasDerivAt_positiveDyadicAmplitude k) (continuous_positiveDyadicAmplitudeDerivative k)
    (hasDerivAt_positiveDyadicAmplitude j) (continuous_positiveDyadicAmplitudeDerivative j)
    (positiveDyadicAmplitude_support_subset k) (positiveDyadicAmplitude_support_subset j)
    (norm_positiveDyadicAmplitude_le k) (norm_positiveDyadicAmplitudeDerivative_le k)
    (norm_positiveDyadicAmplitude_le j) (norm_positiveDyadicAmplitudeDerivative_le j) x y
  apply h.trans
  split_ifs
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith [sq_nonneg R] : R ^ 2 ≤ r * R ^ 2)
  · exact le_rfl


end QuadraticCarleson
