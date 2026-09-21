/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyDyadicLocalization
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingCorrelation
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingSigned

/-!
# The degree-two positive-half correlation in Krause--Lacey

This module proves the degree-two specialization of the oscillatory kernel
estimate (2.4) used at the start of the proof of Krause--Lacey Lemma 3.5.
For the positive-half kernel `ψₖ(y) = e(y²) ρₖ⁺(y)`, its `TT*`
correlation is `O(R⁻¹)` in a fixed neighborhood of the diagonal,
`O(R⁻²)` away from that neighborhood, and vanishes outside a constant
multiple of the annular radius `R`.

The off-diagonal gain is obtained from the project's proved quadratic
integration-by-parts theorem. When the two modulations are both one, the
quadratic term in the `TT*` phase cancels and its slope is the constant
`4π(y-x)`. No local `L¹ → L^q` estimate or sparse bound is assumed here.
-/

open Function MeasureTheory Set
open scoped ComplexConjugate Interval

namespace QuadraticCarleson


/-- A source-normalized same-scale correlation estimate for a smooth
positive-annular amplitude. The constant `P` controls the product amplitude
and `P/R` controls its derivative. -/
theorem krauseLacey_sameScaleCorrelation_le
    {R P : ℝ} (hR : 0 < R) (hP : 0 ≤ P)
    {p p' : ℝ → ℂ} (hp : ∀ t, HasDerivAt p (p' t) t) (hp' : Continuous p')
    (x y : ℝ)
    (hsupport : Function.support p ⊆
      {t | R / 4 ≤ x - t ∧ x - t ≤ R ∧ R / 4 ≤ y - t ∧ y - t ≤ R})
    (hbound : ∀ t, ‖p t‖ ≤ P) (hbound' : ∀ t, ‖p' t‖ ≤ P / R) :
    ‖∫ t, p t * phase (quadraticTTStarPhase 1 1 x y t)‖ ≤
      if |y - x| ≤ 2 * R then
        if |y - x| < 1 / 2 then P * R else P
      else 0 := by
  let l : ℝ := max (x - R) (y - R)
  let r : ℝ := min (x - R / 4) (y - R / 4)
  have hsupp (t : ℝ) (ht : p t ≠ 0) : t ∈ Icc l r := by
    have hh := hsupport ht
    change max (x - R) (y - R) ≤ t ∧ t ≤ min (x - R / 4) (y - R / 4)
    rw [max_le_iff, le_min_iff]
    constructor <;> constructor <;> linarith [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2]
  by_cases hspatial : |y - x| ≤ 2 * R
  · simp only [hspatial, ↓reduceIte]
    by_cases hlr : l ≤ r
    · have hzero (t : ℝ) (ht : t ∉ Icc l r) : p t = 0 := by
        by_contra hn
        exact ht (hsupp t hn)
      have hid : (∫ t, p t * phase (quadraticTTStarPhase 1 1 x y t)) =
          ∫ t in l..r, p t * phase (quadraticTTStarPhase 1 1 x y t) := by
        calc
          _ = ∫ t in Icc l r, p t * phase (quadraticTTStarPhase 1 1 x y t) :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero
              (fun t ht ↦ by rw [hzero t ht, zero_mul])).symm
          _ = ∫ t in Ioc l r, p t * phase (quadraticTTStarPhase 1 1 x y t) :=
            integral_Icc_eq_integral_Ioc
          _ = _ := (intervalIntegral.integral_of_le hlr).symm
      have hlen : r - l ≤ R := by
        have hlower : x - R ≤ l := le_max_left _ _
        have hupper : r ≤ x - R / 4 := min_le_left _ _
        linarith
      by_cases hnear : |y - x| < 1 / 2
      · simp only [hnear, ↓reduceIte]
        rw [hid]
        have htriv := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := l) (b := r) (C := P)
          (f := fun t ↦ p t * phase (quadraticTTStarPhase 1 1 x y t)) (fun t _ ↦ by
            rw [norm_mul, norm_phase, mul_one]
            exact hbound t)
        rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at htriv
        exact htriv.trans (mul_le_mul_of_nonneg_left hlen hP)
      · simp only [hnear, ↓reduceIte]
        have hsep : 1 / 2 ≤ |y - x| := le_of_not_gt hnear
        have hpi : 0 < Real.pi := Real.pi_pos
        let delta : ℝ := 4 * Real.pi * |y - x|
        have hdelta : 0 < delta := by dsimp [delta]; positivity
        have hslope (t : ℝ) (_ht : t ∈ Icc l r) :
            delta ≤ |quadraticTTStarSlope (2 * Real.pi) (2 * Real.pi) x y t| := by
          have heq : quadraticTTStarSlope (2 * Real.pi) (2 * Real.pi) x y t =
              4 * Real.pi * (y - x) := by
            unfold quadraticTTStarSlope
            ring
          rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 4 * Real.pi)]
        have hoff :
            ‖∫ t in l..r, p t * phase (quadraticTTStarPhase 1 1 x y t)‖ ≤
              (3 + 0) * P / delta := by
          rw [integral_quadraticTTStar_eq_angularQuadraticCorrelation]
          have hh := angularQuadraticCorrelation_norm_le_nonstationary_scaled
            (R := R) (B := 0) (2 * Real.pi) (2 * Real.pi) x y l r hlr hR hlen
            (fun t _ ↦ hp t) hp'.continuousOn hdelta hP (by norm_num)
            hslope (by simp) (fun t _ ↦ hbound t) (fun t _ ↦ hbound' t)
          simpa only [mul_one] using hh
        have hlast : (3 + 0) * P / delta ≤ P := by
          apply (div_le_iff₀ hdelta).2
          have hthree : 3 ≤ delta := by
            dsimp [delta]
            nlinarith [Real.pi_gt_three]
          nlinarith
        calc
          ‖∫ t, p t * phase (quadraticTTStarPhase 1 1 x y t)‖ =
              ‖∫ t in l..r, p t * phase (quadraticTTStarPhase 1 1 x y t)‖ :=
            congrArg norm hid
          _ ≤ (3 + 0) * P / delta := hoff
          _ ≤ P := hlast
    · have hzero : p = 0 := by
        funext t
        by_contra hn
        have ht := hsupp t hn
        exact hlr (ht.1.trans ht.2)
      rw [hzero]
      simp only [Pi.zero_apply, zero_mul, integral_zero, norm_zero]
      split_ifs <;> positivity
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

/-- KL18 (2.4), specialized to degree two and to the project's concrete
positive-half dyadic amplitude. Here `R = 2^(j-1)` is the proved outer
support radius. The explicit cutoff constant is finite and was constructed
from cutoff smoothness and compact support in
`QuadraticFixedHeightAveragingAmplitude`. -/
theorem krauseLacey_positiveDyadicCorrelation_le (j : ℤ) (x y : ℝ) :
    let R := (2 : ℝ) ^ (j - 1)
    ‖∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) *
      conj (annularQuadraticKernel (positiveDyadicAmplitude j) 1 (y - t))‖ ≤
      if |y - x| ≤ 2 * R then
        if |y - x| < 1 / 2 then
          2 * positiveDyadicAmplitudeBound ^ 2 / R
        else 2 * positiveDyadicAmplitudeBound ^ 2 / R ^ 2
      else 0 := by
  dsimp only
  let R : ℝ := (2 : ℝ) ^ (j - 1)
  let D : ℝ := positiveDyadicAmplitudeBound
  let a : ℝ → ℂ := positiveDyadicAmplitude j
  let a' : ℝ → ℂ := positiveDyadicAmplitudeDerivative j
  let p : ℝ → ℂ := fun t ↦ a (x - t) * conj (a (y - t))
  let p' : ℝ → ℂ := fun t ↦
    (-a' (x - t)) * conj (a (y - t)) + a (x - t) * conj (-a' (y - t))
  let P : ℝ := 2 * D ^ 2 / R ^ 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 ≤ D := positiveDyadicAmplitudeBound_nonneg
  have ha (t : ℝ) : HasDerivAt a (a' t) t := hasDerivAt_positiveDyadicAmplitude j t
  have ha' : Continuous a' := continuous_positiveDyadicAmplitudeDerivative j
  have hac : Continuous a := continuous_iff_continuousAt.mpr (fun t ↦ (ha t).continuousAt)
  have hpa (z t : ℝ) : HasDerivAt (fun t ↦ a (z - t)) (-a' (z - t)) t := by
    simpa only [Function.comp_def, zero_sub, neg_one_smul] using
      (ha (z - t)).scomp t ((hasDerivAt_const t z).sub (hasDerivAt_id t))
  have hp (t : ℝ) : HasDerivAt p (p' t) t := (hpa x t).mul (hpa y t).star
  have hp' : Continuous p' := by
    exact ((ha'.comp (continuous_const.sub continuous_id)).neg.mul
      (Complex.continuous_conj.comp (hac.comp (continuous_const.sub continuous_id)))).add
      ((hac.comp (continuous_const.sub continuous_id)).mul
        (Complex.continuous_conj.comp (ha'.comp (continuous_const.sub continuous_id)).neg))
  have hsupp : Function.support p ⊆
      {t | R / 4 ≤ x - t ∧ x - t ≤ R ∧ R / 4 ≤ y - t ∧ y - t ≤ R} := by
    intro t ht
    have hat : a (x - t) ≠ 0 := by
      intro hz
      exact ht (by simp [p, hz])
    have hbt : a (y - t) ≠ 0 := by
      intro hz
      exact ht (by simp [p, hz])
    have hxamp := positiveDyadicAmplitude_support_subset j hat
    have hyamp := positiveDyadicAmplitude_support_subset j hbt
    exact ⟨hxamp.1, hxamp.2, hyamp.1, hyamp.2⟩
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpbound (t : ℝ) : ‖p t‖ ≤ P := by
    calc
      ‖p t‖ = ‖a (x - t)‖ * ‖a (y - t)‖ := by simp [p]
      _ ≤ (D / R) * (D / R) :=
        mul_le_mul (norm_positiveDyadicAmplitude_le j _) (norm_positiveDyadicAmplitude_le j _)
          (norm_nonneg _) (by positivity)
      _ ≤ P := by
        have hbase : 0 ≤ D ^ 2 / R ^ 2 := div_nonneg (sq_nonneg D) (sq_nonneg R)
        dsimp [P]
        calc
          D / R * (D / R) = D ^ 2 / R ^ 2 := by ring
          _ ≤ 2 * (D ^ 2 / R ^ 2) := by linarith
          _ = 2 * D ^ 2 / R ^ 2 := by ring
  have hp'bound (t : ℝ) : ‖p' t‖ ≤ P / R := by
    calc
      ‖p' t‖ ≤ ‖(-a' (x - t)) * conj (a (y - t))‖ +
          ‖a (x - t) * conj (-a' (y - t))‖ := norm_add_le _ _
      _ = ‖a' (x - t)‖ * ‖a (y - t)‖ + ‖a (x - t)‖ * ‖a' (y - t)‖ := by
        simp only [norm_mul, norm_neg, RCLike.norm_conj]
      _ ≤ (D / R ^ 2) * (D / R) + (D / R) * (D / R ^ 2) := by
        apply add_le_add
        · exact mul_le_mul (norm_positiveDyadicAmplitudeDerivative_le j _)
            (norm_positiveDyadicAmplitude_le j _) (norm_nonneg _) (by positivity)
        · exact mul_le_mul (norm_positiveDyadicAmplitude_le j _)
            (norm_positiveDyadicAmplitudeDerivative_le j _) (norm_nonneg _) (by positivity)
      _ = P / R := by dsimp [P]; field_simp; ring
  have h := krauseLacey_sameScaleCorrelation_le hR hP hp hp' x y hsupp hpbound hp'bound
  have hPR : P * R = 2 * D ^ 2 / R := by
    dsimp [P]
    field_simp
  simp_rw [annularQuadraticKernel_mul_conj]
  simpa only [p, hPR, P, D, R] using h

/-- Adapter from the sharp two-region KL18 correlation estimate to the
project's integrable quadratic majorant. Its small parameter is the exact
relative diagonal width `u = 1/(2R)`, so the resulting `TT*` mass is
`O(D²/R)`, as in the source's `2^(-k)` estimate. -/
theorem krauseLacey_positiveDyadicCorrelation_le_projectMajorant
    (j : ℤ) (x y : ℝ) :
    let R := (2 : ℝ) ^ (j - 1)
    ‖∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) *
      conj (annularQuadraticKernel (positiveDyadicAmplitude j) 1 (y - t))‖ ≤
      quadraticFixedHeightMajorant (2 * positiveDyadicAmplitudeBound ^ 2)
        (1 / (2 * R)) R (x - y) := by
  dsimp only
  let R : ℝ := (2 : ℝ) ^ (j - 1)
  let D : ℝ := positiveDyadicAmplitudeBound
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 ≤ D := positiveDyadicAmplitudeBound_nonneg
  have h := krauseLacey_positiveDyadicCorrelation_le j x y
  change ‖∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) *
      conj (annularQuadraticKernel (positiveDyadicAmplitude j) 1 (y - t))‖ ≤
    if |y - x| ≤ 2 * R then
      if |y - x| < 1 / 2 then 2 * D ^ 2 / R else 2 * D ^ 2 / R ^ 2
    else 0 at h
  unfold quadraticFixedHeightMajorant
  rw [abs_sub_comm x y]
  change ‖∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) *
      conj (annularQuadraticKernel (positiveDyadicAmplitude j) 1 (y - t))‖ ≤
    if |y - x| ≤ 2 * R then
      2 * D ^ 2 / R * (if |y - x| < 1 / (2 * R) * R then
        1 else 8403968 * (1 / (2 * R)))
    else 0
  by_cases hout : |y - x| ≤ 2 * R
  · simp only [hout, ↓reduceIte] at h ⊢
    have huR : 1 / (2 * R) * R = 1 / 2 := by field_simp
    rw [huR]
    by_cases hnear : |y - x| < 1 / 2
    · simp only [hnear, ↓reduceIte] at h ⊢
      simpa only [mul_one] using h
    · simp only [hnear, ↓reduceIte] at h ⊢
      apply h.trans
      have hbase : 0 ≤ D ^ 2 / R ^ 2 := div_nonneg (sq_nonneg D) (sq_nonneg R)
      calc
        2 * D ^ 2 / R ^ 2 = 2 * (D ^ 2 / R ^ 2) := by ring
        _ ≤ 8403968 * (D ^ 2 / R ^ 2) := by nlinarith
        _ = 2 * D ^ 2 / R * (8403968 * (1 / (2 * R))) := by
          field_simp
  · simp only [hout, ↓reduceIte] at h ⊢
    exact h

/-- The first `L²` consequence of KL18 (2.4): a concrete degree-two
positive-half dyadic convolution has squared `L²` norm `O(R⁻¹)`, hence
operator norm `O(R⁻¹/²)`. This is the oscillatory endpoint used in the
interpolation step of Proposition 4.1. -/
theorem krauseLacey_positiveDyadicConvolution_sq_lintegral_le
    (j : ℤ) {f : ℝ → ℂ} (hf : MemLp f 2) :
    let R := (2 : ℝ) ^ (j - 1)
    (∫⁻ x, ‖∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) * f t‖ₑ ^ 2) ≤
      ENNReal.ofReal
        (2218647684 * positiveDyadicAmplitudeBound ^ 2 / R) *
          ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  dsimp only
  let R : ℝ := (2 : ℝ) ^ (j - 1)
  let D : ℝ := positiveDyadicAmplitudeBound
  let κ : Fin 1 → ℝ → ℂ := fun _ ↦
    annularQuadraticKernel (positiveDyadicAmplitude j) 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 ≤ D := positiveDyadicAmplitudeBound_nonneg
  have hc : ∀ i, Continuous (κ i) := by
    intro i
    have ha : Continuous (positiveDyadicAmplitude j) :=
      continuous_iff_continuousAt.mpr
        (fun t ↦ (hasDerivAt_positiveDyadicAmplitude j t).continuousAt)
    unfold κ annularQuadraticKernel phase
    fun_prop
  have hs : ∀ i, HasCompactSupport (κ i) := by
    intro i
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (R / 4) R))
    intro t ht
    apply positiveDyadicAmplitude_support_subset j
    intro hz
    exact ht (by simp [κ, annularQuadraticKernel, hz])
  have hmax := finiteConvolutionMaximal_sq_lintegral_le_of_quadraticFixedHeightMajorant
    0 κ hc hs (fun _ ↦ R) (fun _ ↦ hR)
    (show 0 ≤ 2 * D ^ 2 by positivity)
    (show 0 < 1 / (2 * R) by positivity)
    (fun _ _ x y ↦ by
      simpa only [κ, D, max_self] using
        krauseLacey_positiveDyadicCorrelation_le_projectMajorant j x y) hf
  have hpoint (x : ℝ) :
      ‖∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) * f t‖ₑ ≤
        finiteConvolutionMaximal κ f x := by
    exact le_iSup_of_le (0 : Fin 1) (by simp only [κ]; exact le_rfl)
  calc
    (∫⁻ x, ‖∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) * f t‖ₑ ^ 2) ≤
        ∫⁻ x, finiteConvolutionMaximal κ f x ^ 2 := by
      apply lintegral_mono
      intro x
      exact pow_le_pow_left₀ bot_le (hpoint x) 2
    _ ≤ ENNReal.ofReal (2218647684 * (2 * D ^ 2) * (1 / (2 * R))) *
        ∫⁻ x, ‖f x‖ₑ ^ 2 := hmax
    _ = ENNReal.ofReal (2218647684 * positiveDyadicAmplitudeBound ^ 2 / R) *
        ∫⁻ x, ‖f x‖ₑ ^ 2 := by
      rw [show 2218647684 * (2 * D ^ 2) * (1 / (2 * R)) =
          2218647684 * positiveDyadicAmplitudeBound ^ 2 / R by
        dsimp [D]
        field_simp]

/-- Exact adapter between KL18's convolution orientation in display (3.2)
and the project's convolution orientation used by the `TT*` theorem. -/
theorem krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution
    (j : ℤ) (I : RealInterval) (f : ℝ → ℂ) (x : ℝ) :
    krauseLaceyLocalizedPiece 1 j I f x =
      ∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) *
        I.centralThird.indicator f t := by
  let F : ℝ → ℂ := fun t ↦
    annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) *
      I.centralThird.indicator f t
  unfold krauseLaceyLocalizedPiece
  calc
    (∫ y, positiveDyadicAmplitude j y * phase (1 * y ^ 2) *
        I.centralThird.indicator f (x - y)) = ∫ y, F (x - y) := by
      apply integral_congr_ae
      filter_upwards with y
      have hxy : x - (x - y) = y := by ring
      simp only [F, annularQuadraticKernel, one_mul]
      rw [hxy]
    _ = ∫ t, F t := MeasureTheory.integral_sub_left_eq_self F volume x
    _ = _ := rfl

/-- The finite fixed-scale sum `T_ℐ` from KL18 (3.3), restricted here to
one dyadic scale. -/
noncomputable def krauseLaceyFixedScaleLocalizedSum
    (j : ℤ) (S : Finset RealInterval) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ I ∈ S, krauseLaceyLocalizedPiece 1 j I f x

/-- The input obtained by summing the central-third restrictions at one
fixed scale. -/
noncomputable def krauseLaceyFixedScaleInput
    (S : Finset RealInterval) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ I ∈ S, I.centralThird.indicator f x

/-- At a fixed scale, the sum of KL18 localized pieces is exactly one genuine
dyadic convolution applied to the sum of central-third restrictions. -/
theorem krauseLaceyFixedScaleLocalizedSum_eq_convolution
    (j : ℤ) (S : Finset RealInterval) {f : ℝ → ℂ} (hf : MemLp f 2)
    (x : ℝ) :
    krauseLaceyFixedScaleLocalizedSum j S f x =
      ∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) *
        krauseLaceyFixedScaleInput S f t := by
  classical
  let κ : ℝ → ℂ := annularQuadraticKernel (positiveDyadicAmplitude j) 1
  have hκc : Continuous κ := by
    have ha : Continuous (positiveDyadicAmplitude j) :=
      continuous_iff_continuousAt.mpr
        (fun t ↦ (hasDerivAt_positiveDyadicAmplitude j t).continuousAt)
    unfold κ annularQuadraticKernel phase
    fun_prop
  have hκs : HasCompactSupport κ := by
    let R : ℝ := (2 : ℝ) ^ (j - 1)
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (R / 4) R))
    intro t ht
    apply positiveDyadicAmplitude_support_subset j
    intro hz
    exact ht (by simp [κ, annularQuadraticKernel, hz])
  have hint (I : RealInterval) (hI : I ∈ S) :
      Integrable (fun t ↦ κ (x - t) * I.centralThird.indicator f t) :=
    integrable_convolution_row_of_memLp hκc hκs
      (MeasureTheory.MemLp.indicator I.measurableSet_centralThird hf) x
  unfold krauseLaceyFixedScaleLocalizedSum
  simp_rw [krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution]
  calc
    ∑ I ∈ S, ∫ t, κ (x - t) * I.centralThird.indicator f t =
        ∫ t, ∑ I ∈ S, κ (x - t) * I.centralThird.indicator f t :=
      (integral_finsetSum S (fun I hI ↦ hint I hI)).symm
    _ = ∫ t, κ (x - t) * krauseLaceyFixedScaleInput S f t := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [krauseLaceyFixedScaleInput, Finset.mul_sum]
    _ = _ := rfl

theorem memLp_krauseLaceyFixedScaleInput
    (S : Finset RealInterval) {f : ℝ → ℂ} (hf : MemLp f 2) :
    MemLp (krauseLaceyFixedScaleInput S f) 2 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hz : krauseLaceyFixedScaleInput ∅ f = 0 := by
        funext x
        simp [krauseLaceyFixedScaleInput]
      rw [hz]
      exact MeasureTheory.MemLp.zero
  | @insert I S hI ih =>
      have hadd : krauseLaceyFixedScaleInput (insert I S) f =
          I.centralThird.indicator f + krauseLaceyFixedScaleInput S f := by
        funext x
        simp [krauseLaceyFixedScaleInput, hI]
      rw [hadd]
      exact (MeasureTheory.MemLp.indicator I.measurableSet_centralThird hf).add ih

/-- Disjoint central thirds prevent any multiplicity loss in the fixed-scale
input assembled from the shifted dyadic grid. -/
theorem norm_krauseLaceyFixedScaleInput_le
    (S : Finset RealInterval) (f : ℝ → ℂ)
    (hdisj : Set.Pairwise (↑S : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.centralThird)) (x : ℝ) :
    ‖krauseLaceyFixedScaleInput S f x‖ ≤ ‖f x‖ := by
  classical
  by_cases hex : ∃ I ∈ S, x ∈ I.centralThird
  · rcases hex with ⟨I, hIS, hxI⟩
    have hsum : krauseLaceyFixedScaleInput S f x = f x := by
      unfold krauseLaceyFixedScaleInput
      rw [Finset.sum_eq_single I]
      · exact Set.indicator_of_mem hxI f
      · intro J hJS hJI
        have hd := hdisj hIS hJS hJI.symm
        have hxJ : x ∉ J.centralThird := by
          intro hx
          exact Set.disjoint_left.1 hd hxI hx
        simp [hxJ]
      · intro hn
        exact (hn hIS).elim
    rw [hsum]
  · have hnone : ∀ I ∈ S, x ∉ I.centralThird := by
      intro I hIS hxI
      exact hex ⟨I, hIS, hxI⟩
    have hzero : krauseLaceyFixedScaleInput S f x = 0 := by
      unfold krauseLaceyFixedScaleInput
      apply Finset.sum_eq_zero
      intro I hIS
      simp [hnone I hIS]
    rw [hzero, norm_zero]
    exact norm_nonneg _

/-- Fixed-scale finite-collection form of the KL18 oscillatory `L²` input.
It is an unconditional consequence of (2.4); no maximal or sparse estimate is
assumed. -/
theorem krauseLaceyFixedScaleLocalizedSum_sq_lintegral_le
    (j : ℤ) (S : Finset RealInterval) {f : ℝ → ℂ} (hf : MemLp f 2) :
    let R := (2 : ℝ) ^ (j - 1)
    (∫⁻ x, ‖krauseLaceyFixedScaleLocalizedSum j S f x‖ₑ ^ 2) ≤
      ENNReal.ofReal
        (2218647684 * positiveDyadicAmplitudeBound ^ 2 / R) *
          ∫⁻ x, ‖krauseLaceyFixedScaleInput S f x‖ₑ ^ 2 := by
  dsimp only
  simp_rw [krauseLaceyFixedScaleLocalizedSum_eq_convolution j S hf]
  exact krauseLacey_positiveDyadicConvolution_sq_lintegral_le j
    (memLp_krauseLaceyFixedScaleInput S hf)

/-- The fixed-scale oscillatory `L²` estimate in the form used in KL18
Proposition 4.1: a pairwise-disjoint grid collection costs no multiplicity
factor. -/
theorem krauseLaceyFixedScaleLocalizedSum_sq_lintegral_le_of_disjoint
    (j : ℤ) (S : Finset RealInterval) {f : ℝ → ℂ} (hf : MemLp f 2)
    (hdisj : Set.Pairwise (↑S : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.centralThird)) :
    let R := (2 : ℝ) ^ (j - 1)
    (∫⁻ x, ‖krauseLaceyFixedScaleLocalizedSum j S f x‖ₑ ^ 2) ≤
      ENNReal.ofReal
        (2218647684 * positiveDyadicAmplitudeBound ^ 2 / R) *
          ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  dsimp only
  have hlocal := krauseLaceyFixedScaleLocalizedSum_sq_lintegral_le j S hf
  apply hlocal.trans
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro x
  apply pow_le_pow_left₀ bot_le _ 2
  simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal
    (norm_krauseLaceyFixedScaleInput_le S f hdisj x)

/-- The localized operator in KL18 display (3.2) inherits the concrete
fixed-scale squared-`L²` decay. The right side retains the exact central-third
restriction, ready for the disjoint-grid summation in Proposition 4.1. -/
theorem krauseLaceyLocalizedPiece_sq_lintegral_le
    (j : ℤ) (I : RealInterval) {f : ℝ → ℂ} (hf : MemLp f 2) :
    let R := (2 : ℝ) ^ (j - 1)
    (∫⁻ x, ‖krauseLaceyLocalizedPiece 1 j I f x‖ₑ ^ 2) ≤
      ENNReal.ofReal
        (2218647684 * positiveDyadicAmplitudeBound ^ 2 / R) *
          ∫⁻ x, ‖I.centralThird.indicator f x‖ₑ ^ 2 := by
  dsimp only
  simp_rw [krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution]
  exact krauseLacey_positiveDyadicConvolution_sq_lintegral_le j
    (MeasureTheory.MemLp.indicator I.measurableSet_centralThird hf)

end QuadraticCarleson
