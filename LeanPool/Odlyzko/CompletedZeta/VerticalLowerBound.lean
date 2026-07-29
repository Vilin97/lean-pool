/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquation
public import LeanPool.Odlyzko.CompletedZeta.GammaFactor
public import LeanPool.Odlyzko.CompletedZeta.TotallyComplex
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealEulerProduct
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealSummability
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Vertical Lower Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A dedekind zeta inverse vertical majorant used in the Odlyzko-bound argument. -/
noncomputable def dedekindZetaInverseVerticalMajorant : ℝ :=
  Real.exp <| ∑' P : HeightOneSpectrum (𝓞 K),
    (primeIdealNorm K P : ℝ) ^ (-(2 : ℝ))

lemma one_le_dedekindZetaInverseVerticalMajorant :
    1 ≤ dedekindZetaInverseVerticalMajorant K := by
  rw [dedekindZetaInverseVerticalMajorant]
  exact Real.one_le_exp <| tsum_nonneg
    (fun _ ↦ Real.rpow_nonneg (by positivity) _)

private lemma norm_one_sub_inverseNormPower_two_add_mul_I_le
    (P : HeightOneSpectrum (𝓞 K)) (t : ℝ) :
    ‖1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖ ≤
      1 + (primeIdealNorm K P : ℝ) ^ (-(2 : ℝ)) := by
  calc
    ‖1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖
        ≤ ‖(1 : ℂ)‖ +
            ‖-inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖ :=
      norm_add_le _ _
    _ = 1 + (primeIdealNorm K P : ℝ) ^ (-(2 : ℝ)) := by
      rw [norm_one, norm_neg, norm_inverseNormPower _ (Nat.zero_lt_of_lt
        (one_lt_primeIdealNorm K P))]
      simp

private lemma multipliable_one_sub_inverseNormPower_two_add_mul_I (t : ℝ) :
    Multipliable (fun P : HeightOneSpectrum (𝓞 K) ↦
      1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)) := by
  have hnorm :
      Summable (fun P : HeightOneSpectrum (𝓞 K) ↦
        ‖-inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖) := by
    simpa [norm_inverseNormPower, Nat.zero_lt_of_lt (one_lt_primeIdealNorm K _)] using
      (summable_primeIdealNorm_rpow K (show (1 : ℝ) < 2 by norm_num))
  have h := multipliable_one_add_of_summable (R := ℂ) hnorm
  grind

private lemma one_sub_inverseNormPower_two_add_mul_I_hasProd (t : ℝ) :
    HasProd
      (fun P : HeightOneSpectrum (𝓞 K) ↦
        1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I))
      (NumberField.dedekindZeta K (2 + t * Complex.I))⁻¹ := by
  let s : ℂ := 2 + t * Complex.I
  have hs : 1 < s.re := by simp [s]
  have hf := multipliable_primeIdealFactor K hs
  have hg := multipliable_one_sub_inverseNormPower_two_add_mul_I K t
  have hmul := hf.tprod_mul hg
  have hzeta :
      ∏' P : HeightOneSpectrum (𝓞 K), primeIdealFactor K P s =
        NumberField.dedekindZeta K s :=
    dedekindZeta_primeIdeal_eulerProduct_tprod K hs
  have hleft :
      ∏' P : HeightOneSpectrum (𝓞 K),
        primeIdealFactor K P s *
          (1 + -inverseNormPower (primeIdealNorm K P) s) = 1 := by
    have hfactor : ∀ P : HeightOneSpectrum (𝓞 K),
        primeIdealFactor K P s *
          (1 + -inverseNormPower (primeIdealNorm K P) s) = 1 := by
      intro P
      rw [primeIdealFactor, localFactor]
      exact inv_mul_cancel₀ <| by
        simpa [sub_eq_add_neg] using one_sub_inverseNormPower_ne_zero
          (one_lt_primeIdealNorm K P) (zero_lt_one.trans hs)
    simp only [hfactor, tprod_one]
  rw [hleft, hzeta] at hmul
  have htprod :
      ∏' P : HeightOneSpectrum (𝓞 K),
        (1 + -inverseNormPower (primeIdealNorm K P) s) =
          (NumberField.dedekindZeta K s)⁻¹ := by grind
  rw [← htprod]
  exact hg.hasProd

theorem norm_inv_dedekindZeta_two_add_mul_I_le (t : ℝ) :
    ‖(NumberField.dedekindZeta K (2 + t * Complex.I))⁻¹‖ ≤
      dedekindZetaInverseVerticalMajorant K := by
  have hzeta :
      HasProd
        (fun P : HeightOneSpectrum (𝓞 K) ↦
          ‖1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖)
        ‖(NumberField.dedekindZeta K (2 + t * Complex.I))⁻¹‖ := by
    exact (one_sub_inverseNormPower_two_add_mul_I_hasProd K t).norm
  apply hasProd_le_of_prod_le hzeta
  intro S
  calc
    ∏ P ∈ S,
        ‖1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖ ≤
        ∏ P ∈ S, (1 + (primeIdealNorm K P : ℝ) ^ (-(2 : ℝ))) := by
      exact Finset.prod_le_prod
        (fun _ _ ↦ norm_nonneg _)
        (fun P _ ↦ norm_one_sub_inverseNormPower_two_add_mul_I_le K P t)
    _ ≤ Real.exp (∑ P ∈ S, (primeIdealNorm K P : ℝ) ^ (-(2 : ℝ))) :=
      Real.prod_one_add_le_exp_sum S
        (fun _ ↦ Real.rpow_nonneg (by positivity) _)
    _ ≤ dedekindZetaInverseVerticalMajorant K := by
      rw [dedekindZetaInverseVerticalMajorant]
      exact Real.exp_le_exp.mpr <|
        (summable_primeIdealNorm_rpow K (by norm_num)).sum_le_tsum S
          (fun _ _ ↦ Real.rpow_nonneg (by positivity) _)

theorem one_le_dedekindZetaInverseVerticalMajorant_mul_norm (t : ℝ) :
    1 ≤ dedekindZetaInverseVerticalMajorant K *
      ‖NumberField.dedekindZeta K (2 + t * Complex.I)‖ := by
  have hs : 1 < (2 + t * Complex.I : ℂ).re := by simp
  have hzeta : NumberField.dedekindZeta K (2 + t * Complex.I) ≠ 0 := by
    rw [← dedekindZeta_primeIdeal_eulerProduct_tprod K hs]
    exact tprod_primeIdealFactor_ne_zero K hs
  have h := mul_le_mul_of_nonneg_right
    (norm_inv_dedekindZeta_two_add_mul_I_le K t)
    (norm_nonneg (NumberField.dedekindZeta K (2 + t * Complex.I)))
  simp_all

end NumberField.Odlyzko

end

section

open Complex

namespace NumberField.Odlyzko

theorem Gamma_one_add_mul_I_mul_Gamma_one_sub_mul_I
    {t : ℝ} (ht : t ≠ 0) :
    Complex.Gamma (1 + t * I) * Complex.Gamma (1 - t * I) =
      (Real.pi * t / Real.sinh (Real.pi * t) : ℝ) := by
  have htI : (t : ℂ) * I ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr ht) I_ne_zero
  have hreflect :=
    Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * I)
  have hrec :
      Complex.Gamma (1 + t * I) =
        ((t : ℂ) * I) * Complex.Gamma ((t : ℂ) * I) := by
    rw [show (1 : ℂ) + t * I = (t : ℂ) * I + 1 by ring]
    exact Complex.Gamma_add_one ((t : ℂ) * I) htI
  rw [hrec, mul_assoc, hreflect]
  rw [show (Real.pi : ℂ) * ((t : ℂ) * I) =
      ((Real.pi * t : ℝ) : ℂ) * I by
        push_cast
        ring]
  rw [Complex.sin_mul_I]
  push_cast
  grind

theorem sq_norm_Gamma_one_add_mul_I
    {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + t * I)‖ ^ 2 =
      Real.pi * |t| / Real.sinh (Real.pi * |t|) := by
  have hconj :
      star (Complex.Gamma (1 + t * I)) =
        Complex.Gamma (1 - t * I) := by
    rw [Complex.star_def, ← Complex.Gamma_conj]
    congr 1
    apply Complex.ext <;> simp
  have hprod :=
    Gamma_one_add_mul_I_mul_Gamma_one_sub_mul_I ht
  have hnorm :
      ‖Complex.Gamma (1 + t * I)‖ ^ 2 =
        (Complex.Gamma (1 + t * I) *
          Complex.Gamma (1 - t * I)).re := by
    rw [← hconj, Complex.star_def, Complex.mul_conj, Complex.sq_norm]
    simp
  rw [hnorm, hprod]
  simp only [ofReal_re]
  by_cases htpos : 0 < t
  · grind
  · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht
    rw [abs_of_neg htneg, mul_neg, Real.sinh_neg, neg_div_neg_eq]

theorem sq_norm_Gamma_two_add_mul_I
    {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (2 + t * I)‖ ^ 2 =
      (1 + t ^ 2) *
        (Real.pi * |t| / Real.sinh (Real.pi * |t|)) := by
  have harg : (1 : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hrec :
      Complex.Gamma (2 + t * I) =
        (1 + t * I) * Complex.Gamma (1 + t * I) := by
    rw [show (2 : ℂ) + t * I = (1 + t * I) + 1 by ring]
    exact Complex.Gamma_add_one (1 + t * I) harg
  rw [hrec, norm_mul, mul_pow, sq_norm_Gamma_one_add_mul_I ht]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [add_re, one_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    zero_mul, mul_one, sub_zero, add_im, one_im, zero_add]
  ring

theorem two_mul_pi_mul_abs_mul_exp_neg_le_sq_norm_Gamma_one_add_mul_I
    {t : ℝ} (ht : t ≠ 0) :
    2 * Real.pi * |t| * Real.exp (-(Real.pi * |t|)) ≤
      ‖Complex.Gamma (1 + t * I)‖ ^ 2 := by
  rw [sq_norm_Gamma_one_add_mul_I ht]
  let x := Real.pi * |t|
  have hx : 0 < x := mul_pos Real.pi_pos (abs_pos.mpr ht)
  have hsinh : Real.sinh x ≤ Real.exp x / 2 := by
    rw [Real.sinh_eq]
    have hpos := Real.exp_pos (-x)
    linarith
  have hsinhpos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hratio :
      2 * x * Real.exp (-x) ≤ x / Real.sinh x := by
    rw [le_div_iff₀ hsinhpos]
    have hexp : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      2 * x * Real.exp (-x) * Real.sinh x ≤
          2 * x * Real.exp (-x) * (Real.exp x / 2) := by
        gcongr
      _ = x := by grind
  grind

theorem sq_norm_complexPlaceGammaFactor_two_add_mul_I
    {t : ℝ} (ht : t ≠ 0) :
    ‖CompletedZeta.complexPlaceGammaFactor (2 + t * I)‖ ^ 2 =
      (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
        (Real.pi * |t| / Real.sinh (Real.pi * |t|)) := by
  rw [complexPlaceGammaFactor_eq, norm_mul, mul_pow,
    sq_norm_Gamma_two_add_mul_I ht]
  have hbase : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hnorm :
      ‖((2 * (Real.pi : ℂ)) ^ (-(2 + t * I)))‖ =
        (2 * Real.pi) ^ (-2 : ℝ) := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by
      simp]
    (convert norm_cpow_eq_rpow_re_of_pos hbase (-(2 + t * I)) using 1; norm_num)
  rw [hnorm, ← Real.rpow_natCast]
  rw [← Real.rpow_mul hbase.le]
  grind

theorem complexPlaceGammaFactor_two_vertical_sq_lowerBound
    {t : ℝ} (ht : t ≠ 0) :
    (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
        (2 * Real.pi * |t| * Real.exp (-(Real.pi * |t|))) ≤
      ‖CompletedZeta.complexPlaceGammaFactor (2 + t * I)‖ ^ 2 := by
  rw [sq_norm_complexPlaceGammaFactor_two_add_mul_I ht]
  gcongr
  have h :=
    two_mul_pi_mul_abs_mul_exp_neg_le_sq_norm_Gamma_one_add_mul_I ht
  rw [sq_norm_Gamma_one_add_mul_I ht] at h
  grind

/-- A complex place gamma vertical lower constant used in the Odlyzko-bound argument. -/
noncomputable def complexPlaceGammaVerticalLowerConstant : ℝ :=
  (2 * Real.pi) ^ (-3 : ℝ)

theorem complexPlaceGammaVerticalLowerConstant_pos :
    0 < complexPlaceGammaVerticalLowerConstant := by
  exact Real.rpow_pos_of_pos (mul_pos (by norm_num) Real.pi_pos) _

theorem complexPlaceGammaVerticalLowerConstant_mul_exp_le_sq_norm
    {t : ℝ} (ht : 1 ≤ |t|) :
    complexPlaceGammaVerticalLowerConstant *
        Real.exp (-(Real.pi * |t|)) ≤
      ‖CompletedZeta.complexPlaceGammaFactor (2 + t * I)‖ ^ 2 := by
  have ht0 : t ≠ 0 := by grind
  apply le_trans ?_ (complexPlaceGammaFactor_two_vertical_sq_lowerBound ht0)
  have hbase : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hpow :
      complexPlaceGammaVerticalLowerConstant =
        (2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) := by
    calc
      complexPlaceGammaVerticalLowerConstant =
          (2 * Real.pi) ^ ((-4 : ℝ) + 1) := by
        rw [complexPlaceGammaVerticalLowerConstant]
        norm_num
      _ = (2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) ^ (1 : ℝ) :=
        Real.rpow_add hbase (-4 : ℝ) 1
      _ = (2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) := by simp
  rw [hpow]
  have hquad : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  calc
    (2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) *
          Real.exp (-(Real.pi * |t|))
        ≤ (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
            ((2 * Real.pi) * Real.exp (-(Real.pi * |t|))) := by
      calc
        (2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) *
              Real.exp (-(Real.pi * |t|)) =
            ((2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) *
              Real.exp (-(Real.pi * |t|))) * 1 := by ring
        _ ≤ ((2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) *
              Real.exp (-(Real.pi * |t|))) * (1 + t ^ 2) := by
          exact mul_le_mul_of_nonneg_left hquad (by positivity)
        _ = (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
              ((2 * Real.pi) * Real.exp (-(Real.pi * |t|))) := by ring
    _ ≤ (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
          (2 * Real.pi * |t| * Real.exp (-(Real.pi * |t|))) := by
      calc
        (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
              ((2 * Real.pi) * Real.exp (-(Real.pi * |t|))) =
            ((2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
              (2 * Real.pi) * Real.exp (-(Real.pi * |t|))) * 1 := by ring
        _ ≤ ((2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
              (2 * Real.pi) * Real.exp (-(Real.pi * |t|))) * |t| := by
          exact mul_le_mul_of_nonneg_left ht (by positivity)
        _ = (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
              (2 * Real.pi * |t| * Real.exp (-(Real.pi * |t|))) := by ring

end NumberField.Odlyzko

end

section

open Complex NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem norm_poleClearedCompletedDedekindZetaContinuation_two_add_mul_I
    (t : ℝ) :
    ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ =
      (Module.finrank ℚ K : ℝ) *
        ‖(2 : ℂ) + t * I‖ * ‖(1 : ℂ) - (2 + t * I)‖ *
        |(discr K : ℝ)| *
        ‖CompletedZeta.complexPlaceGammaFactor (2 + t * I)‖ ^ nrComplexPlaces K *
        ‖dedekindZeta K (2 + t * I)‖ := by
  have hs : 1 < (2 + t * I : ℂ).re := by simp
  rw [poleClearedCompletedDedekindZetaContinuation_eq_completedDedekindZeta K hs,
    completedDedekindZeta_of_isTotallyComplex,
    CompletedZeta.discriminantFactor, CompletedZeta.complexPlaceGammaFactor]
  simp only [norm_mul, norm_pow, norm_natCast]
  have hdisc :
      ‖((|(discr K : ℝ)| : ℝ) : ℂ) ^ (((2 : ℂ) + t * I) / 2)‖ =
        |(discr K : ℝ)| := by
    rw [norm_cpow_eq_rpow_re_of_pos (discr_abs_pos K)]
    simp [Real.rpow_one]
  grind

theorem completedZeta_two_vertical_factor_le_majorant_mul_norm (t : ℝ) :
    (Module.finrank ℚ K : ℝ) *
        ‖(2 : ℂ) + t * I‖ * ‖(1 : ℂ) - (2 + t * I)‖ *
        |(discr K : ℝ)| *
        ‖CompletedZeta.complexPlaceGammaFactor (2 + t * I)‖ ^ nrComplexPlaces K ≤
      dedekindZetaInverseVerticalMajorant K *
        ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ := by
  rw [norm_poleClearedCompletedDedekindZetaContinuation_two_add_mul_I]
  have hnonneg :
      0 ≤ (Module.finrank ℚ K : ℝ) *
          ‖(2 : ℂ) + t * I‖ * ‖(1 : ℂ) - (2 + t * I)‖ *
          |(discr K : ℝ)| *
          ‖CompletedZeta.complexPlaceGammaFactor (2 + t * I)‖ ^ nrComplexPlaces K := by
    positivity
  nlinarith [mul_le_mul_of_nonneg_left
    (one_le_dedekindZetaInverseVerticalMajorant_mul_norm K t) hnonneg]

theorem complexGammaExponential_pow_le_majorant_sq_mul_completedZeta_sq
    {t : ℝ} (ht : 1 ≤ |t|) :
    (complexPlaceGammaVerticalLowerConstant *
        Real.exp (-(Real.pi * |t|))) ^ nrComplexPlaces K ≤
      dedekindZetaInverseVerticalMajorant K ^ 2 *
        ‖poleClearedCompletedDedekindZetaContinuation K
          (2 + t * I)‖ ^ 2 := by
  let B : ℝ :=
    (Module.finrank ℚ K : ℝ) *
      ‖(2 : ℂ) + t * I‖ * ‖(1 : ℂ) - (2 + t * I)‖ *
      |(discr K : ℝ)|
  let G : ℝ := ‖CompletedZeta.complexPlaceGammaFactor (2 + t * I)‖
  let C : ℝ := dedekindZetaInverseVerticalMajorant K
  let X : ℝ :=
    ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖
  have hn : 1 ≤ (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hs : 1 ≤ ‖(2 : ℂ) + t * I‖ := by
    calc
      1 ≤ |((2 : ℂ) + t * I).re| := by simp
      _ ≤ ‖(2 : ℂ) + t * I‖ := Complex.abs_re_le_norm _
  have hones : 1 ≤ ‖(1 : ℂ) - (2 + t * I)‖ := by
    calc
      1 ≤ |((1 : ℂ) - (2 + t * I)).re| := by norm_num
      _ ≤ ‖(1 : ℂ) - (2 + t * I)‖ := Complex.abs_re_le_norm _
  have hdisc : 1 ≤ |(discr K : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  have hB : 1 ≤ B := by
    dsimp [B]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hn hs) hones) hdisc
  have hfactor : B * G ^ nrComplexPlaces K ≤ C * X := by
    simpa [B, G, C, X] using
      completedZeta_two_vertical_factor_le_majorant_mul_norm K t
  have hGnonneg : 0 ≤ G ^ nrComplexPlaces K := by positivity
  have hGX : G ^ nrComplexPlaces K ≤ C * X :=
    (le_mul_of_one_le_left hGnonneg hB).trans hfactor
  have hCXnonneg : 0 ≤ C * X := by grind
  have hsq : (G ^ nrComplexPlaces K) ^ 2 ≤ (C * X) ^ 2 :=
    (sq_le_sq₀ hGnonneg hCXnonneg).2 hGX
  have hgamma :
      complexPlaceGammaVerticalLowerConstant *
          Real.exp (-(Real.pi * |t|)) ≤ G ^ 2 := by
    simpa [G] using
      complexPlaceGammaVerticalLowerConstant_mul_exp_le_sq_norm ht
  calc
    (complexPlaceGammaVerticalLowerConstant *
          Real.exp (-(Real.pi * |t|))) ^ nrComplexPlaces K
        ≤ (G ^ 2) ^ nrComplexPlaces K :=
      pow_le_pow_left₀
        (mul_nonneg complexPlaceGammaVerticalLowerConstant_pos.le
          (Real.exp_pos _).le)
        hgamma _
    _ = (G ^ nrComplexPlaces K) ^ 2 := by ring
    _ ≤ (C * X) ^ 2 := hsq
    _ = C ^ 2 * X ^ 2 := by ring
    _ = dedekindZetaInverseVerticalMajorant K ^ 2 *
          ‖poleClearedCompletedDedekindZetaContinuation K
            (2 + t * I)‖ ^ 2 := rfl

end NumberField.Odlyzko

end
