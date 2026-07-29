/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquation
public import LeanPool.Odlyzko.CompletedZeta.GammaVerticalNorm
public import LeanPool.Odlyzko.CompletedZeta.TotallyComplex
public import LeanPool.Odlyzko.DedekindZeta.VerticalLowerBound

/-!
# Vertical Lower Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

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
