/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.GammaFactor
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace Module

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem dedekindArchimedeanFactor_of_isTotallyComplex (s : ℂ) :
    CompletedZeta.archimedeanFactor K s =
      (Complex.Gammaℂ s / 2) ^ nrComplexPlaces K := by
  simp [CompletedZeta.archimedeanFactor, IsTotallyComplex.nrRealPlaces_eq_zero K]

theorem completedDedekindZeta_of_isTotallyComplex (s : ℂ) :
    CompletedZeta.completed K s =
      CompletedZeta.discriminantFactor K s *
        (Complex.Gammaℂ s / 2) ^ nrComplexPlaces K * dedekindZeta K s := by
  rw [CompletedZeta.completed, dedekindArchimedeanFactor_of_isTotallyComplex]

theorem two_mul_nrComplexPlaces_eq_finrank :
    2 * nrComplexPlaces K = finrank ℚ K := by
  simpa [IsTotallyComplex.nrRealPlaces_eq_zero K] using
    (card_add_two_mul_card_eq_rank K)

theorem logDeriv_dedekindArchimedeanFactor_of_isTotallyComplex {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv (CompletedZeta.archimedeanFactor K) s =
      nrComplexPlaces K *
        (Complex.digamma s - Complex.log (2 * (Real.pi : ℂ))) := by
  rw [show CompletedZeta.archimedeanFactor K =
      fun z : ℂ ↦ CompletedZeta.complexPlaceGammaFactor z ^ nrComplexPlaces K by
    funext z
    simp [dedekindArchimedeanFactor_of_isTotallyComplex, CompletedZeta.complexPlaceGammaFactor]]
  rw [logDeriv_fun_pow (differentiableAt_complexPlaceGammaFactor_of_re_pos hs),
    logDeriv_complexPlaceGammaFactor_of_re_pos hs]

end NumberField.Odlyzko
