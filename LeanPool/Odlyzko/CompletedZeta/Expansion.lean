/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.LogDeriv
public import LeanPool.Odlyzko.CompletedZeta.TotallyComplex

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem differentiableAt_dedekindArchimedeanFactor_of_isTotallyComplex {s : ℂ}
    (hs : 0 < s.re) :
    DifferentiableAt ℂ (CompletedZeta.archimedeanFactor K) s := by
  rw [show CompletedZeta.archimedeanFactor K =
      fun z : ℂ ↦ CompletedZeta.complexPlaceGammaFactor z ^ nrComplexPlaces K by
    funext z
    simp [dedekindArchimedeanFactor_of_isTotallyComplex, CompletedZeta.complexPlaceGammaFactor]]
  exact (differentiableAt_complexPlaceGammaFactor_of_re_pos hs).pow _

theorem logDeriv_completedDedekindZeta_of_isTotallyComplex {s : ℂ} (hs : 0 < s.re)
    (hζne : dedekindZeta K s ≠ 0) (hζdiff : DifferentiableAt ℂ (dedekindZeta K) s) :
    logDeriv (CompletedZeta.completed K) s =
      Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s - Complex.log (2 * (Real.pi : ℂ))) +
        logDeriv (dedekindZeta K) s := by
  rw [show CompletedZeta.completed K = fun z : ℂ ↦
      (CompletedZeta.discriminantFactor K z * CompletedZeta.archimedeanFactor K z) *
        dedekindZeta K z by
    funext z
    simp only [CompletedZeta.completed]]
  have hD : CompletedZeta.discriminantFactor K s ≠ 0 :=
    dedekindDiscriminantFactor_ne_zero K s
  have hA : CompletedZeta.archimedeanFactor K s ≠ 0 := by
    rw [dedekindArchimedeanFactor_of_isTotallyComplex]
    exact pow_ne_zero _ (complexPlaceGammaFactor_ne_zero_of_re_pos hs)
  have hdD : DifferentiableAt ℂ (CompletedZeta.discriminantFactor K) s :=
    differentiable_dedekindDiscriminantFactor K s
  have hdA : DifferentiableAt ℂ (CompletedZeta.archimedeanFactor K) s :=
    differentiableAt_dedekindArchimedeanFactor_of_isTotallyComplex K hs
  rw [logDeriv_mul
      (f := fun z ↦ CompletedZeta.discriminantFactor K z * CompletedZeta.archimedeanFactor K z)
      (g := dedekindZeta K) s (mul_ne_zero hD hA) hζne (hdD.mul hdA) hζdiff,
    logDeriv_mul
      (f := CompletedZeta.discriminantFactor K) (g := CompletedZeta.archimedeanFactor K)
      s hD hA hdD hdA,
    logDeriv_dedekindDiscriminantFactor,
    logDeriv_dedekindArchimedeanFactor_of_isTotallyComplex K hs]

end NumberField.Odlyzko
