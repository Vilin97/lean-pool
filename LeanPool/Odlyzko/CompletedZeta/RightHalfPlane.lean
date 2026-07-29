/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.Expansion
public import LeanPool.Odlyzko.DedekindZeta.PrimePowerExpansion
public import LeanPool.Odlyzko.DedekindZeta.RightHalfPlane

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem dedekindZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s ≠ 0 := by
  rw [← dedekindZeta_primeIdeal_eulerProduct_tprod K hs]
  exact tprod_primeIdealFactor_ne_zero K hs

theorem completedDedekindZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    CompletedZeta.completed K s ≠ 0 := by
  rw [CompletedZeta.completed]
  exact mul_ne_zero
    (mul_ne_zero
      (dedekindDiscriminantFactor_ne_zero K s)
      (by
        rw [CompletedZeta.archimedeanFactor]
        exact mul_ne_zero
          (pow_ne_zero _ (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)))
          (pow_ne_zero _
            (complexPlaceGammaFactor_ne_zero_of_re_pos (by linarith)))))
    (dedekindZeta_ne_zero_of_one_lt_re K hs)

variable [IsTotallyComplex K]

theorem logDeriv_completedDedekindZeta_rightHalfPlane {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv (CompletedZeta.completed K) s =
      Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s - Complex.log (2 * (Real.pi : ℂ))) +
        logDeriv (dedekindZeta K) s := by
  exact logDeriv_completedDedekindZeta_of_isTotallyComplex K
    (by linarith)
    (dedekindZeta_ne_zero_of_one_lt_re K hs)
    (differentiableAt_dedekindZeta K hs)

theorem logDeriv_completedDedekindZeta_rightHalfPlane_eq_primePower
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (CompletedZeta.completed K) s =
      Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s - Complex.log (2 * (Real.pi : ℂ))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          primePowerLogTerm K pe.1 pe.2 s := by
  rw [logDeriv_completedDedekindZeta_rightHalfPlane K hs]
  have hprime :=
    neg_logDeriv_dedekindZeta_eq_tsum_primePower K hs
  grind

end NumberField.Odlyzko
