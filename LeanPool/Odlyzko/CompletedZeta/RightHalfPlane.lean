/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.Defs
public import LeanPool.Odlyzko.CompletedZeta.TotallyComplex
public import LeanPool.Odlyzko.DedekindZeta.Convergence
public import LeanPool.Odlyzko.DedekindZeta.PrimePowerExpansion
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.Deriv

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open Complex LSeries

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem abscissaOfAbsConv_idealNormCount_le_one :
    LSeries.abscissaOfAbsConv (fun n ↦ (idealNormCount K n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact lSeriesSummable_idealNormCount K (by simpa using hy)

theorem hasDerivAt_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (NumberField.dedekindZeta K)
      (-LSeries (LSeries.logMul fun n ↦ (idealNormCount K n : ℂ)) s) s := by
  change HasDerivAt (LSeries fun n ↦ (idealNormCount K n : ℂ)) _ s
  exact LSeries_hasDerivAt ((abscissaOfAbsConv_idealNormCount_le_one K).trans_lt <| by
    exact_mod_cast hs)

theorem differentiableAt_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (NumberField.dedekindZeta K) s :=
  (hasDerivAt_dedekindZeta K hs).differentiableAt

end NumberField.Odlyzko

end

section

open Complex NumberField

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem logDeriv_dedekindDiscriminantFactor (s : ℂ) :
    logDeriv (CompletedZeta.discriminantFactor K) s =
      Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) / 2 := by
  change logDeriv (fun z : ℂ ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (z / 2)) s = _
  rw [logDeriv_apply]
  have hderiv :
      deriv (fun z : ℂ ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (z / 2)) s =
        Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) *
          deriv (fun z : ℂ ↦ z / 2) s *
            ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) :=
    Complex.deriv_const_cpow (f := fun z : ℂ ↦ z / 2) (x := s) (by simp) _
  rw [hderiv]
  have hdiv : deriv (fun z : ℂ ↦ z / 2) s = 1 / 2 :=
    ((hasDerivAt_id s).div_const 2).deriv
  rw [hdiv]
  have hne : (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)) ≠ 0 :=
    dedekindDiscriminantFactor_ne_zero K s
  grind

end NumberField.Odlyzko

end

section

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

end

section

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

end
