/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquationLogDeriv
public import LeanPool.Odlyzko.CompletedZeta.RightHalfPlane
public import LeanPool.Odlyzko.ExplicitFormula.ArchimedeanKernel
public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaPoleContour

/-!
# Right Vertical Expansion

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem logDeriv_poleClearedContinuation_sub_poles
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
        completedZetaPoleLogDeriv s =
      (Real.log |(discr K : ℝ)| : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s -
            Complex.log (2 * (Real.pi : ℂ))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          primePowerLogTerm K pe.1 pe.2 s := by
  have hD : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  rw [logDeriv_poleClearedCompletedDedekindZetaContinuation_eq_primePower
    K hs]
  unfold completedZetaPoleLogDeriv
  rw [Complex.ofReal_log hD]
  ring

theorem logDeriv_poleClearedContinuation_sub_poles_eq_logDeriv_dedekindZeta
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
        completedZetaPoleLogDeriv s =
      (Real.log |(discr K : ℝ)| : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s -
            Complex.log (2 * (Real.pi : ℂ))) +
        logDeriv (dedekindZeta K) s := by
  rw [logDeriv_poleClearedContinuation_sub_poles K hs]
  have hprime :=
    neg_logDeriv_dedekindZeta_eq_tsum_primePower K hs
  grind

end NumberField.Odlyzko
