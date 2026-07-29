/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.LocalLogDeriv
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealFactor

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem logDeriv_primeIdealFactor (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv (primeIdealFactor K P) s =
      -(Complex.log (primeIdealNorm K P) *
        inverseNormPower (primeIdealNorm K P) s /
          (1 - inverseNormPower (primeIdealNorm K P) s)) := by
  exact logDeriv_localFactor (one_lt_primeIdealNorm K P) hs

theorem hasSum_neg_logDeriv_primeIdealFactor
    (P : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    HasSum
      (fun e : ℕ ↦ Complex.log (primeIdealNorm K P) *
        inverseNormPower (primeIdealNorm K P) s ^ (e + 1))
      (-logDeriv (primeIdealFactor K P) s) :=
  hasSum_logDeriv_localFactor (one_lt_primeIdealNorm K P) hs

end NumberField.Odlyzko
