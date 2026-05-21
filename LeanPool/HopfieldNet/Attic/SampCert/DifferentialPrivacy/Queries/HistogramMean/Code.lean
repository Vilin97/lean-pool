/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Abstract
import Init.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Queries.Histogram.Code
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Queries.BoundedMean.Code

/-!
# ``privMeanHistogram`` Implementation

Implementation for
-/


/-!
## Compute the mean using a histogram to compute the noisy max
-/

noncomputable section

variable (dps : SLang.DPSystem ℕ)
variable (numBins : ℕ+)
variable (B : Bins ℕ numBins)

/-
unbin is a function which returns the greatest number inside a bin

For our formalization of DP, this number must be positive (it eventually
becomes the sensitivity of DP noise, but we could also change this).
-/
variable (unbin : Fin numBins -> ℕ+)


namespace SLang

/-
Compute the noisy mean of a list, by computing the noisy maximum τ-thresholded value with (ε₁/ε₂)-DP,
and the bounded mean with (ε₃/ε₄)-DP.
-/
def privMeanHistogram (ε₁ ε₂ : ℕ+) (τ : ℤ) (ε₃ ε₄ : ℕ+) : Mechanism ℕ (Option ℚ) :=
  privPostProcess
    (privComposeAdaptive
      (@privMaxBinAboveThreshold numBins _ B dps ε₁ ε₂ τ)
      (fun opt_max =>
        match opt_max with
        | none => privConst none
        | some mx =>
            privPostProcess
              (privNoisedBoundedMean (unbin mx) ε₃ ε₄)
              (fun x => some x)))
  (fun z => z.2)

end SLang
