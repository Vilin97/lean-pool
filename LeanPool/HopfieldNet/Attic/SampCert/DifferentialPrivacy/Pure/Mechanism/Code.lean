/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Samplers.LaplaceGen.Properties

/-!
# Implementation of ``privNoisedQueryPure``
-/

noncomputable section

namespace SLang

/--
Add noise to a a query from the discrete Laplace distribution in order to obtain a (ε₁/ε₂)-DP mechanism from a Δ-sensitive query.
-/
def privNoisedQueryPure (query : List T → ℤ) (Δ : ℕ+) (ε₁ ε₂ : ℕ+) (l : List T) : PMF ℤ := do
  DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (query l)

end SLang
