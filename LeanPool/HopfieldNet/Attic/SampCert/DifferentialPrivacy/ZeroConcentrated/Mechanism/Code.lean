/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Samplers.GaussianGen.Properties

/-!
# ``privNoisedQuery`` Implementation

Abstract mechanism for adding the proper amount of noise to a query, depending on the sensitivity.
-/

noncomputable section

namespace SLang

/--
Mechanism obtained by postcomposing query with by gaussian noise (of variance ``(Δ ε₁ / ε₂)^2``).
-/
def privNoisedQuery (query : List T → ℤ) (Δ : ℕ+) (ε₁ ε₂ : ℕ+) (l : List T) : PMF ℤ := do
  DiscreteGaussianGenPMF (Δ * ε₂) ε₁ (query l)

end SLang
