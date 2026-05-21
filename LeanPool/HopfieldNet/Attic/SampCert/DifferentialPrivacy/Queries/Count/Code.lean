/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Abstract

/-!
# ``privNoisedCount`` Implementation

This file defines a differentially private noising of an exact length query.
-/

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPSystem T]

/--
Query to count the size of the input list.
-/
def exactCount (l : List T) : ℤ := List.length l

/--
A noised counting mechanism.
-/
def privNoisedCount (ε₁ ε₂ : ℕ+) (l : List T) : PMF ℤ := do
  dps.noise exactCount 1 ε₁ ε₂ l

end SLang
