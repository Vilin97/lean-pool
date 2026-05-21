/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Queries.Count.Code
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Sensitivity
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Abstract

/-!
# ``privNoisedCount`` Properties

This file proves abstract differential privacy for ``privNoisedCount``.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPSystem T]

/--
The counting query is 1-sensitive
-/
theorem exactCount_1_sensitive :
  @sensitivity T exactCount 1 := by
  simp [exactCount, sensitivity]
  intros l₁ l₂ H
  cases H
  · rename_i a b n h1 h2
    subst h1 h2
    simp
  · rename_i a b n h1 h2
    subst h1 h2
    simp
  · rename_i a n b m h1 h2
    subst h1 h2
    simp

/--
The noised counting query satisfies DP property
-/
@[simp]
theorem privNoisedCount_DP (ε₁ ε₂ : ℕ+) :
  dps.prop (privNoisedCount ε₁ ε₂) ((ε₁ : NNReal) / ε₂) := by
  apply dps.noise_prop
  apply exactCount_1_sensitive

end SLang
