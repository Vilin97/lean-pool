/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import LeanPool.Superorthogonality.LeanSuperorthogonality.Defs

import LeanPool.Superorthogonality.LeanSuperorthogonality.Codex.PointwiseEstimate

/-!
Formalizing arXiv:2212.08956
-/

@[expose] public noncomputable section

namespace Superorthogonal

variable {ι : Type*} [Countable ι]
variable {k : ℕ}

open MeasureTheory Nat Set

/-- Proposition 2 from arXiv:2212.08956.
This is the key pointwise estimate used in the proof of the main theorem. -/
theorem pointwise_estimate (hk : 2 ≤ k) (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    ‖Q a - ∏ i, s (a i)‖ₑ ≤
      (((k)! - 1 : ENNReal) * (B hk a) ^ 2 * (max (A hk a) (B hk a)) ^ (k - 2)) :=
  Codex.pointwise_estimate hk a ha

end Superorthogonal

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
