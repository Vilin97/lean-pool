/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS

/-!
# The certification solution

The theorems of `Challenge.lean`, each proved by the theorem of
record of the same name.  Comparator confirms at the kernel-export
level that the statements match the challenge's, that the proofs
use no axiom outside `[propext, Classical.choice, Quot.sound]`, and
that the kernel accepts them; see `comparator-config.json` and the
CI workflow.
-/

namespace Certified

open RS

/-- **The converse**: every mixed partition function is an
edge-rank-bounded parameter, with base `max 1 (k + 2ℓ)`. -/
theorem regts_sevenster_converse : RegtsSevensterConverseStatement :=
  RS.regts_sevenster_converse

/-- **The rank bound from a bounded mixed partition function.** -/
theorem edgeRankBounded_of_mixedBounded
    {f : ClosedFragment → ℂ} {B : ℕ}
    (hf : IsMixedPartitionFunctionBounded f B) :
    EdgeRankBounded f (max 1 (2 * B)) :=
  RS.edgeRankBounded_of_mixedBounded hf

/-- **The forward direction**, with no hypothesis. -/
theorem regts_sevenster : RegtsSevensterStatement :=
  RS.regts_sevenster

/-- **The quantitative forward direction**, with no hypothesis:
both dimensions at most `⌊2eR⌋`. -/
theorem regts_sevenster_quant : RegtsSevensterStatementQuant :=
  RS.regts_sevenster_quant

/-- The total-dimension forward direction: the representing model
has `k + 2 * ℓ ≤ R`. -/
theorem regts_sevenster_total : RegtsSevensterStatementTotal :=
  RS.regts_sevenster_total

/-- **The characterisation**: a fragment parameter has bounded edge
rank exactly when it is a mixed partition function. -/
theorem regts_sevenster_characterisation
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∃ R : ℕ, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f :=
  RS.regts_sevenster_characterisation f hempty hiso

/-- **The quantitative round trip**: edge rank `R` gives dimension
`⌊2eR⌋`, and dimension `B` gives edge rank base `max 1 (2B)`. -/
theorem regts_sevenster_quant_characterisation
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∀ R, EdgeRankBounded f R →
      IsMixedPartitionFunctionBounded f
        ⌊2 * Real.exp 1 * (R : ℝ)⌋₊) ∧
    (∀ B, IsMixedPartitionFunctionBounded f B →
      EdgeRankBounded f (max 1 (2 * B))) :=
  RS.regts_sevenster_quant_characterisation f hempty hiso

end Certified
