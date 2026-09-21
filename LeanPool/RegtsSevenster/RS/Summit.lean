/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.TheoremConverse
import LeanPool.RegtsSevenster.RS.TheoremTotal
import LeanPool.RegtsSevenster.RS.TheoremPadding
import LeanPool.RegtsSevenster.RS.Classical.Deligne.DeligneAssembly

/-!
# The theorems, unconditionally

The theorems of record, carrying no hypothesis: Deligne's theorem,
in fibre-functor form, is `RS.deligne_theorem`
(`RS/Classical/Deligne/DeligneAssembly.lean`),
so the forms in `RS/TheoremForward.lean`, `RS/TheoremQuant.lean`,
`RS/TheoremTotal.lean`, `RS/TheoremDimension.lean`,
`RS/TheoremPadding.lean` and `RS/TheoremConverse.lean` that take it as
an argument are applied to
it here.  Those forms remain available alongside: they exhibit the
dependency structure, which is what a reader checking the argument
against the literature wants.

The envelope's semisimplicity and abelianness come from the
factorial trace obstruction. `Assembly/BlueprintFactorial` checks
that the forward summits use this theorem and exclude the appendix
nilpotent-trace and trace-zeta mechanisms.

The axiom checks are pinned in
`RS/Assembly/BlueprintDeligne.lean`.
-/

namespace RS

/-- **The Regts–Sevenster theorem**: every graph parameter with
exponentially bounded edge-connection rank is a mixed partition
function. -/
theorem regts_sevenster : RegtsSevensterStatement :=
  regts_sevenster_deligne_only deligne_theorem

/-- **The Regts–Sevenster theorem, quantitative form**. -/
theorem regts_sevenster_quant : RegtsSevensterStatementQuant :=
  regts_sevenster_quant_deligne_only deligne_theorem

/-- The Regts–Sevenster theorem with at most `R` colours in total:
the representing functional satisfies `k + 2 * ℓ ≤ R`. -/
theorem regts_sevenster_total : RegtsSevensterStatementTotal :=
  regts_sevenster_total_deligne_only deligne_theorem

/-- Every parameter with exponentially bounded connection rank has
a model attaining its minimum total colour dimension. -/
theorem regts_sevenster_minimum {R : ℕ} (f : EdgeRankParameter R) :
    IsMixedPartitionFunctionTotalBounded f.val
      (minimumColourDimension f.val) :=
  regts_sevenster_minimum_deligne_only deligne_theorem f

/-- The even connection-rank growth rate is the minimum total
number of colours of a representing mixed model. -/
theorem regts_sevenster_rank_growth {R : ℕ} (f : EdgeRankParameter R) :
    Filter.Tendsto
      (fun n => (connectionRank f.val (2 * n) : ℝ) ^
        ((2 * n : ℕ) : ℝ)⁻¹)
      Filter.atTop (nhds (minimumColourDimension f.val : ℝ)) :=
  regts_sevenster_rank_growth_deligne_only deligne_theorem f

/-- Prescribed parity dimensions are characterized by the total
rank bound and the free-circle value. -/
theorem regts_sevenster_prescribed
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    (k ℓ : ℕ) :
    (∃ h : MixedFunctional k ℓ, h.Represents f) ↔
      PrescribedColourBounds f k ℓ :=
  regts_sevenster_prescribed_deligne_only deligne_theorem f hempty hiso k ℓ

/-- **The characterisation**: for a normalised isomorphism-invariant
parameter, bounded edge-connection rank and being a mixed partition
function are equivalent. -/
theorem regts_sevenster_characterisation (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∃ R : ℕ, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f :=
  regts_sevenster_iff deligne_theorem f hempty hiso

/-- **The quantitative round trip**. -/
theorem regts_sevenster_quant_characterisation
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∀ R, EdgeRankBounded f R →
      IsMixedPartitionFunctionBounded f
        ⌊2 * Real.exp 1 * (R : ℝ)⌋₊) ∧
    (∀ B, IsMixedPartitionFunctionBounded f B →
      EdgeRankBounded f (max 1 (2 * B))) :=
  regts_sevenster_quant_roundtrip deligne_theorem f hempty hiso

end RS
