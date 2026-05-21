/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealExpSmall

namespace Computable
namespace CReal

open scoped BigOperators

/-!
# Exponential (range-reduced skeleton)

This module currently defines the *range-reduced auxiliary* exponential `expAux`
parameterized by explicit range data, together with the basic congruence lemma
when the range selector agrees on the halving exponent `k`.

The remaining well-definedness lemma across distinct `k` values (`chooser independence`)
requires the functional equation `exp(x) = (exp(x/2))^2` for the bounded exponential,
and is intentionally left to `CRealExpKIndep.lean`.
-/

/-- Range-reduction data for `exp`: a bounded representative of `x / 2^k`. -/
structure ExpRangeData (x : CReal) where
  k : ℕ
  small : ExpSmallInput
  /-- Semantic link: the bounded representative is `x / 2^k` (expressed via multiplication). -/
  -- `CReal` is only a ring at this stage (no `Inv CReal`), so take the inverse in `ℚ`
  -- and cast it into `CReal`.
  small_spec : (⟦small.pre⟧ : CReal) = x * (((((2 : ℚ) ^ k)⁻¹) : ℚ) : CReal)

/-- Range-reduced auxiliary exponential: `exp(x) = exp(x/2^k)^(2^k)`. -/
def expAux (x : CReal) (d : ExpRangeData x) [Pre.SmallExpModulus] : CReal :=
  (expSmall d.small) ^ (2 ^ d.k)

/--
If two range data packages agree on `k` and their bounded representatives agree,
then `expAux` agrees. This is the "same-`k`" half of chooser-independence.
-/
theorem expAux_congr_of_k_eq [Pre.SmallExpModulus]
    (x : CReal) (d₁ d₂ : ExpRangeData x) (hk : d₁.k = d₂.k)
    (hsmall : CReal.Pre.Equiv d₁.small.pre d₂.small.pre) :
    expAux x d₁ = expAux x d₂ := by
  -- `subst` doesn't work on projection equalities like `d₁.k = d₂.k`;
  -- just rewrite using `hk` and the congruence for the bounded exponential.
  simp [expAux, hk, expSmall_congr hsmall]

end CReal
end Computable
