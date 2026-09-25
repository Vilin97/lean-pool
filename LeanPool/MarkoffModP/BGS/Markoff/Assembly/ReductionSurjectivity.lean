/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ExplicitPuncturedTransitivity
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.WeightedCoarseSupportSurjectivity
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.TransitivitySurjectivity

/-!
# Explicit strong approximation

The explicit punctured-transitivity theorem, together with natural Markoff connectivity,
gives surjectivity of reduction from natural-number Markoff solutions.
-/

@[expose] public section

namespace BGS.Markoff

/-- **Explicit strong approximation in its source-faithful form.**  For every prime above the
closed cutoff, every Markoff solution modulo `p` is the reduction of a natural-number solution. -/
theorem markoffReduction_surjective_of_concreteExplicitBound
    (p : ℕ) (hpPrime : p.Prime)
    (hp : (2 ^ 9 * (48 ^ 3 + 1) ^ 18 *
      (2 ^ 9 * (9 ^ 9) ^ (2 ^ 9)) ^ 8 + 1) ≤ p) :
    Function.Surjective (markoffReduction p) :=
  (puncturedMarkoffTransitiveAt_iff_markoffReduction_surjective p hpPrime).mp
    (puncturedMarkoffTransitiveAt_of_concreteExplicitBound p hpPrime hp)

/-- Strong approximation obtained from the elementary preliminary route. -/
theorem markoffReduction_surjective_of_concretePreliminaryBound
    (p : ℕ) (hpPrime : p.Prime)
    (hp : (2 ^ 1833 * (48 ^ 3 + 1) ^ 10 + 1) ≤ p) :
    Function.Surjective (markoffReduction p) :=
  (puncturedMarkoffTransitiveAt_iff_markoffReduction_surjective p hpPrime).mp
    (puncturedMarkoffTransitiveAt_of_concretePreliminaryBound p hpPrime hp)

/-- The weighted certificate-free Euler-seven coarse-support theorem in the
functor presentation used by the Comparator challenge. -/
theorem reduction_surjective_of_explicitBound :
    let p₀ := 35721 ^ 5 * 2 ^ 1547 * 32769 ^ 2 + 1
    ∀ (p : ℕ), p.Prime → p₀ ≤ p →
      Function.Surjective
        (BGS.Markoff.map (CommSemiRingCat.ofHom (Nat.castRingHom (ZMod p)))) := by
  dsimp only
  intro p hpPrime hp y
  obtain ⟨x, hx⟩ :=
    markoffReduction_surjective_of_weightedCoarseSupportBound p hpPrime hp
    (markoffEquivSemiringMarkoffSurface (ZMod p) y)
  refine ⟨(markoffEquivSemiringMarkoffSurface ℕ).symm x, ?_⟩
  apply (markoffEquivSemiringMarkoffSurface (ZMod p)).injective
  simpa [markoffReduction] using hx

end BGS.Markoff
