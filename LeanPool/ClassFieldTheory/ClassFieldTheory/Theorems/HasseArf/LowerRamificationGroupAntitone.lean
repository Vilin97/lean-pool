/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup
/-!
# The lower ramification filtration decreases

The definition uses powers of the maximal ideal of a valuation subring.
The inclusion below holds without local-field or finiteness hypotheses.
-/

@[expose] public section

namespace ClassFieldTheory

universe u v

/-- A larger lower index gives a smaller ramification subgroup. -/
theorem lowerRamificationGroup_antitone
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    Antitone (lowerRamificationGroup K A) := by
  intro m n hmn σ hσ x
  exact (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal A)
    (Nat.add_le_add_right hmn 1)) (hσ x)

end ClassFieldTheory
