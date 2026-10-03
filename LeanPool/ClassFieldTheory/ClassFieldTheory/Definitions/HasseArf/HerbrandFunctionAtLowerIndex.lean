/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Finset.Interval
public import Mathlib.SetTheory.Cardinal.Finite
/-!
# The Herbrand function at integral lower indices
-/

@[expose] public section

open scoped BigOperators

noncomputable
section

namespace ClassFieldTheory

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/-- The Herbrand value at a nonnegative integral lower index:
`φ(n) = (1 / |G₀|) · ∑_{i=1}^{n} |Gᵢ|`.

Its ramification-theoretic interpretation requires the lower groups to be
finite.  The definition alone does not impose that hypothesis. -/
def herbrandFunctionAtLowerIndex (A : ValuationSubring L) (n : ℕ) : ℚ :=
  (∑ i ∈ Finset.Icc 1 n,
      (Nat.card (lowerRamificationGroup K A i) : ℚ)) /
    (Nat.card (lowerRamificationGroup K A 0) : ℚ)

end ClassFieldTheory
