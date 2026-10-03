/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup
/-!
# Lower ramification jumps
-/

@[expose] public section

namespace ClassFieldTheory

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/-- A nonnegative integer `n` is a lower ramification jump when the lower
ramification filtration strictly changes after index `n`. -/
def IsLowerRamificationJump (A : ValuationSubring L) (n : ℕ) : Prop :=
  lowerRamificationGroup K A n ≠ lowerRamificationGroup K A (n + 1)

end ClassFieldTheory
