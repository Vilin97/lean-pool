/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClassGroup
/-!
# Canonical power classes
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- The canonical class of a nonzero field element modulo `n`-th powers. -/
def powerClass (K : Type u) [Field K] (n : ℕ+) : Kˣ →* PowerClassGroup K n := by
  unfold PowerClassGroup
  exact QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range

end ClassFieldTheory
