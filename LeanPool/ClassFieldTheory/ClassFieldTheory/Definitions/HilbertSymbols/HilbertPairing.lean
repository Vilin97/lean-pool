/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClassGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
/-!
# Pairings on power classes
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- Multiplicative pairings on `n`-th power classes with values in the
`n`-th roots of unity. -/
abbrev HilbertPairing (K : Type u) [Field K] (n : ℕ+) :=
  PowerClassGroup K n →*
    (PowerClassGroup K n →* rootsOfUnity (n : ℕ) K)

end ClassFieldTheory
