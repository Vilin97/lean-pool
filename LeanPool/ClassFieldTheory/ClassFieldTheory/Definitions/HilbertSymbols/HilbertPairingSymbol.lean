/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
/-!
# Evaluation of a Hilbert pairing on representatives
-/

@[expose] public section

namespace ClassFieldTheory.HilbertPairing

universe u

/-- Evaluate a power-class pairing on representatives in `Kˣ`. -/
def symbol
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) (a b : Kˣ) :
    rootsOfUnity (n : ℕ) K :=
  B (powerClass K n a) (powerClass K n b)

end ClassFieldTheory.HilbertPairing
