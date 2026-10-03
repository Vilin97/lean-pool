/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.IsKummerNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
/-!
# Norm-residue criterion for a local Hilbert pairing

The vanishing of a local Hilbert symbol is equivalent to a concrete Kummer
norm condition.  The Kummer algebra is the canonical Mathlib quotient
`K[X] / (X^n - a)`, so the statement does not choose a root in an algebraic
closure.
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- A local Hilbert pairing evaluates to one exactly on Kummer norms. -/
theorem localHilbertPairing_eq_one_iff_isKummerNorm
    (K : Type u) [Field K] (n : ℕ+)
    (B : HilbertPairing K n)
    (hB : HilbertPairing.IsLocalHilbertPairing B)
    (a b : Kˣ) :
    B.symbol a b = 1 ↔ IsKummerNorm K n a b := by
  exact hB.2.2.2 a b

end ClassFieldTheory
