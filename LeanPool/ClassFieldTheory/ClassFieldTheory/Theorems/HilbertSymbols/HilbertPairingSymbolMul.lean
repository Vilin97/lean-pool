/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol
/-!
# Multiplicativity of Hilbert-pairing symbols

A Hilbert pairing is a homomorphism in each power-class argument.  These
formulas expose that structure directly on representatives in `Kˣ`.
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- The symbol is multiplicative in its first representative. -/
@[simp]
theorem symbol_mul_left
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) (a b c : Kˣ) :
    B.symbol (a * b) c = B.symbol a c * B.symbol b c := by
  simp only [symbol, map_mul, MonoidHom.mul_apply]

end ClassFieldTheory.HilbertPairing
