/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
/-!
# Possible nontrivial finite-place Hilbert factors

This set depends on the two nonzero global arguments and the exponent.  A
finite place is excluded exactly when all three have valuation one there.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- The places where `a`, `b`, or the exponent is not a valuation-ring unit.
This is the precise finite-place bound for global Hilbert factors. -/
def finitePlaceHilbertBadSet
    (F : Type u) [Field F] [NumberField F]
    (n : ℕ+) (a b : Fˣ) : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | v.valuation F (a : F) ≠ 1 ∨
    v.valuation F (b : F) ≠ 1 ∨
    v.valuation F ((n : ℕ) : F) ≠ 1}

end ClassFieldTheory
