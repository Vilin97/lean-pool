/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
/-!
# Families of finite-place Hilbert pairings
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- A choice of power-class pairing on the completion of `F` at every finite
place.  No reciprocity law is hidden in this data type. -/
abbrev GlobalHilbertPairingFamily
    (F : Type u) [Field F] [NumberField F] (n : ℕ+) :=
  ∀ v : HeightOneSpectrum (𝓞 F), HilbertPairing (v.adicCompletion F) n

end ClassFieldTheory
