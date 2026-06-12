/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Data.Fintype.BigOperators
import LeanPool.CircuitComplexity.Basic

/-! # Essential Inputs

This module defines the notion of essential (non-redundant) input variables
for a Boolean function.

## Main definitions

* `IsEssentialInput` — a function depends on a particular input variable
* `EssentialInputs` — the set of essential input variables
-/

namespace CircuitComplexity


/-- A function `f` depends on input variable `i` if flipping that bit
    can change some output. -/
def IsEssentialInput {N M : Nat} (f : BitString N → BitString M) (i : Fin N) : Prop :=
  ∃ x : BitString N, f x ≠ f (Function.update x i (!x i))

instance {N M : Nat} {f : BitString N → BitString M} {i : Fin N} :
    Decidable (IsEssentialInput f i) :=
  inferInstanceAs (Decidable (∃ x, f x ≠ f (Function.update x i (!x i))))

/-- The set of input variables that `f` depends on. -/
def EssentialInputs {N M : Nat} (f : BitString N → BitString M) : Finset (Fin N) :=
  Finset.univ.filter (IsEssentialInput f)

end CircuitComplexity
