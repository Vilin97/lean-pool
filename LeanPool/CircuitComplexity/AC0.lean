/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.AC0.Defs
import LeanPool.CircuitComplexity.XOR

/-! # AC0 — The AC0 Complexity Class

This module re-exports the AC0 definitions and main results.

## Definitions (from `Circ.AC0.Defs`)

* `InAC0` — predicate: the family is in AC0 (constant depth, polynomial size,
  unbounded fan-in AND/OR)
-/

namespace CircuitComplexity


/-- The parity (XOR) function family: the `N`-input XOR for each input length. -/
def parityFamily : BoolFunFamily := fun N => Schnorr.xorBool N

end CircuitComplexity
