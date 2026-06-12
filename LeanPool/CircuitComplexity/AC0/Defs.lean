/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.AON.Defs

/-! # AC0 — Core Definitions

This module defines the AC0 circuit complexity class.

## Main definitions

* `InAC0` — predicate: the family is in AC0 (constant depth, polynomial size,
  unbounded fan-in AND/OR)
-/

namespace CircuitComplexity


/-- A Boolean function family is in **AC0** if there exist constants `d`
(depth bound) and `c` (size exponent) such that for every input length
`N ≥ 1`, some unbounded-fan-in AND/OR circuit of depth at most `d` and
size at most `N ^ c` computes `f N`.

This captures the standard definition of AC0:
- **Constant depth**: the circuit depth does not grow with `N`.
- **Polynomial size**: the number of gates is bounded by a polynomial in `N`.
- **Unbounded fan-in**: AND and OR gates may have arbitrarily many inputs.
- **Free negation**: each gate input carries a negation flag (standard in
  circuit complexity). -/
def InAC0 (f : BoolFunFamily) : Prop :=
  ∃ (d c : Nat), ∀ (N : Nat) [NeZero N],
    ∃ (G : Nat) (circuit : Circuit Basis.unboundedAON N 1 G),
      circuit.depth ≤ d ∧ circuit.size ≤ N ^ c ∧
      (fun x => (circuit.eval x) 0) = f N

end CircuitComplexity
