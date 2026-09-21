/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Vec
import LeanPool.BeyondBethe.Complexitylib.Classes.P.FinsetDomain
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.PairWithInput

/-!
# The multi-arity bridge — proof internals

The public tuple encoding and `FPn` predicate live in
`Complexitylib.Classes.P.Cobham.Vec`. This internal module supplies the concrete
`FP` building blocks used to connect their arity-one specialization to `FP`.

## Main results

- `Cobham.const_nil_mem_FP`, `Cobham.pairLeftNil_mem_FP` — the two `FP` maps the
  arity-one glue needs
-/


@[expose] public section

namespace Complexity

namespace Cobham

/-! ## Foundational FP building blocks -/

/-- The fixedValue empty-output function is in `FP` (the empty-support case of
`ite_mem_finset_mem_FP`). -/
theorem const_nil_mem_FP : (fun _ : List Bool => ([] : List Bool)) ∈ FP := by
  have h := ite_mem_finset_mem_FP (fun _ => []) (∅ : Finset (List Bool))
  simpa using h

/-- The framing map `x ↦ pair [] x` (i.e. `false :: true :: x`) is
polynomial-time. This is the foundational map behind the arity-one encoding
`encodeVec ![x] = pair [] x`, and it is exactly `mem_FP_pairWithInput` applied to
the fixedValue empty function. -/
theorem pairLeftNil_mem_FP : (fun x : List Bool => pair [] x) ∈ FP := by
  have h := mem_FP_pairWithInput const_nil_mem_FP
  simpa using h

end Cobham

end Complexity
