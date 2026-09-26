/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.FinsetDomain.Internal

/-!
# Finite-deviation functions are polynomial-time

A function that agrees with the constant empty-output function on all but
finitely many inputs is polynomial-time computable. Concretely, for any target
function `g` and finite set `S`, the function `fun s => if s ∈ S then g s else []`
belongs to `FP`: the finite lookup table can be hard-wired into the states of a
Turing machine that decides membership in `S` while scanning the input and then
emits the corresponding fixed output, all in linear time.

This is the base case for building up polynomial-time functions — every function
with finite support (relative to the empty output) is trivially in `FP`,
regardless of how the values `g s` are chosen.

## Main result

- `ite_mem_finset_mem_FP` — `fun s => if s ∈ S then g s else []` belongs to `FP`
-/

@[expose] public section

namespace Complexity

/-- A function that agrees with the constant empty-output function except on a
finite set `S` — that is, `fun s => if s ∈ S then g s else []` — is computable in
polynomial (indeed linear) time. The finite table of exceptional values is
hard-wired into the lookup machine's states. -/
theorem ite_mem_finset_mem_FP (g : List Bool → List Bool) (S : Finset (List Bool)) :
    (fun s => if s ∈ S then g s else []) ∈ FP :=
  ite_mem_finset_mem_FP_internal g S

end Complexity
