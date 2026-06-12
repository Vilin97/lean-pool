/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.EssentialInput
import LeanPool.CircuitComplexity.Internal.LowerBound

/-! # Gate Elimination Lower Bound

For any circuit over a bounded fan-in `k` AND/OR basis (`Basis.boundedAON k`),
the number of essential input variables is at most `k` times the circuit size.

The key insight: if no gate directly reads a primary input wire, then that
input cannot influence the circuit's output. By contrapositive, every
essential variable must be "covered" by at least one gate. Since each gate
reads at most `k` inputs, the circuit needs at least `⌈n'/k⌉` gates.

## Definitions (from `Circ.EssentialInput`)

* `IsEssentialInput f i` — function `f` depends on input variable `i`
  (flipping bit `i` can change some output)
* `EssentialInputs f` — the `Finset` of all essential input variables

## Main results

The main theorem is `Circuit.gate_elimination_lower_bound`:

    theorem Circuit.gate_elimination_lower_bound {k : Nat}
        (c : Circuit (Basis.boundedAON k) N M G)
        (f : BitString N → BitString M)
        (hf : c.eval = f) :
        (EssentialInputs f).card ≤ k * c.size

And its corollary for functions that depend on all inputs:

    theorem Circuit.lower_bound_all_inputs {k : Nat}
        (c : Circuit (Basis.boundedAON k) N M G)
        (f : BitString N → BitString M)
        (hf : c.eval = f)
        (hall : ∀ i : Fin N, IsEssentialInput f i) :
        N ≤ k * c.size
-/

namespace CircuitComplexity

end CircuitComplexity
