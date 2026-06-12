/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.XOR
import LeanPool.CircuitComplexity.Internal.Bridge

/-! # Schnorr's Lower Bound for XOR Circuits

Any fan-in-2 AND/OR circuit computing the N-input XOR function (or its
complement) requires at least `2(N − 1)` internal gates.

The proof proceeds by induction on `N`. At each step:
1. **Restrict** one input variable, reducing to XOR on `N − 1` inputs.
2. **Eliminate** two gates that become redundant after restriction.
3. Apply the inductive hypothesis to the smaller circuit.

## Definitions (from `Circ.XOR`)

* `Schnorr.xorBool N x` — the N-input XOR (parity) function

## Main results

The main theorem is `schnorr_lower_bound_circuit`:

    theorem schnorr_lower_bound_circuit (N G : Nat) [NeZero N]
        (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
        (heval : ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x))
        (hN : 1 ≤ N) : G + 2 ≥ 2 * N

Here `G` is the number of internal gates. The hypothesis allows the circuit
to compute either XOR or its complement (`comp = true` for complement).
The bound `G + 2 ≥ 2 * N` means `G ≥ 2(N − 1)` internal gates, or
equivalently `G + 1 ≥ 2N − 1` total gates (since `Circuit.size = G + 1`
for single-output circuits).

When `Basis.andOr2` is known to be complete, this yields a
`sizeComplexity` bound via `schnorr_size_complexity`.
-/

namespace CircuitComplexity


/-- **Schnorr lower bound in terms of `sizeComplexity`**: the fan-in-2
    AND/OR circuit complexity of N-input XOR is at least `2N − 1`. -/
theorem schnorr_size_complexity (N : Nat) [NeZero N] (hN : 1 ≤ N)
    [CompleteBasis Basis.andOr2] :
    Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N) ≥ 2 * N - 1 := by
  by_contra hlt; push Not at hlt
  obtain ⟨G, c, hs, hc⟩ := Circuit.size_complexity_witness (B := Basis.andOr2)
    (Schnorr.xorBool N)
  have heval : ∀ x, (c.eval x) 0 = false.xor (Schnorr.xorBool N x) := by
    intro x; simp [congr_fun hc x]
  have hbound := schnorr_lower_bound_circuit N G c false heval hN
  rw [Circuit.size] at hs; omega

end CircuitComplexity
