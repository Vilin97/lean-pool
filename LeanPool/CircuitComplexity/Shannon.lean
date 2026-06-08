/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Internal.Bridge
import LeanPool.CircuitComplexity.Internal.ShannonUpper

/-! # Shannon Bounds

For `N ≥ 6`, there exists a Boolean function on `N` inputs that cannot be
computed by any fan-in-2 AND/OR circuit with fewer than `2^N / (5N)` gates.

The proof proceeds by a counting (pigeonhole) argument: the number of
distinct circuits of a given size is strictly less than the number of
Boolean functions, so some function must be hard.

## Main results

The main theorem is `shannon_lower_bound_circuit`:

    theorem shannon_lower_bound_circuit (N : Nat) [NeZero N] (hN : 6 ≤ N) :
        ∃ f : BitString N → Bool,
          ∀ G (c : Circuit Basis.andOr2 N 1 G),
            G + 1 ≤ 2 ^ N / (5 * N) →
            (fun x => (c.eval x) 0) ≠ f

Here `G` is the number of internal gates and the output gate adds one more,
so `G + 1` is the total gate count (`Circuit.size` for a single-output circuit).

When `Basis.andOr2` is known to be complete, this yields a
`sizeComplexity` bound via `shannon_size_complexity`.

* `shannon_upper_bound` — for sufficiently large `N`, every Boolean function
  on `N` inputs has `sizeComplexity` at most `18 · 2^N / N`.

Together these establish that worst-case circuit complexity is `Θ(2^N / N)`.
-/

namespace CircuitComplexity


/-- **Shannon lower bound in terms of `sizeComplexity`**: for `N ≥ 6`,
    there exists a Boolean function whose fan-in-2 AND/OR circuit complexity
    exceeds `2^N / (5N)`. -/
theorem shannon_size_complexity (N : Nat) [NeZero N] (hN : 6 ≤ N)
    [CompleteBasis Basis.andOr2] :
    ∃ f : BitString N → Bool,
      Circuit.sizeComplexity Basis.andOr2 f > 2 ^ N / (5 * N) := by
  obtain ⟨f, hf⟩ := shannon_lower_bound_circuit N hN
  refine ⟨f, ?_⟩
  by_contra hle; push Not at hle
  obtain ⟨G, c, hs, hc⟩ := Circuit.size_complexity_witness (B := Basis.andOr2) f
  have : c.size ≤ 2 ^ N / (5 * N) := hs ▸ hle
  exact hf G c (by rw [Circuit.size] at this; omega) hc

/-- **Shannon upper bound**: for `N ≥ 16`, every Boolean function on `N`
    inputs has fan-in-2 AND/OR circuit complexity at most `18 · 2^N / N`.

    Combined with `shannon_size_complexity`, this gives `Θ(2^N / N)`.

    This is the full-column-library variant (C = 18). The tighter
    `(1 + o(1)) · 2^N / N` bound due to Lupanov (1958) uses column
    grouping and is not yet formalized. -/
theorem shannon_upper_bound [CompleteBasis Basis.andOr2]
    (N : Nat) (hN : 16 ≤ N) [NeZero N]
    (f : BitString N → Bool) :
    Circuit.sizeComplexity Basis.andOr2 f ≤ 18 * 2 ^ N / N := by
  obtain ⟨G, c, heval, hsize⟩ := ShannonUpper.shannon_construction N hN f
  exact le_trans (Circuit.size_complexity_le c f heval) hsize

end CircuitComplexity
