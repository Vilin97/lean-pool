/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-! Scalar closure of the normalized all-order recurrence in l.V.
This module is algebraic: application to the actual iterates additionally
requires derivation of the recurrence from their differentiated equations. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- The two geometric convolution kernels in the source have mass at most two. -/
theorem iterate_geometric_kernel_le_two {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (n : ℕ) : (∑ k ∈ Finset.range n, r ^ k) ≤ 2 := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, (1 / (2 : ℝ)) ^ k :=
      Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ hr hrhalf k)
    _ ≤ 2 := sum_geometric_two_le n

end AVenhance.Infra.Section4
