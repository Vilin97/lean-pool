/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Pauli propagation: truncation error

Pauli propagation evolves an observable in the Heisenberg picture as a sum over Pauli
paths and, to stay efficient, truncates low-coefficient / high-weight terms. Rudolph
et al. (2025) bound the total simulation error by the sum of the per-layer discarded
`ℓ¹`-norms (a triangle-inequality bound). This module records that bound abstractly
(the discarded norms are the hypotheses) and derives that exact propagation (no
truncation) incurs no error, and that the error bound is nonnegative.

Source: Rudolph, Jones, Teng, Angrisani, Holmes (2025), *Pauli Propagation*
(arXiv:2505.21606), Theory Box 3.
-/

@[expose] public section

namespace QuantumAlg

/-- Per-layer truncation data for a Pauli-propagation simulation: the discarded
`ℓ¹`-norm at each layer and the total error, bounded by their sum (Rudolph et al.
2025). -/
structure PauliPropagationTruncation where
  /-- Number of circuit layers. -/
  layers : ℕ
  /-- `ℓ¹`-norm of the Pauli terms discarded at each layer. -/
  discarded : ℕ → ℝ
  /-- Discarded norms are nonnegative. -/
  discarded_nonneg : ∀ i, 0 ≤ discarded i
  /-- Total simulation error. -/
  totalError : ℝ
  /-- Triangle-inequality bound: the error is at most the sum of discarded norms. -/
  error_le : totalError ≤ ∑ i ∈ Finset.range layers, discarded i

namespace PauliPropagationTruncation

variable (M : PauliPropagationTruncation)

/-- The error bound (sum of discarded norms) is nonnegative. -/
theorem sum_discarded_nonneg :
    0 ≤ ∑ i ∈ Finset.range M.layers, M.discarded i :=
  Finset.sum_nonneg fun i _ => M.discarded_nonneg i

/-- Exact propagation: if nothing is discarded, the simulation error is `≤ 0`. -/
theorem exact (h : ∀ i, M.discarded i = 0) : M.totalError ≤ 0 := by
  have hsum : ∑ i ∈ Finset.range M.layers, M.discarded i = 0 :=
    Finset.sum_eq_zero fun i _ => h i
  exact hsum ▸ M.error_le

end PauliPropagationTruncation

end QuantumAlg
