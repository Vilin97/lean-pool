/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel

/-!
# Standard simplex barycentric coordinates

This module defines standard simplex coordinates as nonnegative weights summing to one,
with their induced topology and relative interior.
-/

public section

namespace NRR

open scoped BigOperators

/-- Barycentric coordinates of the standard `d`-simplex. -/
@[expose]
def StandardSimplex (d : ℕ) :=
  {w : Fin (d + 1) → ℝ // (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

namespace StandardSimplex

instance (d : ℕ) : TopologicalSpace (StandardSimplex d) :=
  TopologicalSpace.induced Subtype.val inferInstance

instance (d : ℕ) : CoeFun (StandardSimplex d) (fun _ => Fin (d + 1) → ℝ) :=
  ⟨fun w => w.1⟩

@[simp] theorem nonneg {d : ℕ} (w : StandardSimplex d) (i : Fin (d + 1)) :
    0 ≤ w i :=
  w.2.1 i

@[simp] theorem sum_eq_one {d : ℕ} (w : StandardSimplex d) :
    ∑ i, w i = 1 :=
  w.2.2

/-- The relative interior of the standard simplex. -/
@[expose]
def IsInterior {d : ℕ} (w : StandardSimplex d) : Prop :=
  ∀ i, 0 < w i

end StandardSimplex

end NRR
