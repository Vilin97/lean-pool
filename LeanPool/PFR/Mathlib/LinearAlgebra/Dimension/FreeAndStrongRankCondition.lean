/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Cardinality bounds for finite-dimensional modules
-/

open Cardinal Module Module Set Submodule

universe u v

variable {K : Type u} {V : Type v} [Ring K] [StrongRankCondition K]
  [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]

variable (K V) in
public
theorem cardinal_le_aleph0_of_finiteDimensional [h : Countable K] :
    #V ≤ ℵ₀ := by
  rw [← lift_le_aleph0.{v, u}, lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank K V]
  apply power_le_aleph0 (lift_le_aleph0.mpr (mk_le_aleph0_iff.mpr h))
    (lift_lt_aleph0.mpr (rank_lt_aleph0 K V))

variable (K V) in
public
theorem countable_of_finiteDimensional [h : Countable K] : Countable V := by
  have : #V ≤ ℵ₀ := cardinal_le_aleph0_of_finiteDimensional K V
  exact mk_le_aleph0_iff.mp this
