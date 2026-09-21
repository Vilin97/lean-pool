/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayPrincipalIdealSubgroup
import Mathlib.Algebra.Group.Subgroup.Lattice
/-!
# Membership in the ray-principal ideal subgroup

The ray-congruent generators already form a subgroup under the principal
ideal map, so taking their subgroup closure adds no new ideals.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- A fractional ideal is ray-principal exactly when it has one
ray-congruent nonzero generator. -/
theorem mem_rayPrincipalIdealSubgroup_iff
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K)
    (I : NumberFieldFractionalIdealGroup K) :
    I ∈ rayPrincipalIdealSubgroup m ↔
      ∃ x : Kˣ, IsRayCongruent m x ∧
        toPrincipalIdeal (𝓞 K) K x = I := by
  let P : Subgroup (NumberFieldFractionalIdealGroup K) := {
    carrier := {J | ∃ x : Kˣ,
      IsRayCongruent m x ∧ toPrincipalIdeal (𝓞 K) K x = J}
    one_mem' := by
      refine ⟨1, IsRayCongruent.one m, ?_⟩
      simp only [map_one]
    mul_mem' := by
      rintro J J' ⟨x, hx, hxJ⟩ ⟨y, hy, hyJ⟩
      refine ⟨x * y, IsRayCongruent.mul hx hy, ?_⟩
      rw [map_mul, hxJ, hyJ]
    inv_mem' := by
      rintro J ⟨x, hx, hxJ⟩
      refine ⟨x⁻¹, IsRayCongruent.inv hx, ?_⟩
      rw [map_inv, hxJ] }
  have hP : rayPrincipalIdealSubgroup m = P := by
    change Subgroup.closure (P : Set (NumberFieldFractionalIdealGroup K)) = P
    exact Subgroup.closure_eq P
  rw [hP]
  rfl

end ClassFieldTheory
