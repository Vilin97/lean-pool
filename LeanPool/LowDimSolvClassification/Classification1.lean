/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Field.Defs
import LeanPool.LowDimSolvClassification.GeneralResults
import LeanPool.LowDimSolvClassification.InstancesLowDim

/-!
# LeanPool.LowDimSolvClassification.Classification1
-/

open Module
open Submodule
namespace LieAlgebra
namespace Dim1

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

section classification_dim_1

theorem abelian (h : Module.finrank K L = 1) : IsLieAbelian L :=by
  simp only [IsLieAbelian]
  constructor
  intro x y
  have := Module.finite_of_finrank_eq_succ h
  have B := Module.finBasisOfFinrankEq K L h
  rw [Basis.repr_fin_one B x, Basis.repr_fin_one B y]
  simp

theorem classification (h : Module.finrank K L = 1) :
    Nonempty (L ≃ₗ⁅K⁆ K) := by
  have := abelian h
  have := Module.finite_of_finrank_eq_succ h
  have B := Module.finBasisOfFinrankEq K L h
  constructor
  exact ({
    toFun := fun x ↦ B.repr x 0,
    invFun := fun x ↦ x • B 0,
    left_inv := by
      intro x
      simp only
      rw [← Basis.repr_fin_one B x]
    right_inv := fun _ => by simp
    map_add' := by simp
    map_smul' := by simp
    map_lie' := by
      intro x y
      rw [trivial_lie_zero L L x y]
      simp [Bracket.bracket, mul_comm]
  })

end classification_dim_1

section corollaries_dim_1

theorem _root_.LieAlgebra.Dim1.solvable (dim1 : Module.finrank K L = 1) :
    LieAlgebra.IsSolvable L := by
  obtain a := abelian dim1
  apply LieAlgebra.ofAbelianIsSolvable

end corollaries_dim_1

end Dim1

end LieAlgebra
