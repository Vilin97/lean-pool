/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinRelation
/-!
# Translation of the integral ring in the totally ramified cyclotomic extension

This file records that translating `ζ` by one preserves the explicit integral closure.
-/

@[expose] public section

noncomputable
section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open scoped Polynomial

universe u

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

/-- The `ℤ_[p]`-algebra on the cyclotomic extension is induced through `ℚ_[p]`. -/
local instance padicCyclotomicTotallyRamifiedIntegralTranslateAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedIntegralTranslateScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Translating the generator by one does not change the explicit
`ℤ_[p]`-algebra. -/
theorem padicCyclotomicTotallyRamified_adjoin_sub_one_eq_adjoin
    (ζ : L) :
    Algebra.adjoin ℤ_[p] ({ζ - 1} : Set L) =
      Algebra.adjoin ℤ_[p] ({ζ} : Set L) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Subalgebra.sub_mem _
      (Algebra.self_mem_adjoin_singleton ℤ_[p] ζ)
      (Subalgebra.one_mem _)
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simpa using Subalgebra.add_mem _
      (Algebra.self_mem_adjoin_singleton ℤ_[p] (ζ - 1))
      (Subalgebra.one_mem _)

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
