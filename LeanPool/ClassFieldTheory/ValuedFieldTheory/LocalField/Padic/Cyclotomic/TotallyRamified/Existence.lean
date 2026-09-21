/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.RamificationIndex
/-!
# The totally ramified cyclotomic endpoint

This file packages the actual integral-closure complete-DVF model as a totally ramified extension.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open scoped Polynomial

universe u

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

local instance padicCyclotomicTotallyRamifiedRamificationEndpointAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedRamificationEndpointScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- the totally ramified cyclotomic theorem(i), valuative conclusion: the extension
`ℚ_[p](ζ) / ℚ_[p]` is totally ramified.  The target valuation is the
canonical complete discrete valuation supplied by the actual integral
closure of `ℤ_[p]` in `L`. -/
theorem padicCyclotomicTotallyRamified_exists_totallyRamified_extension
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    ∃ hfd : FiniteDimensional ℚ_[p] L,
      letI : FiniteDimensional ℚ_[p] L := hfd
      ∃ target : CompleteDVF.{u, 0} L,
        ∃ hExt :
          (padicCompleteDVF p).valuation.HasExtension
            target.valuation,
          letI :
            (padicCompleteDVF p).valuation.HasExtension
              target.valuation := hExt
          target.valuation.IsUniformizer (1 - ζ) ∧
            ValuedExtension.IsTotallyRamified
              (padicCompleteDVF p).toDVF target.toDVF := by
  let : NeZero (p ^ (k + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let : IsCyclotomicExtension {p ^ (k + 1)} ℚ_[p] L :=
    padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top ζ hζ hgen
  let hfd : FiniteDimensional ℚ_[p] L :=
    IsCyclotomicExtension.finiteDimensional {p ^ (k + 1)} ℚ_[p] L
  let : FiniteDimensional ℚ_[p] L := hfd
  let : Algebra.IsSeparable ℚ_[p] L := by infer_instance
  let base := padicCompleteDVF p
  obtain ⟨target, hExt, hTarget, _⟩ :=
    ValuedExtension.exists_integralClosure_standard_fundamental_identity
      (K := ℚ_[p]) (L := L) base
  let : base.valuation.HasExtension target.valuation := hExt
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L := hTarget
  let : IsScalarTower base.valuationSubring target.valuationSubring L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  have hsource :=
    padicCyclotomicTotallyRamified_uniformizer_and_ramificationIndex_eq_degree
      ζ hζ hgen target
  exact ⟨hfd, target, hExt, hsource.1,
    (LocalFieldTheory.DiscreteValuationField.ValuedExtension.isTotallyRamified_iff_ramificationIndex_eq_degree_of_finite_separable
        base target).2 hsource.2⟩

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
