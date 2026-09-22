/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.ValuationRingEquiv
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
/-!
# The ramification index of the totally ramified cyclotomic extension

This file maps the Eisenstein unit relation into the target valuation ring and proves `e = [L :
  ℚ_[p]]`, together with the uniformizer statement.
-/

open _root_.LocalFieldTheory.DiscreteValuationField.ValuedExtension renaming
  target_maximalIdeal_pow_not_le_pow_succ →
    target_maximalIdeal_pow_not_le_pow_succ


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

/-- The `ℤ_[p]`-algebra on the cyclotomic extension is induced through `ℚ_[p]`. -/
local instance padicCyclotomicTotallyRamifiedRamificationIndexAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedRamificationIndexScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The ideal-theoretic core of the totally ramified cyclotomic theorem(i): for the actual
integral-closure valuation, `1 - ζ` is a uniformizer and the Eisenstein
relation forces the ramification index to equal the field degree. -/
theorem padicCyclotomicTotallyRamified_uniformizer_and_ramificationIndex_eq_degree
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤)
    [FiniteDimensional ℚ_[p] L] [Algebra.IsSeparable ℚ_[p] L]
    (target : CompleteDVF.{u, 0} L)
    [hExt : (padicCompleteDVF p).valuation.HasExtension
      target.valuation]
    [hTarget : IsIntegralClosure target.valuationSubring
      (padicCompleteDVF p).valuationSubring L] :
    target.valuation.IsUniformizer (1 - ζ) ∧
      ValuedExtension.ramificationIndex
          (padicCompleteDVF p).toDVF target.toDVF =
        ValuedExtension.degree
          (padicCompleteDVF p).toDVF target.toDVF := by
  let n := p ^ (k + 1)
  let d := Nat.totient n
  let α : L := ζ - 1
  let Aζ := Algebra.adjoin ℤ_[p] ({ζ} : Set L)
  let A := Algebra.adjoin ℤ_[p] ({α} : Set L)
  let a : A := ⟨α, Algebra.self_mem_adjoin_singleton ℤ_[p] α⟩
  have hadjoin : Aζ = A := by
    simpa [Aζ, A, α] using
      (padicCyclotomicTotallyRamified_adjoin_sub_one_eq_adjoin ζ).symm
  let eζα : Aζ ≃+* A := (Subalgebra.equivOfEq Aζ A hadjoin).toRingEquiv
  have hprimeβ : Prime (padicCyclotomicTotallyRamifiedOneSubPrimitiveRootInteger (p := p) ζ) :=
    padicCyclotomicTotallyRamified_one_sub_primitiveRoot_prime ζ hζ hgen
  have hprimeNegA : Prime (-a) := by
    have hmapped : Prime
        (eζα (padicCyclotomicTotallyRamifiedOneSubPrimitiveRootInteger (p := p) ζ)) :=
      (MulEquiv.prime_iff eζα).2 hprimeβ
    convert hmapped using 1
    apply Subtype.ext
    simp [eζα, padicCyclotomicTotallyRamifiedOneSubPrimitiveRootInteger, a, α, Aζ, A]
  have hirrA : Irreducible a := by
    have hassoc : Associated (-a) a :=
      (Associated.refl a).neg_left
    exact hassoc.irreducible hprimeNegA.irreducible
  obtain ⟨y, hyu, hy⟩ :=
    padicCyclotomicTotallyRamified_exists_unit_mul_p_eq_sub_one_pow ζ hζ hgen
  change algebraMap ℤ_[p] A (p : ℤ_[p]) * y = a ^ d at hy
  have hdDegree : d = Module.finrank ℚ_[p] L := by
    exact (padicCyclotomicTotallyRamified_finrank_eq_totient ζ hζ hgen).symm
  let base := padicCompleteDVF p
  let V := base.valuationSubring
  let : Algebra V L := Algebra.ofSubsemiring base.valuation.valuationSubring
  let : IsScalarTower V ℚ_[p] L := IsScalarTower.of_algebraMap_eq' rfl
  let eZV : ℤ_[p] ≃+* V :=
    padicIntEquivValuationSubring p
  let : IsIntegralClosure target.valuationSubring V L := by
    simpa [V] using hTarget
  let : IsScalarTower V target.valuationSubring L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  obtain ⟨q, hq⟩ :=
    padicCyclotomicTotallyRamified_exists_adjoin_sub_one_equiv_valuationSubring
      ζ hζ hgen target
  change A ≃+* target.valuationSubring at q
  change ∀ z : A, algebraMap target.valuationSubring L (q z) =
    algebraMap A L z at hq
  let ϖ : V := eZV (p : ℤ_[p])
  have hϖirr : Irreducible ϖ :=
    (MulEquiv.irreducible_iff eZV).2 PadicInt.irreducible_p
  have hϖ : base.valuation.IsUniformizer (ϖ : ℚ_[p]) :=
    base.valuation.isUniformizer_of_maximalIdeal_eq_span hϖirr.maximalIdeal_eq
  let π : target.valuationSubring := q a
  have hπirr : Irreducible π :=
    (MulEquiv.irreducible_iff q).2 hirrA
  have hπ : target.valuation.IsUniformizer (π : L) :=
    target.valuation.isUniformizer_of_maximalIdeal_eq_span hπirr.maximalIdeal_eq
  have hπcoe : (π : L) = ζ - 1 := by
    calc
      (π : L) = algebraMap A L a := hq a
      _ = ζ - 1 := rfl
  have hone : target.valuation.IsUniformizer (1 - ζ) := by
    rw [show 1 - ζ = -(ζ - 1) by ring, ← hπcoe]
    simpa [Valuation.IsUniformizer] using hπ
  have hpmap : q (algebraMap ℤ_[p] A (p : ℤ_[p])) =
      ValuedExtension.integerMap
        base.toDVF target.toDVF ϖ := by
    apply Subtype.ext
    change algebraMap target.valuationSubring L
      (q (algebraMap ℤ_[p] A (p : ℤ_[p]))) =
        algebraMap target.valuationSubring L
          (ValuedExtension.integerMap
            base.toDVF target.toDVF ϖ)
    rw [hq]
    rfl
  have hyq := congrArg q hy
  simp only [map_mul, map_pow] at hyq
  have hassocQ : Associated
      (q (algebraMap ℤ_[p] A (p : ℤ_[p]))) ((q a) ^ d) := by
    refine ⟨(hyu.map q).unit, ?_⟩
    simpa using hyq
  have ha : Associated
      (ValuedExtension.integerMap
        base.toDVF target.toDVF ϖ)
      (π ^ d) := by
    rw [← hpmap]
    exact hassocQ
  have hmapT : Ideal.map
      (ValuedExtension.integerMap
        base.toDVF target.toDVF)
      base.maximalIdeal =
      target.maximalIdeal ^ d := by
    calc
      _ = Ideal.span
          ({ValuedExtension.integerMap
              base.toDVF target.toDVF ϖ} :
            Set target.valuationSubring) := by
        rw [base.maximalIdeal_eq_span_uniformizer hϖ, Ideal.map_span,
          Set.image_singleton]
      _ = Ideal.span ({π ^ d} : Set target.valuationSubring) :=
        (Ideal.span_singleton_eq_span_singleton).2 ha
      _ = (Ideal.span ({π} : Set target.valuationSubring)) ^ d := by
        rw [Ideal.span_singleton_pow]
      _ = target.maximalIdeal ^ d := by
        rw [← target.maximalIdeal_eq_span_uniformizer hπ]
  have hnot : ¬ Ideal.map
      (ValuedExtension.integerMap base.toDVF target.toDVF)
      base.maximalIdeal ≤ target.maximalIdeal ^ (d + 1) := by
    rw [hmapT]
    exact
      target_maximalIdeal_pow_not_le_pow_succ
        target hπ d
  have he :
      ValuedExtension.ramificationIndex
        base.toDVF target.toDVF = d := by
    rw [ValuedExtension.ramificationIndex]
    apply Ideal.ramificationIdx'_spec
    · simpa [ValuedExtension.integerMap] using hmapT.le
    · simpa [ValuedExtension.integerMap] using hnot
  have hramDegree :
      ValuedExtension.ramificationIndex
          base.toDVF target.toDVF =
        ValuedExtension.degree
          base.toDVF target.toDVF := by
    calc
      ValuedExtension.ramificationIndex
          base.toDVF target.toDVF = d := he
      _ = Module.finrank ℚ_[p] L := hdDegree
      _ = ValuedExtension.degree
          base.toDVF target.toDVF :=
        (ValuedExtension.degree_eq_finrank
          base.toDVF target.toDVF).symm
  exact ⟨hone, hramDegree⟩

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
