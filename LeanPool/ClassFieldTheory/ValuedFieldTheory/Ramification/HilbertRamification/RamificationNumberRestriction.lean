/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.OrbitPolynomialIdeal
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.FixedFieldRamificationIndex
/-!
# quotient-depth identity over a general DVF

The public endpoint has no generator argument.  The monogenic integral-generator theorem
  supplies the top
integral generator internally, while the fixed-field ramification number is
the intrinsic value of its displacement ideal.
-/

@[expose] public section

noncomputable
section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]
variable [FiniteDimensional K L] [IsGalois K L]

/-- Sum of ramification numbers over the right coset `sigma H`, for a
specified top generator. -/
def cosetRamificationNumberSum
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (sigma : Gal(L/K))
    (z : target.valuationSubring) : ℕ∞ := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  exact ∑ tau : H, ramificationNumberOfUniqueExtension
    (base := base) (target := target) huniq z (sigma * tau)

omit [IsGalois K L] in
/-- The valuation of the coset displacement product is the corresponding
sum of ramification numbers. -/
theorem addVal_cosetGeneratorDisplacementProduct
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (sigma : Gal(L/K))
    (z : target.valuationSubring) :
    IsDiscreteValuationRing.addVal target.valuationSubring
        (cosetGeneratorDisplacementProductDVF
          (base := base) (target := target) huniq H sigma z) =
      cosetRamificationNumberSum
        (base := base) (target := target) huniq H sigma z := by
  classical
  let : Fintype H := Fintype.ofFinite H
  unfold cosetGeneratorDisplacementProductDVF
  simp only [cosetRamificationNumberSum,
    ramificationNumberOfUniqueExtension]
  have hprod : ∀ s : Finset H,
      IsDiscreteValuationRing.addVal target.valuationSubring
          (∏ tau ∈ s,
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq (sigma * tau) z - z)) =
        ∑ tau ∈ s,
          IsDiscreteValuationRing.addVal target.valuationSubring
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq (sigma * tau) z - z) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert tau s htau ih =>
        rw [Finset.prod_insert htau, Finset.sum_insert htau,
          IsDiscreteValuationRing.addVal_mul, ih]
  simpa using hprod Finset.univ

variable [Algebra.IsSeparable base.residueField target.residueField]

/-- The canonical coset sum, with its monogenic integral generator hidden. -/
def intrinsicCosetRamificationNumberSum
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (sigma : Gal(L/K)) : ℕ∞ := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  exact ∑ tau : H, intrinsicRamificationNumberOfUniqueExtension
    (base := base) (target := target) huniq (sigma * tau)

/-- States the theorem `cosetRamificationNumberSum_eq_intrinsic`. -/
theorem cosetRamificationNumberSum_eq_intrinsic
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (sigma : Gal(L/K))
    {z : target.valuationSubring}
    (hz : Algebra.adjoin base.valuationSubring
      ({z} : Set target.valuationSubring) = ⊤) :
    cosetRamificationNumberSum
        (base := base) (target := target) huniq H sigma z =
      intrinsicCosetRamificationNumberSum
        (base := base) (target := target) huniq H sigma := by
  classical
  let : Fintype H := Fintype.ofFinite H
  simp only [cosetRamificationNumberSum,
    intrinsicCosetRamificationNumberSum,
    intrinsicRamificationNumberOfUniqueExtension]
  apply Finset.sum_congr rfl
  intro tau _
  exact ramificationNumberOfUniqueExtension_eq_of_adjoin_eq_top
    (base := base) (target := target) huniq hz
    (chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top
      (base := base) (target := target) huniq) (sigma * tau)

/-- The quotient-depth identity (division-free normalized form).

For `M = L ^ H` and `sigma' = sigma|_M`,

`e(L/M) * i_(M/K)(sigma') = sum_(tau in H) i_(L/K)(sigma tau)`.

The statement also covers the identity, where both sides are infinite. -/
theorem ramificationIndex_nsmul_fixedFieldRamificationNumber_eq_cosetSum
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K)) :
    fixedFieldRamificationIndex
          (target := target) H •
        fixedFieldRamificationNumber
          (base := base) (target := target) huniq H
          (IsGalois.normalAutEquivQuotient H sigma) =
      intrinsicCosetRamificationNumberSum
        (base := base) (target := target) huniq H sigma := by
  let B := fixedFieldValuationSubringDVF (K := K) (target := target) H
  let j := fixedFieldValuationSubringDVFToTarget
    (K := K) (target := target) H
  let q := IsGalois.normalAutEquivQuotient H sigma
  let J := fixedFieldDisplacementIdealDVF
    (base := base) (target := target) huniq H q
  let z := chosenRamificationGeneratorOfUniqueExtension
    (base := base) (target := target) huniq
  let : IsDiscreteValuationRing B :=
    fixedFieldValuationSubringDVF_isDiscreteValuationRing
      (base := base) (target := target) huniq H
  let g : B := Submodule.IsPrincipal.generator J
  have hz : Algebra.adjoin base.valuationSubring
      ({z} : Set target.valuationSubring) = ⊤ :=
    chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top
      (base := base) (target := target) huniq
  have hspanJ : Ideal.span ({g} : Set B) = J :=
    Submodule.IsPrincipal.span_singleton_generator J
  have hmapJ : Ideal.map j J =
      Ideal.span ({j g} : Set target.valuationSubring) := by
    rw [← hspanJ, Ideal.map_span, Set.image_singleton]
  have hideal :
      Ideal.span ({cosetGeneratorDisplacementProductDVF
          (base := base) (target := target) huniq H sigma z} :
        Set target.valuationSubring) =
        Ideal.span ({j g} : Set target.valuationSubring) := by
    rw [span_cosetGeneratorDisplacementProduct_eq_map_fixedFieldDisplacementIdeal
      (base := base) (target := target) huniq H sigma hz]
    exact hmapJ
  have hadd :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (cosetGeneratorDisplacementProductDVF
            (base := base) (target := target) huniq H sigma z) =
        IsDiscreteValuationRing.addVal target.valuationSubring (j g) :=
    (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2
      (Ideal.span_singleton_eq_span_singleton.mp hideal)
  have hfixed :
      fixedFieldRamificationNumber
          (base := base) (target := target) huniq H q =
        IsDiscreteValuationRing.addVal B g := by
    unfold fixedFieldRamificationNumber
    dsimp only
  calc
    fixedFieldRamificationIndex
          (target := target) H •
        fixedFieldRamificationNumber
          (base := base) (target := target) huniq H q =
        IsDiscreteValuationRing.addVal target.valuationSubring (j g) := by
      rw [hfixed]
      exact (addVal_fixedFieldValuationSubringToTarget_eq_ramificationIndex_nsmul
        (base := base) (target := target) huniq H g).symm
    _ = IsDiscreteValuationRing.addVal target.valuationSubring
        (cosetGeneratorDisplacementProductDVF
          (base := base) (target := target) huniq H sigma z) := hadd.symm
    _ = cosetRamificationNumberSum
        (base := base) (target := target) huniq H sigma z :=
      addVal_cosetGeneratorDisplacementProduct
        (base := base) (target := target) huniq H sigma z
    _ = intrinsicCosetRamificationNumberSum
        (base := base) (target := target) huniq H sigma :=
      cosetRamificationNumberSum_eq_intrinsic
        (base := base) (target := target) huniq H sigma hz

end Higher
end RamificationTheory.HilbertRamification
