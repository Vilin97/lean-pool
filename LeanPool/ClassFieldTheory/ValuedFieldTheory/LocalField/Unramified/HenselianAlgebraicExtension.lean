/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.Definitions
/-!
# Henselianity along algebraic valued extensions

The proof of the unramified base-change theorem applies Hensel's lemma after
base change from `K` to an algebraic extension `K'`.  This file supplies the
source used there: the unique extension of a Henselian valuation to an
algebraic field is again Henselian.  The result is derived from the unique
extension criterion of the unique-extension criterion, rather than added as an assumption to
the unramified base-change theorem.
-/

@[expose] public section

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

universe u


/-- The exponential presentation of a Henselian valuation has a unique
valuation-subring extension to every algebraic field in the same universe.
This is the unique-extension criterion transported through the associated nonarchimedean
absolute value. -/
theorem exponentialValuation_hasUniqueAlgebraicValuationSubringExtensions
    {K : Type u} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    HasUniqueAlgebraicValuationSubringExtensions
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v) := by
  let av := exponentialAssociatedAbsoluteValue v
  have hav : LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1) av :=
    exponentialAssociatedAbsoluteValue_associated v
  have havNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue av :=
    associatedAbsoluteValue_nonarchimedean v (Real.exp 1) av hav
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Va := absoluteValueValuationSubring av havNonarch
  have hV : Vv = Va :=
    associatedAbsoluteValue_valuationSubring_eq
      v (Real.exp 1) av havNonarch hav
  have hhensA : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
    Va.valuation := by
    rw [← hV]
    exact hhens
  change HasUniqueAlgebraicValuationSubringExtensions Vv
  rw [hV]
  exact henselianUniqueExtension_unique_algebraic_valuationSubring_extensions_of_henselian
    av havNonarch hhensA


/-- An algebraic extension of a Henselian valued field is Henselian for its
unique extended valuation.

Only the actual exact extension of the two exponential valuations is an
input.  For a further algebraic extension `M/L`, uniqueness over `K` first
forces the restriction of its unique valuation ring to be the chosen ring on
`L`; transitivity then gives uniqueness over `L`, and the unique-extension criterion supplies
Hensel factorization on the target valuation ring. -/
theorem henselianValuation_of_algebraic_extension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w).valuation := by
  let av := exponentialAssociatedAbsoluteValue v
  let aw := exponentialAssociatedAbsoluteValue w
  have hav : LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1) av :=
    exponentialAssociatedAbsoluteValue_associated v
  have haw : LubinTate.Valuations.AssociatedAbsoluteValue w (Real.exp 1) aw :=
    exponentialAssociatedAbsoluteValue_associated w
  have havNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue av :=
    associatedAbsoluteValue_nonarchimedean v (Real.exp 1) av hav
  have hawNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue aw :=
    associatedAbsoluteValue_nonarchimedean w (Real.exp 1) aw haw
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  let Va := absoluteValueValuationSubring av havNonarch
  let Wa := absoluteValueValuationSubring aw hawNonarch
  have hV : Vv = Va :=
    associatedAbsoluteValue_valuationSubring_eq
      v (Real.exp 1) av havNonarch hav
  have hW : Wv = Wa :=
    associatedAbsoluteValue_valuationSubring_eq
      w (Real.exp 1) aw hawNonarch haw
  have habsExt : ∀ a : K, aw (algebraMap K L a) = av a :=
    associatedAbsoluteValue_extends
      v w hExt (Real.exp 1) av aw hav haw
  have hVaWa : Va.valuation.HasExtension Wa.valuation :=
    absoluteValueValuation_hasExtension_of_extends
      av aw havNonarch hawNonarch habsExt
  have hVvWv : Vv.valuation.HasExtension Wv.valuation := by
    rw [hV, hW]
    exact hVaWa
  let : Vv.valuation.HasExtension Wv.valuation := hVvWv
  have hUniqueV : HasUniqueAlgebraicValuationSubringExtensions Vv :=
    exponentialValuation_hasUniqueAlgebraicValuationSubringExtensions
      v hhens
  have hUniqueVW : HasUniqueValuationSubringExtension (L := L) Vv :=
    hUniqueV L
  have hUniqueW : HasUniqueAlgebraicValuationSubringExtensions Wv := by
    intro M _fieldM _algLM _algM
    let : Algebra K M :=
      ((algebraMap L M).comp (algebraMap K L)).toAlgebra
    let : IsScalarTower K L M :=
      IsScalarTower.of_algebraMap_eq (by intro; rfl)
    let : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.trans K L M
    obtain ⟨B, hVB, hBunique⟩ := hUniqueV M
    let : Vv.valuation.HasExtension B.valuation := hVB
    let vBL := B.valuation.comap (algebraMap L M)
    have hVvBL : Vv.valuation.HasExtension vBL :=
      DiscreteValuationField.Valuation.comap_to_middle_hasExtension_of_top_hasExtension
        Vv.valuation B.valuation
    let : Vv.valuation.HasExtension vBL := hVvBL
    have hVvRestrict :
        Vv.valuation.HasExtension vBL.valuationSubring.valuation := by
      apply _root_.Valuation.HasExtension.ofComapInteger
      ext a
      simp only [Subring.mem_comap, Valuation.mem_integer_iff,
        ValuationSubring.valuation_le_one_iff]
      rw [vBL.mem_valuationSubring_iff]
      rw [← Vv.valuationSubring_valuation]
      rw [Vv.valuation.mem_valuationSubring_iff]
      exact _root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := Vv.valuation) (vA := vBL) a
    let : Vv.valuation.HasExtension vBL.valuationSubring.valuation :=
      hVvRestrict
    have hrestrict : vBL.valuationSubring = Wv := by
      obtain ⟨W0, hVW0, hW0unique⟩ := hUniqueVW
      exact (hW0unique vBL.valuationSubring inferInstance).trans
        (hW0unique Wv inferInstance).symm
    have hWB : Wv.valuation.HasExtension B.valuation := by
      apply _root_.Valuation.HasExtension.ofComapInteger
      change vBL.valuationSubring.toSubring =
        Wv.valuation.valuationSubring.toSubring
      rw [ValuationSubring.valuationSubring_valuation]
      exact congrArg ValuationSubring.toSubring hrestrict
    refine ⟨B, hWB, ?_⟩
    intro C hWC
    let : Wv.valuation.HasExtension C.valuation := hWC
    let : Vv.valuation.HasExtension C.valuation :=
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
        Vv.valuation Wv.valuation C.valuation
    exact hBunique C inferInstance
  change ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
    Wv.valuation.valuationSubring
  rw [ValuationSubring.valuationSubring_valuation]
  exact henselFactorization_of_unique_algebraic_valuationSubring_extensions
    Wv hUniqueW

end Valuations
end AlgebraicNumberTheory

end
