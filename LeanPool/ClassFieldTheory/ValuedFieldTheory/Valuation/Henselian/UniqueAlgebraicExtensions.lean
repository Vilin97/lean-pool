/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionPrimitive
/-!
# unique extension criterion

Valuations are regarded valuations up to equivalence.  Accordingly, uniqueness on
an algebraic extension is stated as literal uniqueness of its valuation
subring.  This is the same endpoint used in the finite norm-formula theorem.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

universe u

/-- A valuation subring has a unique extension valuation ring to `L`. -/
def HasUniqueValuationSubringExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) : Prop :=
  ∃! W : ValuationSubring L, V.valuation.HasExtension W.valuation

/-- A valuation subring has a unique extension valuation ring on every
algebraic extension in the same universe.  This is the valuation-ring form
of the right-hand side of the unique-extension criterion. -/
def HasUniqueAlgebraicValuationSubringExtensions
    {K : Type u} [Field K] (V : ValuationSubring K) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L],
    HasUniqueValuationSubringExtension (L := L) V

/-- Unique extension on every algebraic field supplies the exact monic
coprime-factor lifting property.  Factor the monic polynomial into monic
irreducibles over the valuation ring; uniqueness on each splitting field
forces every irreducible reduction to lie wholly on one side of a coprime
residual factorization. -/
theorem monicResidualCoprimeFactorLifting_of_unique_algebraic_extensions
    {K : Type u} [Field K] (V : ValuationSubring K)
    (hunique : HasUniqueAlgebraicValuationSubringExtensions V) :
    DiscreteValuationField.MonicResidualCoprimeFactorLifting V := by
  intro f gbar hbar hf hgbar hhbar hfactor hcoprime
  obtain ⟨factors, hfactors, hprod⟩ :=
    monic_eq_prod_monic_irreducible_map_factors V f hf
  have hredprod :
      (factors.map
        (fun Q => Q.map (IsLocalRing.residue V))).prod = gbar * hbar := by
    calc
      (factors.map
          (fun Q => Q.map (IsLocalRing.residue V))).prod =
          factors.prod.map (IsLocalRing.residue V) := by
            rw [Polynomial.map_multiset_prod]
      _ = f.map (IsLocalRing.residue V) := by rw [hprod]
      _ = gbar * hbar := hfactor
  obtain ⟨G, H, hG, hH, hGH, hGbar, hHbar⟩ :=
    partition_monic_irreducible_factors_along_coprime_reduction
      V hunique factors hfactors gbar hbar hgbar hhbar hredprod hcoprime
  exact ⟨G, H, hG, hH, hprod.symm.trans hGH, hGbar, hHbar⟩

/-- the unique-extension criterion, forward direction.  the primitive factorization definition,
in its exact
factorization form, gives a unique extension valuation ring on every
algebraic extension. -/
theorem henselianUniqueExtension_unique_algebraic_valuationSubring_extension_of_henselian
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation) :
    HasUniqueValuationSubringExtension
      (L := L) (absoluteValueValuationSubring v hnonarch) := by
  let V := absoluteValueValuationSubring v hnonarch
  obtain ⟨B, hB, hBuniq⟩ :=
    normFormula_algebraic_extension (K := K) (L := L)
      v hnonarch hhens
  refine ⟨B, hB.1, ?_⟩
  intro W hW
  apply hBuniq W
  refine ⟨hW, ?_⟩
  have hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty V :=
    (henselianValuation_iff_henselFactorization v hnonarch).1 hhens
  have hvalV :
      ∀ z : L,
        z ∈ (integralClosure V L).toSubring ∨
          z⁻¹ ∈ (integralClosure V L).toSubring :=
    normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization
      v hnonarch hv
  have hval :
      ∀ z : L,
        z ∈ (integralClosure V.valuation.valuationSubring L).toSubring ∨
          z⁻¹ ∈
            (integralClosure V.valuation.valuationSubring L).toSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    exact hvalV
  let : V.valuation.HasExtension W.valuation := hW
  have hWic :
      W =
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) V.valuation hval := by
    simpa only [ValuationSubring.valuationSubring_valuation] using
      DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
        (K := K) (L := L) V hval W.valuation
  change W.toSubring = (integralClosure V L).toSubring
  rw [hWic]
  ext z
  change z ∈
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) V.valuation hval ↔ z ∈ (integralClosure V L).toSubring
  rw [ValuationTheory.DiscreteValuationField.Valuation.mem_integralClosureValuationSubringOfMemOrInv
      V.valuation hval z]
  rw [ValuationSubring.valuationSubring_valuation]

/-- the unique-extension criterion, forward implication simultaneously for every algebraic
extension. -/
theorem henselianUniqueExtension_unique_algebraic_valuationSubring_extensions_of_henselian
    {K : Type u} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation) :
    HasUniqueAlgebraicValuationSubringExtensions
      (absoluteValueValuationSubring v hnonarch) := by
  intro L _ _ _
  exact
    henselianUniqueExtension_unique_algebraic_valuationSubring_extension_of_henselian
      (L := L) v hnonarch hhens

/-- the unique-extension criterion, converse in the exact factorization form of the primitive
factorization definition.
The Galois argument gives the primitive-irreducible reduction property, and
the primitive-factor partition turns it into the required degree-controlled
factorization. -/
theorem henselFactorization_of_unique_algebraic_valuationSubring_extensions
    {K : Type u} [Field K] (V : ValuationSubring K)
    (hunique : HasUniqueAlgebraicValuationSubringExtensions V) :
    ValuationTheory.DiscreteValuationField.HenselFactorizationProperty V := by
  apply
    DiscreteValuationField.henselFactorization_of_primitiveIrreducibleReductionProperty
  exact
    primitiveIrreducibleReductionProperty_of_unique_algebraic_extensions
      V hunique

/-- The converse of the unique-extension criterion for the valuation attached to the construction's
nonarchimedean absolute value. -/
theorem henselianUniqueExtension_henselian_of_unique_algebraic_valuationSubring_extensions
    {K : Type u} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hunique : HasUniqueAlgebraicValuationSubringExtensions
      (absoluteValueValuationSubring v hnonarch)) :
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation := by
  change ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
    ((absoluteValueValuationSubring
      v hnonarch).valuation.valuationSubring)
  rw [ValuationSubring.valuationSubring_valuation]
  intro f gbar hbar hprimitive hfactor hcoprime
  exact
    (henselFactorization_of_unique_algebraic_valuationSubring_extensions
      (absoluteValueValuationSubring v hnonarch) hunique)
      hprimitive hfactor hcoprime

/-- the unique-extension criterion.  A nonarchimedean valuation is Henselian exactly when its
valuation ring has a unique extension valuation ring on every algebraic
extension.  Literal equality of valuation rings is the equivalence
relation on valuations. -/
theorem henselianUniqueExtension_henselian_iff_unique_algebraic_valuationSubring_extensions
    {K : Type u} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (absoluteValueValuationSubring
          v hnonarch).valuation ↔
      HasUniqueAlgebraicValuationSubringExtensions
        (absoluteValueValuationSubring v hnonarch) := by
  constructor
  · exact
      henselianUniqueExtension_unique_algebraic_valuationSubring_extensions_of_henselian
        v hnonarch
  · exact
      henselianUniqueExtension_henselian_of_unique_algebraic_valuationSubring_extensions
        v hnonarch

end Valuations
end AlgebraicNumberTheory

end
