/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteExtensionClassFieldAxiom
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateComparison

/-! # Local Class Field Axiom -/
namespace LocalClassFieldTheory
open CyclicCohomology ClassFormation

open LocalFieldTheory

/-!
# The local multiplicative group satisfies the class-field axiom

For a finite cyclic abstract tower `L / K / k`, the closed subgroups are
replaced by their concrete fixed fields.  The lower fixed field is finite
over the local ground field and the upper fixed field is finite Galois over
it.  The finite-tower form of the local class-field-axiom theorem therefore
applies.  The fixed unit representation and cyclic Tate-complex comparisons
then transport its two cardinality statements back to the abstract
class-field-axiom predicate.
-/

noncomputable section

open CategoryTheory

/-- **The local class-field-axiom theorem, abstract class-field-axiom form.**

For any Galois ambient field over a nonarchimedean local field, its ambient
unit representation satisfies the abstract class-field-axiom predicate.
The predicate ranges only over towers whose lower field is finite over the
distinguished base, in the fixed-separable-closure model. -/
private theorem galoisAmbientUnits_satisfiesClassFieldAxiom
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω) := by
  rintro ⟨K, hKfinite⟩
  rintro ⟨L, hLK, hnormal, hfinite, g, hg⟩
  let := hKfinite
  let := hnormal
  let := hfinite
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let : Fintype Q := Fintype.ofFinite Q
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω hLK
  let : FiniteDimensional k F :=
    abstractFixedField_finiteDimensional k Ω K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKfinite hfinite
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois k Ω K L hLK hnormal
  let eQ : Q ≃* Gal(E/F) :=
    abstractExtensionQuotientEquivGaloisGroup k Ω K L hLK hnormal
  let g' : Gal(E/F) := eQ g
  have hg' : ∀ σ : Gal(E/F), σ ∈ Subgroup.zpowers g' :=
    map_cyclicGenerator eQ g hg
  have hUnitsTateCard := finiteTowerUnits_tate_card_of_generator k F E g' hg'
  let : IsCyclic Q := CyclicCohomology.isCyclic_of_generator g hg
  let : CommGroup Q := IsCyclic.commGroup
  let : IsCyclic (Gal(E/F)) :=
    CyclicCohomology.isCyclic_of_generator g' hg'
  let : CommGroup (Gal(E/F)) := IsCyclic.commGroup
  let M := extensionFixedRepresentation
    (galoisAmbientUnitsRep k Ω) K L hLK hnormal
  let U := Rep.ofAlgebraAutOnUnits F E
  let eM : M ≅
      Rep.res eQ.toMonoidHom U :=
    abstractExtensionFixedRepresentationIsoUnitsRes
      k Ω K L hLK hnormal
  let eH0 :
      (Rep.FiniteCyclicGroup.normHomCompSub M g).homology ≅
        (Rep.FiniteCyclicGroup.normHomCompSub U g').homology :=
    (normHomCompSubHomologyIsoOfRepIso eM g) ≪≫
      normHomCompSubHomologyResEquivIso eQ U g
  let eHm1 :
      (Rep.FiniteCyclicGroup.subCompNormHom M g).homology ≅
        (Rep.FiniteCyclicGroup.subCompNormHom U g').homology :=
    (subCompNormHomHomologyIsoOfRepIso eM g) ≪≫
      subCompNormHomHomologyResEquivIso eQ U g
  let eTateH0 :
      tateCohomology M 0 ≅ tateCohomology U 0 :=
    TateCohomology.isoFiniteCyclicZero M g hg ≪≫ eH0 ≪≫
      (TateCohomology.isoFiniteCyclicZero U g' hg').symm
  let eTateHm1 :
      tateCohomology M (-1) ≅ tateCohomology U (-1) :=
    TateCohomology.isoFiniteCyclicNegOne M g hg ≪≫ eHm1 ≪≫
      (TateCohomology.isoFiniteCyclicNegOne U g' hg').symm
  let : Finite (tateCohomology U 0) :=
    hUnitsTateCard.finiteH0
  have hUTateMinusOneZero :
      Limits.IsZero (tateCohomology U (-1)) :=
    hilbert90_unitsTateHminusOne_isZero F E g' hg'
  let : Subsingleton (tateCohomology U (-1)) :=
    ModuleCat.subsingleton_of_isZero hUTateMinusOneZero
  let : Finite (tateCohomology U (-1)) := by infer_instance
  let : Finite (tateCohomology M 0) :=
    Finite.of_equiv (tateCohomology U 0) eTateH0.symm.toLinearEquiv.toEquiv
  let : Finite (tateCohomology M (-1)) :=
    Finite.of_equiv (tateCohomology U (-1)) eTateHm1.symm.toLinearEquiv.toEquiv
  have hH0actual :
      Nat.card (tateCohomology U 0) =
        Module.finrank F E :=
    hUnitsTateCard.cardH0
  have hHm1actual :
      Nat.card (tateCohomology U (-1)) = 1 :=
    hUnitsTateCard.cardHminusOne
  refine
    { finiteTateHZero := by
        change Finite (tateCohomology M 0)
        infer_instance
      finiteTateHMinusOne := by
        change Finite (tateCohomology M (-1))
        infer_instance
      tateHZero_card := ?_
      tateHMinusOne_card := ?_ }
  · change Nat.card
      (tateCohomology M 0) =
        ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ)
    calc
      Nat.card (tateCohomology M 0) =
          Nat.card (tateCohomology U 0) :=
        Nat.card_congr eTateH0.toLinearEquiv.toEquiv
      _ = Module.finrank F E := hH0actual
      _ = ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) :=
        (finiteAbstractExtension_degree_eq_finrank
          k Ω K L hLK hnormal hKfinite hfinite).symm
  · change Nat.card
      (tateCohomology M (-1)) = 1
    calc
      Nat.card (tateCohomology M (-1)) =
          Nat.card (tateCohomology U (-1)) :=
        Nat.card_congr eTateHm1.toLinearEquiv.toEquiv
      _ = 1 := hHm1actual

/-- The coefficient module A = (kˢᵉᵖ)ˣ satisfies the abstract
class-field axiom.  This is the separable-closure specialization used for local
reciprocity. -/
theorem separableClosureUnits_isClassFormation
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k (SeparableClosure k)) :=
  galoisAmbientUnits_satisfiesClassFieldAxiom k (SeparableClosure k)

end
end LocalClassFieldTheory
