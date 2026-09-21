/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
/-!
# The global norm-residue symbol for finite Galois extensions

For an arbitrary finite Galois extension of number fields, the global
norm-residue quotient is the abelianization of the genuine Galois group:

`C_K / N_{L/K} C_L ≃ Gal(L / K)ᵃᵇ`.

The abelian specialization in `GlobalNormResidue` identifies this target
further with `Gal(L / K)`.  This file retains the abelianization and therefore
states global reciprocity at its full finite-Galois generality.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Idèle classes are commutative.  Keeping the mixin as a named local
instance lets norm-range quotient types elaborate before entering a
declaration body. -/
local instance
    globalNormResidueAbelianization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The abelianization of the compatible abstract extension quotient is the
abelianization of the actual Galois group. -/
noncomputable def
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization :
    Additive
        (Abelianization
          (ClassFormation.FiniteGaloisSubextension.extensionQuotient
            (numberFieldTowerFiniteGaloisSubextension K L))) ≃+
      Additive (Abelianization (Gal(L / K))) :=
  MulEquiv.toAdditive
    (MulEquiv.abelianizationCongr
      (numberFieldTowerExtensionQuotientEquivGaloisGroup K L))

private theorem numberFieldTowerAbelianizationCongr_of
    (q :
      ClassFormation.FiniteGaloisSubextension.extensionQuotient
        (numberFieldTowerFiniteGaloisSubextension K L)) :
    MulEquiv.abelianizationCongr
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L)
        (Abelianization.of q) =
      Abelianization.of
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L q) :=
  abelianizationCongr_of
    (numberFieldTowerExtensionQuotientEquivGaloisGroup K L) q

/-- The comparison on abelianizations sends the class of an abstract
automorphism to the class of its actual restriction to `L`. -/
@[simp]
theorem
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization_of
    (q :
      ClassFormation.FiniteGaloisSubextension.extensionQuotient
        (numberFieldTowerFiniteGaloisSubextension K L)) :
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
        K L (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul
        (Abelianization.of
          (numberFieldTowerExtensionQuotientEquivGaloisGroup K L q)) := by
  exact
    congrArg Additive.ofMul
      (numberFieldTowerAbelianizationCongr_of K L q)

/-- The abstract norm-residue symbol followed by the concrete Galois
comparison.  This declaration boundary keeps the dependent quotient indices
and their instance packages from being reconstructed at each evaluation. -/
private noncomputable def
    numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv :
    FiniteNormQuotient rationalIdeleClassRepresentation
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L) ≃+
      Additive (Abelianization (Gal(L / K))) := by
  let _ : Finite _ :=
    (numberFieldTowerReciprocityFiniteAbstractField K L).finite
  let _ :
      (CyclicCohomology.extensionSubgroup
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
    numberFieldTowerExtensionSubgroup_normal K L
  let _ : Finite _ :=
    (numberFieldTowerFiniteGaloisSubextension K L).finite
  letI : AddCommGroup
      (FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
    finiteNormQuotientAddCommGroup rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  exact
    @AddEquiv.trans
      (FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
      (Additive
        (Abelianization
          (ClassFormation.FiniteGaloisSubextension.extensionQuotient
            (numberFieldTowerFiniteGaloisSubextension K L))))
      (Additive (Abelianization (Gal(L / K))))
      inferInstance inferInstance inferInstance
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        (numberFieldTowerReciprocityFiniteAbstractField K L)
        (numberFieldTowerFiniteGaloisSubextension K L))
      (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
        K L)

/-- The actual global norm-residue equivalence for a finite Galois
number-field extension:

`C_K / N_{L/K} C_L ≃ Gal(L / K)ᵃᵇ`. -/
noncomputable def globalNormResidueAbelianizationEquiv :
    Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃+
      Additive (Abelianization (Gal(L / K))) := by
  exact
    (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
        K L).symm.trans
      (numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv K L)

private theorem
    numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv_apply
    (x :
      FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :
    letI :=
      (numberFieldTowerReciprocityFiniteAbstractField K L).finite
    letI :=
      numberFieldTowerExtensionSubgroup_normal K L
    letI :=
      (numberFieldTowerFiniteGaloisSubextension K L).finite
    numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv K L x =
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
        K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L) x) := by
  let hBaseFinite :=
    (numberFieldTowerReciprocityFiniteAbstractField K L).finite
  let hExtensionNormal :=
    numberFieldTowerExtensionSubgroup_normal K L
  let hRelativeFinite :=
    (numberFieldTowerFiniteGaloisSubextension K L).finite
  rfl

private theorem globalNormResidueAbelianizationEquiv_transport_apply
    (x :
      FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :
    globalNormResidueAbelianizationEquiv K L
        (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
          K L x) =
      numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv K L x := by
  simp only [globalNormResidueAbelianizationEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]

/-- The abelianized global norm-residue equivalence on a finite norm class. -/
theorem globalNormResidueAbelianizationEquiv_finiteNormClass
    (x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :
    letI := (numberFieldTowerReciprocityFiniteAbstractField K L).finite
    letI := numberFieldTowerExtensionSubgroup_normal K L
    letI := (numberFieldTowerFiniteGaloisSubextension K L).finite
    globalNormResidueAbelianizationEquiv K L
        (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
          K L x) =
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
        K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L) x) := by
  exact (globalNormResidueAbelianizationEquiv_transport_apply K L x).trans
    (numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv_apply K L x)

/-- On the genuine finite-reciprocity class of an abstract extension
automorphism, the finite-Galois norm-residue equivalence gives the class of
the corresponding actual automorphism in the Galois abelianization. -/
@[simp]
theorem globalNormResidueAbelianizationEquiv_finiteReciprocityHom
    (q :
      ClassFormation.FiniteGaloisSubextension.extensionQuotient
        (numberFieldTowerFiniteGaloisSubextension K L)) :
    letI :=
      (numberFieldTowerReciprocityFiniteAbstractField K L).finite
    letI :=
      numberFieldTowerExtensionSubgroup_normal K L
    letI :=
      (numberFieldTowerFiniteGaloisSubextension K L).finite
    globalNormResidueAbelianizationEquiv K L
        (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
          K L
          (rationalCyclotomicDegreeData.finiteReciprocityHom
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            (rationalCyclotomicIdeleClassValuationData.classFieldAxiom_implies_unramifiedUnitCohomology
                rationalIdeleClassRepresentation_satisfiesClassFieldAxiom)
            (numberFieldTowerReciprocityFiniteAbstractField K L)
            (numberFieldTowerFiniteGaloisSubextension K L).field
            (numberFieldTowerFiniteGaloisSubextension K L).below
            (hLnormal :=
              (numberFieldTowerFiniteGaloisSubextension K L).normal)
            (hLfinite :=
              (numberFieldTowerFiniteGaloisSubextension K L).finite)
            (Additive.ofMul q))) =
      Additive.ofMul
        (Abelianization.of
          (numberFieldTowerExtensionQuotientEquivGaloisGroup K L q)) := by
  let hBaseFinite :=
    (numberFieldTowerReciprocityFiniteAbstractField K L).finite
  let hExtensionNormal :=
    numberFieldTowerExtensionSubgroup_normal K L
  let hRelativeFinite :=
    (numberFieldTowerFiniteGaloisSubextension K L).finite
  let x :=
    rationalCyclotomicDegreeData.finiteReciprocityHom
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      (rationalCyclotomicIdeleClassValuationData.classFieldAxiom_implies_unramifiedUnitCohomology
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom)
      (numberFieldTowerReciprocityFiniteAbstractField K L)
      (numberFieldTowerFiniteGaloisSubextension K L).field
      (numberFieldTowerFiniteGaloisSubextension K L).below
      (hLnormal :=
        (numberFieldTowerFiniteGaloisSubextension K L).normal)
      (hLfinite :=
        (numberFieldTowerFiniteGaloisSubextension K L).finite)
      (Additive.ofMul q)
  have hxNorm :
      rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L) x =
        Additive.ofMul (Abelianization.of q) :=
    rationalCyclotomicDegreeData.normResidueSymbol_finiteReciprocityHom
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      (numberFieldTowerReciprocityFiniteAbstractField K L)
      (numberFieldTowerFiniteGaloisSubextension K L) q
  exact
    (globalNormResidueAbelianizationEquiv_transport_apply K L x).trans
      ((numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv_apply
          K L x).trans
        ((congrArg
            (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
              K L)
            hxNorm).trans
          (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization_of
            K L q)))

/-- The inverse global reciprocity equivalence for an arbitrary finite Galois
extension. -/
noncomputable def globalReciprocityAbelianizationEquiv :
    Additive (Abelianization (Gal(L / K))) ≃+
      Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) :=
  (globalNormResidueAbelianizationEquiv K L).symm

/-- The genuine global norm-residue homomorphism with target the
abelianization of the actual Galois group. -/
noncomputable def globalNormResidueAbelianizationMonoidHom :
    IdeleClassGroup K →*
      Abelianization (Gal(L / K)) := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Abelianization (Gal(L / K)) :=
    AddEquiv.toMultiplicative
      (globalNormResidueAbelianizationEquiv K L)
  exact
    e.toMonoidHom.comp
      (QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range)

/-- Evaluation of the finite-Galois global norm-residue homomorphism is the
global equivalence applied to the genuine norm quotient class. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHom_apply
    (c : IdeleClassGroup K) :
    globalNormResidueAbelianizationMonoidHom K L c =
      Additive.toMul
        (globalNormResidueAbelianizationEquiv K L
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm K L).range c))) :=
  rfl

/-- Evaluate the finite-Galois symbol on the norm class of an idèle class. -/
theorem globalNormResidueAbelianizationMonoidHom_finiteNormClass
    (c : IdeleClassGroup K) :
    letI := (numberFieldTowerReciprocityFiniteAbstractField K L).finite
    letI := numberFieldTowerExtensionSubgroup_normal K L
    letI := (numberFieldTowerFiniteGaloisSubextension K L).finite
    globalNormResidueAbelianizationMonoidHom K L c =
      Additive.toMul
        (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
          K L
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldTowerReciprocityFiniteAbstractField K L)
            (numberFieldTowerFiniteGaloisSubextension K L)
            (finiteNormClass rationalIdeleClassRepresentation
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
              (numberFieldTowerIdeleClassEquivAmbientFixed K L
                (Additive.ofMul c))))) := by
  let x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L) :=
    finiteNormClass rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
      (numberFieldTowerIdeleClassEquivAmbientFixed K L (Additive.ofMul c))
  have hclass :=
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L c
  calc
    _ = Additive.toMul
        (globalNormResidueAbelianizationEquiv K L
          (Additive.ofMul
            (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c))) :=
      globalNormResidueAbelianizationMonoidHom_apply K L c
    _ = Additive.toMul
        (globalNormResidueAbelianizationEquiv K L
          (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
            K L x)) :=
      congrArg (fun q => Additive.toMul
        (globalNormResidueAbelianizationEquiv K L q)) hclass.symm
    _ = _ := congrArg Additive.toMul
      (globalNormResidueAbelianizationEquiv_finiteNormClass K L x)

/-- An idele class has trivial finite-Galois norm-residue symbol exactly when
it is an actual idele-class norm from `L`. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHom_eq_one_iff
    (c : IdeleClassGroup K) :
    globalNormResidueAbelianizationMonoidHom K L c = 1 ↔
      c ∈ (_root_.ideleClassNorm K L).range := by
  let e :=
    AddEquiv.toMultiplicative
      (globalNormResidueAbelianizationEquiv K L)
  change
    e (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c) =
        1 ↔
      c ∈ (_root_.ideleClassNorm K L).range
  constructor
  · intro h
    have hq :
        QuotientGroup.mk'
            (_root_.ideleClassNorm K L).range c =
          1 := by
      apply
        e.injective
      exact h.trans (map_one e).symm
    exact (QuotientGroup.eq_one_iff c).1 hq
  · intro hc
    have hq :
        QuotientGroup.mk'
            (_root_.ideleClassNorm K L).range c =
          1 :=
      (QuotientGroup.eq_one_iff c).2 hc
    exact
      (congrArg e hq).trans
        (map_one e)

/-- The finite-Galois global norm-residue homomorphism is surjective onto the
actual Galois abelianization. -/
theorem globalNormResidueAbelianizationMonoidHom_surjective :
    Function.Surjective
      (globalNormResidueAbelianizationMonoidHom K L) := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Abelianization (Gal(L / K)) :=
    AddEquiv.toMultiplicative
      (globalNormResidueAbelianizationEquiv K L)
  intro y
  obtain ⟨q, hq⟩ := e.surjective y
  obtain ⟨c, hc⟩ :=
    QuotientGroup.mk'_surjective
      (_root_.ideleClassNorm K L).range q
  refine ⟨c, ?_⟩
  calc
    globalNormResidueAbelianizationMonoidHom K L c =
        Additive.toMul
          (globalNormResidueAbelianizationEquiv K L
            (Additive.ofMul
              (QuotientGroup.mk'
                (_root_.ideleClassNorm K L).range c))) :=
      globalNormResidueAbelianizationMonoidHom_apply K L c
    _ = e q := congrArg e hc
    _ = y := hq

/-- The finite-Galois global norm-residue symbol viewed on the idele group.

This is the genuine idele-class symbol pulled back along
`I_K → C_K`; in particular it is not a separately chosen map. -/
noncomputable def globalNormResidueAbelianizationIdeleMonoidHom :
    IdeleGroup K →*
      Abelianization (Gal(L / K)) :=
  (globalNormResidueAbelianizationMonoidHom K L).comp
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K))

/-- Evaluation of the finite-Galois norm-residue symbol on an idele is
evaluation of the class symbol on its genuine idele class. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_apply
    (a : IdeleGroup K) :
    globalNormResidueAbelianizationIdeleMonoidHom K L a =
      globalNormResidueAbelianizationMonoidHom K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) :=
  rfl

/-- The finite-Galois norm-residue symbol on ideles is trivial on every
principal idele. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_principalIdele
    (x : Kˣ) :
    globalNormResidueAbelianizationIdeleMonoidHom K L
        (IdeleGroup.principalIdele K x) =
      1 := by
  have hclass :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (IdeleGroup.principalIdele K x) =
        1 :=
    (QuotientGroup.eq_one_iff
      (IdeleGroup.principalIdele K x)).2
      ⟨x, rfl⟩
  calc
    globalNormResidueAbelianizationIdeleMonoidHom K L
          (IdeleGroup.principalIdele K x) =
        globalNormResidueAbelianizationMonoidHom K L
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (IdeleGroup.principalIdele K x)) :=
      globalNormResidueAbelianizationIdeleMonoidHom_apply K L _
    _ = globalNormResidueAbelianizationMonoidHom K L 1 :=
      congrArg
        (globalNormResidueAbelianizationMonoidHom K L)
        hclass
    _ = 1 := map_one _

/-- The finite-Galois norm-residue symbol remains surjective when viewed
on ideles. -/
theorem globalNormResidueAbelianizationIdeleMonoidHom_surjective :
    Function.Surjective
      (globalNormResidueAbelianizationIdeleMonoidHom K L) :=
  (globalNormResidueAbelianizationMonoidHom_surjective K L).comp
    (QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup K))

/-- An idele has trivial finite-Galois norm-residue symbol exactly when
its idele class is an actual norm from `L`. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff
    (a : IdeleGroup K) :
    globalNormResidueAbelianizationIdeleMonoidHom K L a = 1 ↔
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a ∈
        (_root_.ideleClassNorm K L).range := by
  simpa only [
    globalNormResidueAbelianizationIdeleMonoidHom_apply] using
      globalNormResidueAbelianizationMonoidHom_eq_one_iff K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a)

/-- The kernel of the idele-level finite-Galois norm-residue symbol is the
full inverse image of the genuine idele-class norm range. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_ker :
    (globalNormResidueAbelianizationIdeleMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range.comap
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)) := by
  ext a
  change
    globalNormResidueAbelianizationIdeleMonoidHom K L a = 1 ↔
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a ∈
        (_root_.ideleClassNorm K L).range
  exact
    globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff
      K L a

/-- The kernel of the finite-Galois norm-residue homomorphism is exactly the
range of the ordinary idele-class norm. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHom_ker :
    (globalNormResidueAbelianizationMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range := by
  ext c
  change
    globalNormResidueAbelianizationMonoidHom K L c = 1 ↔
      c ∈ (_root_.ideleClassNorm K L).range
  exact
    globalNormResidueAbelianizationMonoidHom_eq_one_iff
      K L c

/-- The index of the actual norm subgroup is the order of the
abelianization of the genuine finite Galois group. -/
theorem ideleClassNorm_index_eq_galoisAbelianization_card :
    (_root_.ideleClassNorm K L).range.index =
      Nat.card (Abelianization (Gal(L / K))) := by
  calc
    (_root_.ideleClassNorm K L).range.index =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) :=
      Subgroup.index_eq_card
        ((_root_.ideleClassNorm K L).range)
    _ =
        Nat.card
          (Additive
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range)) :=
      (Nat.card_congr Additive.toMul).symm
    _ =
        Nat.card
          (Additive
            (Abelianization (Gal(L / K)))) :=
      Nat.card_congr
        (globalNormResidueAbelianizationEquiv K L).toEquiv
    _ =
        Nat.card
          (Abelianization (Gal(L / K))) :=
      Nat.card_congr Additive.toMul

section AbelianSpecialization

variable
    (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]

private theorem
    globalNormResidueAbelianizationEquiv_abelianSpecialization_apply
    (q :
      Additive
        (IdeleClassGroup F ⧸
          (_root_.ideleClassNorm F E).range)) :
    MulEquiv.toAdditive
          (Abelianization.equivOfComm :
            Gal(E / F) ≃*
              Abelianization (Gal(E / F))).symm
        (globalNormResidueAbelianizationEquiv F E q) =
      globalNormResidueEquiv F E q := by
  let H :=
    numberFieldTowerReciprocityFiniteAbstractField F E
  let T :=
    numberFieldTowerFiniteGaloisSubextension F E
  let hBaseFinite := H.finite
  let hExtensionNormal :=
    numberFieldTowerExtensionSubgroup_normal F E
  let hRelativeFinite := T.finite
  let hUnramified :=
    rationalCyclotomicIdeleClassValuationData.classFieldAxiom_implies_unramifiedUnitCohomology
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
  let r :=
    rationalCyclotomicDegreeData.finiteReciprocityHom
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      hUnramified H T.field T.below
      (hLnormal := T.normal)
      (hLfinite := T.finite)
  let n :=
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient F E
  let canonical :
      Gal(E / F) ≃*
        Abelianization (Gal(E / F)) :=
    Abelianization.equivOfComm
  have hr : Function.Surjective r :=
    rationalCyclotomicIdeleClassValuationData.abstractReciprocity_finiteReciprocityHom_surjective
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      hUnramified H T
  obtain ⟨x, rfl⟩ := n.surjective q
  obtain ⟨t, rfl⟩ := hr x
  have hAbelianized :=
    globalNormResidueAbelianizationEquiv_finiteReciprocityHom
      F E (Additive.toMul t)
  have hOrdinary :=
    globalNormResidueEquiv_finiteReciprocityHom
      F E (Additive.toMul t)
  calc
    MulEquiv.toAdditive canonical.symm
          (globalNormResidueAbelianizationEquiv F E (n (r t))) =
        MulEquiv.toAdditive canonical.symm
          (Additive.ofMul
            (Abelianization.of
              (numberFieldTowerExtensionQuotientEquivGaloisGroup
                F E (Additive.toMul t)))) :=
      congrArg (MulEquiv.toAdditive canonical.symm) hAbelianized
    _ =
        Additive.ofMul
          (numberFieldTowerExtensionQuotientEquivGaloisGroup
            F E (Additive.toMul t)) :=
      congrArg Additive.ofMul
        (canonical.symm_apply_apply
          (numberFieldTowerExtensionQuotientEquivGaloisGroup
            F E (Additive.toMul t)))
    _ = globalNormResidueEquiv F E (n (r t)) :=
      hOrdinary.symm

/-- For an abelian extension, composing the finite-Galois equivalence with
the canonical equivalence from the Galois abelianization recovers the usual
global norm-residue equivalence. -/
theorem globalNormResidueAbelianizationEquiv_abelianSpecialization :
    (globalNormResidueAbelianizationEquiv F E).trans
        (MulEquiv.toAdditive
          (Abelianization.equivOfComm :
            Gal(E / F) ≃*
              Abelianization (Gal(E / F))).symm) =
      globalNormResidueEquiv F E := by
  apply AddEquiv.ext
  intro q
  exact
    globalNormResidueAbelianizationEquiv_abelianSpecialization_apply
      F E q

/-- In the canonical direction used by the global reciprocity isomorphism,
the finite-Galois construction likewise specializes to the ordinary
abelian reciprocity equivalence. -/
theorem globalReciprocityAbelianizationEquiv_abelianSpecialization :
    (MulEquiv.toAdditive
        (Abelianization.equivOfComm :
          Gal(E / F) ≃*
            Abelianization (Gal(E / F)))).trans
      (globalReciprocityAbelianizationEquiv F E) =
        globalReciprocityEquiv F E := by
  change
    ((globalNormResidueAbelianizationEquiv F E).trans
      (MulEquiv.toAdditive
        (Abelianization.equivOfComm :
          Gal(E / F) ≃*
            Abelianization (Gal(E / F))).symm)).symm =
      (globalNormResidueEquiv F E).symm
  exact
    congrArg AddEquiv.symm
      (globalNormResidueAbelianizationEquiv_abelianSpecialization F E)

private theorem
    globalNormResidueAbelianizationMonoidHom_abelianSpecialization_apply
    (c : IdeleClassGroup F) :
    (Abelianization.equivOfComm :
        Gal(E / F) ≃*
          Abelianization (Gal(E / F))).symm
        (globalNormResidueAbelianizationMonoidHom F E c) =
      globalNormResidueMonoidHom F E c := by
  simpa only [
    globalNormResidueAbelianizationMonoidHom_apply,
    globalNormResidueMonoidHom_apply,
    MulEquiv.toAdditive_apply_apply,
    MonoidHom.toAdditive_apply_apply,
    MulEquiv.coe_toMonoidHom,
    toMul_ofMul] using
      congrArg Additive.toMul
        (globalNormResidueAbelianizationEquiv_abelianSpecialization_apply
          F E
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm F E).range c)))

/-- The finite-Galois norm-residue homomorphism specializes to the ordinary
abelian global Artin homomorphism after the canonical target
identification. -/
theorem
    globalNormResidueAbelianizationMonoidHom_abelianSpecialization :
    (Abelianization.equivOfComm :
        Gal(E / F) ≃*
          Abelianization (Gal(E / F))).symm.toMonoidHom.comp
        (globalNormResidueAbelianizationMonoidHom F E) =
      globalNormResidueMonoidHom F E := by
  apply MonoidHom.ext
  intro c
  exact
    globalNormResidueAbelianizationMonoidHom_abelianSpecialization_apply
      F E c

/-- The idele-level finite-Galois symbol has the same abelian
specialization, after pulling both class symbols back along
`I_F → C_F`. -/
theorem
    globalNormResidueAbelianizationIdeleMonoidHom_abelianSpecialization :
    (Abelianization.equivOfComm :
        Gal(E / F) ≃*
          Abelianization (Gal(E / F))).symm.toMonoidHom.comp
        (globalNormResidueAbelianizationIdeleMonoidHom F E) =
      (globalNormResidueMonoidHom F E).comp
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup F)) := by
  apply MonoidHom.ext
  intro a
  simpa only [
    MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,
    globalNormResidueAbelianizationIdeleMonoidHom_apply] using
      globalNormResidueAbelianizationMonoidHom_abelianSpecialization_apply
        F E
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup F) a)

end AbelianSpecialization

end Reciprocity
end GlobalClassFieldTheory
