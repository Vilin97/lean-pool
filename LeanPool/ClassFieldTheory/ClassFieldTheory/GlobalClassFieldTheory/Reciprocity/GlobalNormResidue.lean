/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.MaximalUnramifiedReciprocity
/-!
# The global norm-residue symbol

For a finite abelian Galois extension `L / K`, the rational absolute
idele-class formation realizes the abstract finite norm quotient as the
actual quotient

`C_K / N_{L/K} C_L`.

The concrete cyclotomic valuation supplies the valuation data required
by abstract reciprocity.  Composing the inverse of the fixed-field
comparison, the abstract norm-residue symbol, and the compatible
Galois-group comparison gives the actual equivalence

`C_K / N_{L/K} C_L ≃ Gal(L / K)`.

The homomorphism on `C_K` is obtained from the genuine quotient map.
Consequently it is surjective and its kernel is exactly the range of
the actual ordinary idele-class norm.
-/

@[expose] public section

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

/-- Fix the canonical class-group dictionary before forming norm quotients. -/
@[instance_reducible]
private noncomputable def globalNormResidueIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] globalNormResidueIdeleClassCommGroup

private theorem globalNormResidueIdeleClassIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] globalNormResidueIdeleClassIsMulCommutative

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- A reducible presentation of the compatible finite abstract field.
Its field projection is definitionally the concrete tower subgroup, so
dependent norm-quotient types do not require opaque unfolding. -/
noncomputable abbrev numberFieldTowerReciprocityFiniteAbstractField :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  field := numberFieldTowerBaseSubgroup K L
  finite := numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L

/-- The abelianization of the compatible abstract extension quotient
is the actual abelian Galois group of `L / K`. -/
noncomputable def
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup :
    Additive
        (Abelianization
          (ClassFormation.FiniteGaloisSubextension.extensionQuotient
            (numberFieldTowerFiniteGaloisSubextension K L))) ≃+
      Additive (Gal(L/K)) :=
  MulEquiv.toAdditive
    (MulEquiv.trans
      (MulEquiv.abelianizationCongr
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L))
        (Abelianization.equivOfComm :
          Gal(L/K) ≃*
            Abelianization (Gal(L/K))).symm)

/-- The compatible abelianized extension-quotient comparison sends the
class of an abstract automorphism to the corresponding actual
automorphism of `L / K`. -/
@[simp]
theorem
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup_of
    (q :
      ClassFormation.FiniteGaloisSubextension.extensionQuotient
        (numberFieldTowerFiniteGaloisSubextension K L)) :
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L q) := by
  apply Additive.toMul.injective
  change
    (Abelianization.equivOfComm :
        Gal(L/K) ≃*
          Abelianization (Gal(L/K))).symm
        (MulEquiv.abelianizationCongr
          (numberFieldTowerExtensionQuotientEquivGaloisGroup K L)
          (Abelianization.of q)) =
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L q
  rw [abelianizationCongr_of]
  exact
    (Abelianization.equivOfComm :
      Gal(L/K) ≃*
        Abelianization (Gal(L/K))).symm_apply_apply _

/-- The abstract norm-residue map followed by the compatible actual
Galois-group comparison.  Keeping this composition behind a typed boundary
prevents the finite norm quotient from being reconstructed while composing
with the concrete quotient comparison. -/
private noncomputable def
    numberFieldTowerAbstractNormResidueGaloisEquiv :
    FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L) ≃+
      Additive (Gal(L/K)) := by
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
      (Additive (Gal(L/K)))
      inferInstance inferInstance inferInstance
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        (numberFieldTowerReciprocityFiniteAbstractField K L)
        (numberFieldTowerFiniteGaloisSubextension K L))
      (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L)

/-- Evaluation of the typed abstract norm-residue/Galois comparison. -/
private theorem numberFieldTowerAbstractNormResidueGaloisEquiv_apply
    (x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :
    numberFieldTowerAbstractNormResidueGaloisEquiv K L x =
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L) x) := by
  rfl

/-- The actual global norm-residue equivalence

`C_K / N_{L/K} C_L ≃ Gal(L / K)`.

Its three factors are respectively the actual fixed-field norm
comparison, the abstract norm-residue symbol built from the concrete
cyclotomic valuation, and the compatible Galois-group comparison. -/
noncomputable def globalNormResidueEquiv :
    Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃+
      Additive (Gal(L/K)) := by
  exact
    (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
        K L).symm.trans
      (numberFieldTowerAbstractNormResidueGaloisEquiv K L)

/-- Evaluation after transporting an abstract finite norm class to the
ordinary idele-class norm quotient. -/
private theorem globalNormResidueEquiv_transport_apply
    (x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :
    globalNormResidueEquiv K L
        (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
          K L x) =
      numberFieldTowerAbstractNormResidueGaloisEquiv K L x := by
  simp only [globalNormResidueEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]

/-- The global norm-residue equivalence on a finite abstract norm class,
after transport to the ordinary idele-class norm quotient. -/
theorem globalNormResidueEquiv_finiteNormClass
    (x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :
    globalNormResidueEquiv K L
        (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
          K L x) =
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L) x) :=
  (globalNormResidueEquiv_transport_apply K L x).trans
    (numberFieldTowerAbstractNormResidueGaloisEquiv_apply K L x)

/-- On the genuine finite-reciprocity class of an abstract extension
automorphism, the global norm-residue equivalence is the corresponding
actual automorphism of `L / K`. -/
@[simp]
theorem globalNormResidueEquiv_finiteReciprocityHom
    (q :
      ClassFormation.FiniteGaloisSubextension.extensionQuotient
        (numberFieldTowerFiniteGaloisSubextension K L)) :
    globalNormResidueEquiv K L
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
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L q) := by
  let x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L) :=
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
  change
    globalNormResidueEquiv K L
        (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
          K L x) =
      Additive.ofMul
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L q)
  calc
    _ = numberFieldTowerAbstractNormResidueGaloisEquiv K L x :=
      globalNormResidueEquiv_transport_apply K L x
    _ =
        numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldTowerReciprocityFiniteAbstractField K L)
            (numberFieldTowerFiniteGaloisSubextension K L)
            x) :=
      numberFieldTowerAbstractNormResidueGaloisEquiv_apply K L x
    _ =
        numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
          (Additive.ofMul (Abelianization.of q)) :=
      congrArg
        (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L)
        (rationalCyclotomicDegreeData.normResidueSymbol_finiteReciprocityHom
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L) q)
    _ = _ :=
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup_of K L q

/-- The inverse global reciprocity equivalence

`Gal(L / K) ≃ C_K / N_{L/K} C_L`. -/
noncomputable def globalReciprocityEquiv :
    Additive (Gal(L/K)) ≃+
      Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) :=
  (globalNormResidueEquiv K L).symm

/-- The actual global norm-residue homomorphism on the idele class
group, obtained by composing the genuine quotient map with the global
norm-residue equivalence. -/
noncomputable def globalNormResidueMonoidHom :
    IdeleClassGroup K →* Gal(L/K) := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Gal(L/K) :=
    AddEquiv.toMultiplicative (globalNormResidueEquiv K L)
  exact
    e.toMonoidHom.comp
      (QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range)

/-- Evaluation of the actual global norm-residue homomorphism is the
global norm-residue equivalence applied to the genuine norm quotient
class. -/
@[simp]
theorem globalNormResidueMonoidHom_apply
    (c : IdeleClassGroup K) :
    globalNormResidueMonoidHom K L c =
      Additive.toMul
        (globalNormResidueEquiv K L
          (Additive.ofMul
            (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c))) :=
  rfl

open ClassFormation.ValuationData renaming
  normResidueSymbol_finiteNormClass_eq_maximalUnramifiedRestriction →
    normResidueSymbol_finiteNormClass_eq_maximalUnramifiedRestriction in
/-- For a finite extension whose compatible abstract realization is
unramified for the cyclotomic degree datum, the actual global
norm-residue symbol is the finite restriction of the
maximal-unramified valuation symbol. -/
theorem globalNormResidueMonoidHom_eq_maximalUnramifiedRestriction
    (hUnramified :
      (numberFieldTowerFiniteGaloisSubextension K L).IsUnramified
        rationalCyclotomicDegreeData)
    (c : IdeleClassGroup K) :
    globalNormResidueMonoidHom K L c =
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
        (DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField
            (numberFieldTowerReciprocityFiniteAbstractField K L)
            rationalCyclotomicDegreeData)
          (numberFieldTowerFiniteGaloisSubextension K L)
          hUnramified
          (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData
            (numberFieldTowerReciprocityFiniteAbstractField K L)
            (numberFieldTowerIdeleClassEquivAmbientFixed K L
              (Additive.ofMul c))).toMul) := by
  let H :=
    numberFieldTowerReciprocityFiniteAbstractField K L
  let E :=
    numberFieldTowerFiniteGaloisSubextension K L
  let a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L) :=
    numberFieldTowerIdeleClassEquivAmbientFixed K L
      (Additive.ofMul c)
  let x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L) :=
    finiteNormClass rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L) a
  let q : E.extensionQuotient :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField
        H rationalCyclotomicDegreeData)
      E hUnramified
      (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
        rationalCyclotomicIdeleClassValuationData H a).toMul
  have hclass :=
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L c
  rw [globalNormResidueMonoidHom_apply, ← hclass]
  calc
    _ = Additive.toMul
        (numberFieldTowerAbstractNormResidueGaloisEquiv K L x) :=
      congrArg Additive.toMul
        (globalNormResidueEquiv_transport_apply K L x)
    _ = Additive.toMul
        (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            H E x)) :=
      congrArg Additive.toMul
        (numberFieldTowerAbstractNormResidueGaloisEquiv_apply K L x)
    _ =
        Additive.toMul
          (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
            (Additive.ofMul (Abelianization.of q))) :=
      congrArg
        (fun z =>
          Additive.toMul
            (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup
              K L z))
        (normResidueSymbol_finiteNormClass_eq_maximalUnramifiedRestriction
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          H E hUnramified a)
    _ = _ := by
      rw [numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup_of]
      exact toMul_ofMul _

/-- An idele class has trivial global norm-residue symbol exactly when
it is an actual idele-class norm from `L`. -/
theorem globalNormResidueMonoidHom_eq_one_iff
    (c : IdeleClassGroup K) :
    globalNormResidueMonoidHom K L c = 1 ↔
      c ∈ (_root_.ideleClassNorm K L).range := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Gal(L/K) :=
    AddEquiv.toMultiplicative (globalNormResidueEquiv K L)
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
      apply e.injective
      exact h.trans (map_one e).symm
    exact (QuotientGroup.eq_one_iff c).1 hq
  · intro hc
    have hq :
        QuotientGroup.mk'
            (_root_.ideleClassNorm K L).range c =
          1 :=
      (QuotientGroup.eq_one_iff c).2 hc
    calc
      e (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c) = e 1 :=
        congrArg e hq
      _ = 1 := map_one e

/-- The actual global norm-residue homomorphism is surjective. -/
theorem globalNormResidueMonoidHom_surjective :
    Function.Surjective
      (globalNormResidueMonoidHom K L) := by
  change
    Function.Surjective
      ((AddEquiv.toMultiplicative
          (globalNormResidueEquiv K L)).toMonoidHom.comp
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range))
  exact
    (AddEquiv.toMultiplicative
        (globalNormResidueEquiv K L)).surjective.comp
      (QuotientGroup.mk'_surjective
        (_root_.ideleClassNorm K L).range)

/-- The index of the actual idele-class norm subgroup of a finite
abelian extension is its field degree. -/
theorem ideleClassNorm_index_eq_finrank_abelian :
    (_root_.ideleClassNorm K L).range.index =
      Module.finrank K L := by
  rw [Subgroup.index_eq_card]
  calc
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) =
        Nat.card
          (Additive
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range)) :=
      (Nat.card_congr Additive.toMul).symm
    _ = Nat.card (Additive (Gal(L/K))) :=
      Nat.card_congr (globalNormResidueEquiv K L).toEquiv
    _ = Nat.card (Gal(L/K)) :=
      Nat.card_congr Additive.toMul
    _ = Module.finrank K L :=
      IsGalois.card_aut_eq_finrank K L

/-- The kernel of the actual global norm-residue homomorphism is
exactly the range of the ordinary idele-class norm. -/
@[simp]
theorem globalNormResidueMonoidHom_ker :
    (globalNormResidueMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range := by
  ext c
  change
    globalNormResidueMonoidHom K L c = 1 ↔
      c ∈ (_root_.ideleClassNorm K L).range
  exact globalNormResidueMonoidHom_eq_one_iff K L c

end Reciprocity
end GlobalClassFieldTheory
