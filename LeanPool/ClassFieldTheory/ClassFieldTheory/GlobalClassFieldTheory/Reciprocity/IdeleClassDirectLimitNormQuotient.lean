/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtensionNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient
/-!
# Finite norm quotients for rational fixed fields

The abstract finite norm subgroup and quotient are identified with the
ordinary idele-class norm range and quotient of the actual fixed-field extension.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

local instance
    rationalNormQuotientIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance
    rationalNormQuotientIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative

@[instance_reducible]
private noncomputable def rationalNormQuotientIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  open scoped IsMulCommutative in
    inferInstance

private theorem rationalNormQuotientNumberFieldOfFiniteDimensional
    (F : Type*) [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] :
    NumberField F :=
  NumberField.of_module_finite ℚ F

private theorem rationalNormQuotientAbstractFixedFieldNumberField
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K) := by
  let _ : FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K) :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  exact
    NumberField.of_module_finite ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)

private theorem rationalNormQuotientAbstractRelativeFixedFieldNumberField
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  exact NumberField.of_module_finite ℚ E

private theorem addEquiv_trans_symm_trans_symm_trans_apply_eq
    {V A B C D : Type*}
    [Add V] [Add A] [Add B] [Add C] [Add D]
    (eV : V ≃+ D) (eB : B ≃+ D)
    (eA : A ≃+ B) (eC : A ≃+ C)
    {y : V} {z : A} {w : C}
    (h : eV y = eB (eA z))
    (ht : eC z = w) :
    (((eV.trans eB.symm).trans eA.symm).trans eC) y = w := by
  change eC (eA.symm (eB.symm (eV y))) = w
  rw [h, eB.symm_apply_apply, eA.symm_apply_apply]
  exact ht

private theorem rationalTowerRelativeClass_baseChange
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    [IsScalarTower ℚ F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E]
    (c : Additive (IdeleClassGroup E)) :
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := E)
        (towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ F E).symm
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)).symm (Additive.toMul c)))) =
      Additive.toMul c := by
  let dQ : RelativeIdeleGroup.ClassGroup ℚ E :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E)).symm (Additive.toMul c)
  have hTower :=
    relativeIdeleClassBaseChangeMulEquiv_tower ℚ F E dQ
  have hBase :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E)).apply_symm_apply (Additive.toMul c)
  exact Eq.trans hTower hBase

private theorem rationalTowerRelativeClass_norm
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    [IsScalarTower ℚ F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E]

    (c : Additive (IdeleClassGroup E)) :
    let dF :=
      towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
        ((TowerRelativeIdeleGroup.classGroupEquiv
          ℚ F E).symm
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E)).symm (Additive.toMul c)))
    RelativeIdeleGroup.Cohomology.ideleClassNorm F E dF =
      _root_.ideleClassNorm F E (Additive.toMul c) := by
  let dF :=
    towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
      ((TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm
        ((_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)).symm (Additive.toMul c)))
  have hbase := rationalTowerRelativeClass_baseChange F E c
  change
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := E) dF = Additive.toMul c at hbase
  exact
    (ordinaryIdeleClassNorm_relativeIdeleClassBaseChange dF).symm.trans
      (congrArg (_root_.ideleClassNorm F E) hbase)

private noncomputable abbrev rationalRelativeFixedFieldIdeleClassAdditiveType
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField E :=
    NumberField.of_module_finite ℚ E
  Additive (IdeleClassGroup E)

private noncomputable abbrev rationalOrdinaryNormQuotientAdditiveType
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI :=
    rationalNormQuotientNumberFieldOfFiniteDimensional F
  letI :=
    rationalNormQuotientNumberFieldOfFiniteDimensional E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  Additive
    (IdeleClassGroup F ⧸ (_root_.ideleClassNorm F E).range)

@[instance_reducible] private noncomputable instance
    rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    AddCommGroup
      (rationalOrdinaryNormQuotientAdditiveType
        K L hLK hnormal) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI : NumberField F :=
    rationalNormQuotientNumberFieldOfFiniteDimensional F
  letI : NumberField E :=
    rationalNormQuotientNumberFieldOfFiniteDimensional E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  letI : CommGroup (IdeleClassGroup F) :=
    rationalNormQuotientIdeleClassCommGroup F
  change
    AddCommGroup
      (Additive
        (IdeleClassGroup F ⧸ (_root_.ideleClassNorm F E).range))
  infer_instance

private def quotientAddEquivOfEquivMapEq
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (S : AddSubgroup A) (T : AddSubgroup B)
    (e : B ≃+ A)
    (hmap : S.map e.symm.toAddMonoidHom = T) :
    (A ⧸ S) ≃+ (B ⧸ T) := by
  have hforward :
      S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hinverse :
      T ≤ AddSubgroup.comap e.toAddMonoidHom S := by
    intro y hy
    change e y ∈ S
    have hy' : y ∈ S.map e.symm.toAddMonoidHom := by
      rw [hmap]
      exact hy
    rcases hy' with ⟨x, hx, hxy⟩
    have heq : e y = x := by
      apply e.symm.injective
      simpa using hxy.symm
    rw [heq]
    exact hx
  let f : (A ⧸ S) →+ (B ⧸ T) :=
    QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
  let g : (B ⧸ T) →+ (A ⧸ S) :=
    QuotientAddGroup.map T S e.toAddMonoidHom hinverse
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change (↑(e (e.symm x)) : A ⧸ S) = ↑x
        rw [e.apply_symm_apply]
      right_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change (↑(e.symm (e x)) : B ⧸ T) = ↑x
        rw [e.symm_apply_apply]
      map_add' := f.map_add }

private theorem quotientAddEquivOfEquivMapEq_mk
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (S : AddSubgroup A) (T : AddSubgroup B)
    (e : B ≃+ A)
    (hmap : S.map e.symm.toAddMonoidHom = T)
    (x : A) :
    quotientAddEquivOfEquivMapEq S T e hmap
        (QuotientAddGroup.mk' S x) =
      QuotientAddGroup.mk' T (e.symm x) := by
  have hforward :
      S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro y hy
    change e.symm y ∈ T
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  change
    QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
        (QuotientAddGroup.mk' S x) =
      QuotientAddGroup.mk' T (e.symm x)
  rw [QuotientAddGroup.map_mk']
  rfl

private noncomputable def additiveQuotientEquiv
    {G : Type*} [CommGroup G] (H : Subgroup G) :
    (Additive G ⧸ H.toAddSubgroup) ≃+
      Additive (G ⧸ H) := by
  let normAdd : Additive G →+ Additive (G ⧸ H) :=
    MonoidHom.toAdditive (QuotientGroup.mk' H)
  let T := normAdd.ker
  have hT : H.toAddSubgroup = T := by
    ext g
    change
      Additive.toMul g ∈ H ↔
        QuotientGroup.mk' H (Additive.toMul g) = 1
    exact (QuotientGroup.eq_one_iff (Additive.toMul g)).symm
  have hmap :
      H.toAddSubgroup.map
          (AddEquiv.refl (Additive G)).symm.toAddMonoidHom = T := by
    change
      H.toAddSubgroup.map (AddMonoidHom.id (Additive G)) = T
    rw [AddSubgroup.map_id]
    exact hT
  let modelEquiv :
      (Additive G ⧸ H.toAddSubgroup) ≃+
        (Additive G ⧸ T) :=
    quotientAddEquivOfEquivMapEq
      H.toAddSubgroup T (AddEquiv.refl (Additive G)) hmap
  have hsurjective : Function.Surjective normAdd := by
    intro q
    obtain ⟨g, hg⟩ :=
      QuotientGroup.mk'_surjective H (Additive.toMul q)
    refine ⟨Additive.ofMul g, ?_⟩
    apply Additive.toMul.injective
    change QuotientGroup.mk' H g = Additive.toMul q
    exact hg
  exact modelEquiv.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      normAdd hsurjective)

private noncomputable def quotientAddEquivOfEquivMapEqToQuotient
    {A G : Type*} [AddCommGroup A] [CommGroup G]
    (S : AddSubgroup A) (N : Subgroup G) [N.Normal]
    (e : Additive G ≃+ A)
    (hmap : S.map e.symm.toAddMonoidHom = N.toAddSubgroup) :
    (A ⧸ S) ≃+ Additive (G ⧸ N) :=
  (quotientAddEquivOfEquivMapEq S N.toAddSubgroup e hmap).trans
    (additiveQuotientEquiv N)

private noncomputable def addEquivTransQuotientOfEquivMapEq
    {Q A G : Type*}
    [AddCommGroup Q] [AddCommGroup A] [CommGroup G]
    (S : AddSubgroup A) (N : Subgroup G) [N.Normal]
    (eConcrete : Q ≃+ (A ⧸ S)) (e : Additive G ≃+ A)
    (hmap : S.map e.symm.toAddMonoidHom = N.toAddSubgroup) :
    Q ≃+ Additive (G ⧸ N) :=
  eConcrete.trans
    (quotientAddEquivOfEquivMapEqToQuotient S N e hmap)

private theorem map_addRange_eq_monoidRange_toAddSubgroup_of_equiv
    {U A G H : Type*}
    [AddCommGroup U] [AddCommGroup A] [CommGroup G] [CommGroup H]
    (f : U →+ A) (g : G →* H)
    (eU : Additive G ≃+ U) (eA : Additive H ≃+ A)
    (hcompat : ∀ c : Additive G,
      eA.symm (f (eU c)) =
        Additive.ofMul (g (Additive.toMul c))) :
    f.range.map eA.symm.toAddMonoidHom = g.range.toAddSubgroup := by
  ext y
  constructor
  · intro hy
    obtain ⟨n, ⟨u, hu⟩, hny⟩ := hy
    let c : Additive G := eU.symm u
    refine ⟨Additive.toMul c, ?_⟩
    apply Additive.ofMul.injective
    exact
      (hcompat c).symm.trans
        ((congrArg (fun z => eA.symm (f z))
            (eU.apply_symm_apply u)).trans
          ((congrArg eA.symm hu).trans hny))
  · intro hy
    obtain ⟨d, hd⟩ := hy
    let c : Additive G := Additive.ofMul d
    let u : U := eU c
    exact
      ⟨f u, ⟨u, rfl⟩,
        (hcompat c).trans (congrArg Additive.ofMul hd)⟩

/-- The ordinary idele class group of the upper fixed field, identified
directly with the corresponding fixed part of the rational absolute
idele-class representation.  Unlike
`rationalAbstractExtensionIdeleClassEquiv`, this comparison does not
package a Galois action and therefore does not require normality. -/
noncomputable def
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    rationalRelativeFixedFieldIdeleClassAdditiveType
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField E :=
    NumberField.of_module_finite ℚ E
  change Additive (IdeleClassGroup E) ≃+
    KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L
  exact
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK

private noncomputable def rationalRelativeFixedFieldNormComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :
    (KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K) ×
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI : NumberField F :=
    rationalNormQuotientNumberFieldOfFiniteDimensional F
  letI : NumberField E :=
    rationalNormQuotientNumberFieldOfFiniteDimensional E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  (relativeNorm rationalIdeleClassRepresentation K L hLK
      (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed K L hLK c),
    rationalAbstractFixedFieldIdeleClassEquivFixed K
      (Additive.ofMul
        (_root_.ideleClassNorm F E (Additive.toMul c))))

private noncomputable def rationalRelativeFixedFieldNormPreimageComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  let dQ : RelativeIdeleGroup.ClassGroup ℚ E :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E)).symm
      (Additive.toMul c)
  let dF : RelativeIdeleGroup.ClassGroup F E := towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
    ((TowerRelativeIdeleGroup.classGroupEquiv ℚ F E).symm dQ)
  (rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
      ((extensionFixedRepresentationEquiv
        rationalIdeleClassRepresentation K L hLK hnormal).symm
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          K L hLK c)),
    Additive.ofMul dF)

private theorem rationalRelativeFixedFieldNormPreimageComparison_eq
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :
    (rationalRelativeFixedFieldNormPreimageComparison K L hLK hnormal c).1 =
    (rationalRelativeFixedFieldNormPreimageComparison K L hLK hnormal c).2 := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let eUpper := rationalAbstractRelativeFixedFieldIdeleClassEquivFixed K L hLK
  let dQ : RelativeIdeleGroup.ClassGroup ℚ E :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E)).symm
      (Additive.toMul c)
  let dF : RelativeIdeleGroup.ClassGroup F E :=
    towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
      ((TowerRelativeIdeleGroup.classGroupEquiv ℚ F E).symm dQ)
  let eAmbient := extensionFixedRepresentationEquiv
    rationalIdeleClassRepresentation K L hLK hnormal
  let eFixed : Additive (IdeleClassGroup E) ≃+
      KummerTheory.ambientFixedAddSubgroup rationalIdeleClassRepresentation L :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
  let eRelative :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (IdeleClassGroup E) :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E))
  let eTower :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (RelativeIdeleGroup.ClassGroup F E) :=
    MulEquiv.toAdditive ((TowerRelativeIdeleGroup.classGroupEquiv ℚ F E).symm.trans
      (towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E))
  change
    (((eAmbient.trans eFixed.symm).trans eRelative.symm).trans eTower)
        (eAmbient.symm (eUpper c)) =
      Additive.ofMul dF
  apply addEquiv_trans_symm_trans_symm_trans_apply_eq
      eAmbient eFixed eRelative eTower
      (z := Additive.ofMul dQ)
  · have hAmbient := eAmbient.apply_symm_apply (eUpper c)
    have heUpper : eUpper c = eFixed c := rfl
    have heRelative : eRelative (Additive.ofMul dQ) = c := by
      apply Additive.toMul.injective
      change
        _root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E) dQ =
          Additive.toMul c
      exact
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)).apply_symm_apply _
    exact hAmbient.trans (heUpper.trans (congrArg eFixed heRelative).symm)
  · rfl

private noncomputable def rationalRelativeFixedFieldNormCohomologyComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let eUpper :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed K L hLK
  let comparison :=
    rationalRelativeFixedFieldNormPreimageComparison
      K L hLK hnormal c
  ((rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
      (relativeNorm rationalIdeleClassRepresentation
        K L hLK (eUpper c)),
    Additive.ofMul
      (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
        (Additive.toMul comparison.2)))

private theorem rationalRelativeFixedFieldNormCohomologyComparison_eq
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :
    (rationalRelativeFixedFieldNormCohomologyComparison
      K L hLK hnormal c).1 =
      (rationalRelativeFixedFieldNormCohomologyComparison
        K L hLK hnormal c).2 := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let eUpper :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed K L hLK
  let comparison :=
    rationalRelativeFixedFieldNormPreimageComparison
      K L hLK hnormal c
  change
    (rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
        (relativeNorm rationalIdeleClassRepresentation
          K L hLK (eUpper c)) =
      Additive.ofMul
        (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
          (Additive.toMul comparison.2))
  have htransport : comparison.1 = comparison.2 :=
    rationalRelativeFixedFieldNormPreimageComparison_eq
      K L hLK hnormal c
  have hnorm :=
    rationalAbstractFixedFieldIdeleClassEquivFixed_relativeNorm
      K L hLK hnormal (eUpper c)
  change
    (rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
        (relativeNorm rationalIdeleClassRepresentation
          K L hLK (eUpper c)) =
      Additive.ofMul
        (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
          (Additive.toMul comparison.1))
    at hnorm
  rw [htransport] at hnorm
  exact hnorm

/-- For a finite Galois pair of abstract fixed fields, the direct upper
fixed-part comparison intertwines the class-formation relative norm with
the ordinary idele-class norm. -/
theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :
    let comparison := rationalRelativeFixedFieldNormComparison
      (hKfinite := hKfinite) (hfinite := hfinite) K L hLK hnormal c
    comparison.1 = comparison.2 := by
  let _ := hnormal
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let _ : NumberField F :=
    NumberField.of_module_finite ℚ F
  let _ : NumberField E :=
    NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  change
    relativeNorm rationalIdeleClassRepresentation K L hLK
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          K L hLK c) =
      rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul
          (_root_.ideleClassNorm F E (Additive.toMul c)))
  let eUpper :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
      K L hLK
  let comparison :=
    rationalRelativeFixedFieldNormPreimageComparison
      K L hLK hnormal c
  let dF : RelativeIdeleGroup.ClassGroup F E :=
    Additive.toMul comparison.2
  have hcohom :=
    rationalRelativeFixedFieldNormCohomologyComparison_eq
      K L hLK hnormal c
  change
    (rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
        (relativeNorm rationalIdeleClassRepresentation
          K L hLK (eUpper c)) =
      Additive.ofMul
        (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
          dF)
    at hcohom
  have hbridge := rationalTowerRelativeClass_norm F E c
  change
    RelativeIdeleGroup.Cohomology.ideleClassNorm F E dF =
      _root_.ideleClassNorm F E (Additive.toMul c) at hbridge
  calc
    relativeNorm rationalIdeleClassRepresentation K L hLK (eUpper c) =
        rationalAbstractFixedFieldIdeleClassEquivFixed K
          ((rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
            (relativeNorm rationalIdeleClassRepresentation
              K L hLK (eUpper c))) :=
      ((rationalAbstractFixedFieldIdeleClassEquivFixed K).apply_symm_apply _).symm
    _ = rationalAbstractFixedFieldIdeleClassEquivFixed K
          (Additive.ofMul
            (_root_.ideleClassNorm F E (Additive.toMul c))) :=
      congrArg (rationalAbstractFixedFieldIdeleClassEquivFixed K)
        (hcohom.trans (congrArg Additive.ofMul hbridge))

/-- The fixed-field comparison carries the abstract finite norm subgroup
exactly to the ordinary idele-class norm range of the actual fixed fields. -/
theorem
    map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    (finiteNormSubgroup rationalIdeleClassRepresentation K L hLK).map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          K).symm.toAddMonoidHom =
      (_root_.ideleClassNorm F E).range.toAddSubgroup := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let _ : CommGroup (IdeleClassGroup F) :=
    rationalNormQuotientIdeleClassCommGroup F
  let _ : CommGroup (IdeleClassGroup E) :=
    rationalNormQuotientIdeleClassCommGroup E
  let eK : Additive (IdeleClassGroup F) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      (hfinite := hKfinite) K
  let eUpper : Additive (IdeleClassGroup E) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
      (hKfinite := hKfinite) (hfinite := hfinite) K L hLK
  let f :
      KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation L →+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K :=
    relativeNorm rationalIdeleClassRepresentation K L hLK
  let g : IdeleClassGroup E →* IdeleClassGroup F :=
    _root_.ideleClassNorm F E
  change f.range.map eK.symm.toAddMonoidHom = g.range.toAddSubgroup
  refine map_addRange_eq_monoidRange_toAddSubgroup_of_equiv
    (U := KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L)
    (A := KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K)
    (G := IdeleClassGroup E) (H := IdeleClassGroup F)
    (f := f) (g := g) (eU := eUpper) (eA := eK) ?_
  intro c
  have hcompat :
      f (eUpper c) = eK (Additive.ofMul (g (Additive.toMul c))) := by
    exact
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm
        (hKfinite := hKfinite) (hfinite := hfinite) K L hLK hnormal c
  apply eK.injective
  exact Eq.trans (eK.apply_symm_apply (f (eUpper c))) hcompat

private noncomputable def rationalFiniteNormQuotientConcreteStep
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteNormQuotient rationalIdeleClassRepresentation K L hLK ≃+
      KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K ⧸
        finiteNormSubgroup rationalIdeleClassRepresentation K L hLK :=
  finiteNormQuotientConcreteEquiv
    rationalIdeleClassRepresentation K L hLK

/-- The finite norm quotient in the rational absolute representation is
the ordinary idele-class quotient by the actual norm subgroup of the
fixed-field extension. -/
noncomputable def
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteNormQuotient rationalIdeleClassRepresentation K L hLK ≃+
      rationalOrdinaryNormQuotientAdditiveType K L hLK hnormal := by
  letI : (extensionSubgroup K L hLK).Normal := hnormal
  letI : FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K) :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
    IsScalarTower.of_algebraMap_eq'
      (R := ℚ)
      (S := abstractFixedField ℚ (SeparableClosure ℚ) K)
      (A := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)
      (RingHom.ext_rat
        (algebraMap ℚ (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK))
        ((algebraMap
            (abstractFixedField ℚ (SeparableClosure ℚ) K)
            (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)).comp
          (algebraMap ℚ (abstractFixedField ℚ (SeparableClosure ℚ) K))))
  letI : NumberField (abstractFixedField ℚ (SeparableClosure ℚ) K) :=
    rationalNormQuotientAbstractFixedFieldNumberField
      (hKfinite := hKfinite) K
  letI : NumberField (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
    rationalNormQuotientAbstractRelativeFixedFieldNumberField
      (hKfinite := hKfinite) (hfinite := hfinite) K L hLK
  letI : IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  letI : CommGroup (IdeleClassGroup (abstractFixedField ℚ (SeparableClosure ℚ) K)) :=
    rationalNormQuotientIdeleClassCommGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
  letI : (_root_.ideleClassNorm
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)).range.Normal :=
    rationalNormQuotientIdeleClassSubgroupNormal
      (F := abstractFixedField ℚ (SeparableClosure ℚ) K)
      (_root_.ideleClassNorm
        (abstractFixedField ℚ (SeparableClosure ℚ) K)
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)).range
  change FiniteNormQuotient rationalIdeleClassRepresentation K L hLK ≃+
    Additive (IdeleClassGroup (abstractFixedField ℚ (SeparableClosure ℚ) K) ⧸
      (_root_.ideleClassNorm
        (abstractFixedField ℚ (SeparableClosure ℚ) K)
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)).range)
  exact addEquivTransQuotientOfEquivMapEq
    (Q := FiniteNormQuotient
      rationalIdeleClassRepresentation K L hLK)
    (A := KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K)
    (G := IdeleClassGroup (abstractFixedField ℚ (SeparableClosure ℚ) K))
    (S := finiteNormSubgroup rationalIdeleClassRepresentation K L hLK)
    (N := (_root_.ideleClassNorm
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)).range)
    (eConcrete := rationalFiniteNormQuotientConcreteStep
      (hfinite := hfinite) K L hLK)
    (e := rationalAbstractFixedFieldIdeleClassEquivFixed
      (hfinite := hKfinite) K)
    (hmap := map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
      (hKfinite := hKfinite) (hfinite := hfinite) K L hLK hnormal)

private noncomputable def rationalFiniteNormQuotientClassValue
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K) :
    rationalOrdinaryNormQuotientAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK hnormal :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  Additive.ofMul
    (QuotientGroup.mk' (_root_.ideleClassNorm F E).range
      (Additive.toMul
        ((rationalAbstractFixedFieldIdeleClassEquivFixed K).symm a)))

/-- The fixed-field norm-quotient comparison sends an abstract finite
norm class to the ordinary idele class of the transported
representative. -/
@[simp]
theorem
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K) :
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        K L hLK hnormal
        (finiteNormClass rationalIdeleClassRepresentation
          K L hLK a) =
      rationalFiniteNormQuotientClassValue
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  change
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        K L hLK hnormal
        (finiteNormClass rationalIdeleClassRepresentation
          K L hLK a) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm F E).range
          (Additive.toMul
            ((rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
              a)))
  simp only [
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient,
    rationalFiniteNormQuotientConcreteStep,
    addEquivTransQuotientOfEquivMapEq,
    quotientAddEquivOfEquivMapEqToQuotient]
  rfl

end Reciprocity
end GlobalClassFieldTheory
