/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.MaximalSubextension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.BasicInvariants
public import Mathlib.FieldTheory.SeparableClosure
/-!
# Finite-subextension sources for residue embeddings

For the maximal unramified subextension `T`, the maximal-residue theorem identifies the
residue field with the separable closure of the base residue field and the
value group with that of the base.  This file proves the two corresponding
statements for every finite unramified subextension used to form `T`.

Passing these statements through the whole supremum requires closure under
finite composita (stability under finite composita); that missing step is not inserted here as an
extra hypothesis.
-/

@[expose] public section

noncomputable
section

namespace AlgebraicNumberTheory
namespace Valuations

section FiniteUnramifiedSubextensionInvariants

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-- Inclusion of the valuation ring of a restricted valuation into the
ambient valuation ring. -/
def restrictedValuationRingMapToAmbient
    (w : LubinTate.Valuations.ExponentialValuation L) (E : IntermediateField K L) :
    LubinTate.Valuations.exponentialValuationSubring
        (exponentialValuationRestrict w E) →+*
      LubinTate.Valuations.exponentialValuationSubring w :=
  E.val.toRingHom.restrict _ _ fun x hx ↦ by
    change (0 : WithTop ℝ) ≤ w (x : L)
    exact hx

@[simp]
theorem restrictedValuationRingMapToAmbient_apply
    (w : LubinTate.Valuations.ExponentialValuation L) (E : IntermediateField K L)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (exponentialValuationRestrict w E)) :
    ((restrictedValuationRingMapToAmbient w E x :
      LubinTate.Valuations.exponentialValuationSubring w) : L) = (x : E) :=
  rfl

/-- The restricted-to-ambient valuation-ring map is local, hence induces an
injective map on the actual residue fields. -/
theorem restrictedValuationRingMapToAmbient_isLocalHom
    (w : LubinTate.Valuations.ExponentialValuation L) (E : IntermediateField K L) :
    IsLocalHom (restrictedValuationRingMapToAmbient w E) := by
  constructor
  intro x hx
  have hwzero :
      w (((restrictedValuationRingMapToAmbient w E) x :
        LubinTate.Valuations.exponentialValuationSubring w) : L) = 0 :=
    LubinTate.Valuations.exponentialValuation_eq_zero_of_isUnit w hx
  have hrestrict : exponentialValuationRestrict w E (x : E) = 0 := by
    exact hwzero
  exact LubinTate.Valuations.isUnit_of_exponentialValuation_eq_zero
    (exponentialValuationRestrict w E) hrestrict

/-- The residue-field embedding from a restricted intermediate field into
the ambient residue field, as an algebra homomorphism over the base residue
field. -/
def restrictedResidueAlgHomToAmbient
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (E : IntermediateField K L) :
    let vE := exponentialValuationRestrict w E
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let VE := LubinTate.Valuations.exponentialValuationSubring vE
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v vE
      (exponentialValuationRestrict_extends v w hExt E)
    let j := restrictedValuationRingMapToAmbient w E
    let b := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v vE
        (exponentialValuationRestrict_extends v w hExt E)
    letI : IsLocalHom j :=
      restrictedValuationRingMapToAmbient_isLocalHom w E
    letI : IsLocalHom b :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    let k := IsLocalRing.ResidueField V
    let kE := IsLocalRing.ResidueField VE
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k kE := (IsLocalRing.ResidueField.map i).toAlgebra
    letI : Algebra k ell := (IsLocalRing.ResidueField.map b).toAlgebra
    kE →ₐ[k] ell := by
  let vE := exponentialValuationRestrict w E
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let VE := LubinTate.Valuations.exponentialValuationSubring vE
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v vE
    (exponentialValuationRestrict_extends v w hExt E)
  let j := restrictedValuationRingMapToAmbient w E
  let b := unramifiedValuationRingValuationRingMap v w hExt
  letI : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v vE
      (exponentialValuationRestrict_extends v w hExt E)
  letI : IsLocalHom j :=
    restrictedValuationRingMapToAmbient_isLocalHom w E
  letI : IsLocalHom b :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let kE := IsLocalRing.ResidueField VE
  let ell := IsLocalRing.ResidueField W
  letI : Algebra k kE := (IsLocalRing.ResidueField.map i).toAlgebra
  letI : Algebra k ell := (IsLocalRing.ResidueField.map b).toAlgebra
  refine
    { IsLocalRing.ResidueField.map j with
      commutes' := ?_ }
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  rfl

/-- Value-group source for the finite unramified embedding.

Every finite unramified subextension occurring in the maximal-unramified-subextension definition
  has exactly
the value subgroup of the base field. -/
theorem finiteUnramifiedSubextension_valueSubgroup_eq
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    {E : IntermediateField K L}
    (hE : FiniteUnramifiedSubextension v w hExt E) :
    exponentialValueSubgroup
        (exponentialValuationRestrict w E) =
      exponentialValueSubgroup v := by
  rcases hE with ⟨hfin, hUnramified⟩
  let : FiniteDimensional K E := hfin
  exact exponentialValueSubgroup_eq_of_finiteUnramifiedExtension
    v (exponentialValuationRestrict w E)
      (exponentialValuationRestrict_extends v w hExt E) hUnramified

/-- Residue-field source for the finite unramified embedding.

The image in the ambient residue field of every residue class from a finite
unramified subextension lies in the separable closure of the base residue
field. -/
theorem finiteUnramifiedSubextension_residue_image_mem_separableClosure
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    {E : IntermediateField K L}
    (hE : FiniteUnramifiedSubextension v w hExt E)
    (x : IsLocalRing.ResidueField
      (LubinTate.Valuations.exponentialValuationSubring
        (exponentialValuationRestrict w E))) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let b := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom b :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    let k := IsLocalRing.ResidueField V
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k ell := (IsLocalRing.ResidueField.map b).toAlgebra
    restrictedResidueAlgHomToAmbient v w hExt E x ∈
      separableClosure k ell := by
  rcases hE with ⟨hfin, hUnramified⟩
  let : FiniteDimensional K E := hfin
  let vE := exponentialValuationRestrict w E
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let VE := LubinTate.Valuations.exponentialValuationSubring vE
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v vE
    (exponentialValuationRestrict_extends v w hExt E)
  let j := restrictedValuationRingMapToAmbient w E
  let b := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v vE
      (exponentialValuationRestrict_extends v w hExt E)
  let : IsLocalHom j :=
    restrictedValuationRingMapToAmbient_isLocalHom w E
  let : IsLocalHom b :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let kE := IsLocalRing.ResidueField VE
  let ell := IsLocalRing.ResidueField W
  let : Algebra k kE := (IsLocalRing.ResidueField.map i).toAlgebra
  let : Algebra k ell := (IsLocalRing.ResidueField.map b).toAlgebra
  have hsep : Algebra.IsSeparable k kE := hUnramified.1
  let : Algebra.IsSeparable k kE := hsep
  let f : kE →ₐ[k] ell :=
    restrictedResidueAlgHomToAmbient v w hExt E
  apply (map_mem_separableClosure_iff f).2
  exact mem_separableClosure_iff.2
    (Algebra.IsSeparable.isSeparable k x)

/-- Field-range form of the finite residue-field inclusion for an unramified
subextension. -/
theorem finiteUnramifiedSubextension_residue_fieldRange_le_separableClosure
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    {E : IntermediateField K L}
    (hE : FiniteUnramifiedSubextension v w hExt E) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let vE := exponentialValuationRestrict w E
    let VE := LubinTate.Valuations.exponentialValuationSubring vE
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v vE
      (exponentialValuationRestrict_extends v w hExt E)
    let b := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v vE
        (exponentialValuationRestrict_extends v w hExt E)
    letI : IsLocalHom b :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    let k := IsLocalRing.ResidueField V
    let kE := IsLocalRing.ResidueField VE
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k kE := (IsLocalRing.ResidueField.map i).toAlgebra
    letI : Algebra k ell := (IsLocalRing.ResidueField.map b).toAlgebra
    (restrictedResidueAlgHomToAmbient v w hExt E).fieldRange ≤
      separableClosure k ell := by
  simp only
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact finiteUnramifiedSubextension_residue_image_mem_separableClosure
    v w hExt hE x

end FiniteUnramifiedSubextensionInvariants

end Valuations
end AlgebraicNumberTheory

end
