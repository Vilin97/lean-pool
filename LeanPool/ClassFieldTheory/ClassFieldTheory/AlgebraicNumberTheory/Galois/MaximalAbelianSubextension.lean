/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
import LeanPool.ClassFieldTheory.GaloisCohomology.GroupTheory.Quotient
import Mathlib.FieldTheory.Galois.Abelian
/-!
# Maximal abelian subextensions inside finite normal closures

For a finite extension `L / K`, its chosen finite normal closure contains a
distinguished copy of `L`.  The subgroup fixing that copy, together with the
commutator subgroup of the full Galois group, cuts out the largest abelian
Galois intermediate field contained in the distinguished copy.
-/

noncomputable section

open scoped IsMulCommutative

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The subgroup of the finite-normal-closure Galois group fixing the
distinguished copy of the original extension. -/
noncomputable def finiteNormalClosureOriginalFixingSubgroup :
    Subgroup Gal(finiteNormalClosure K L / K) :=
  (finiteNormalClosureOriginalField K L).fixingSubgroup

/-- The relative Galois group over the distinguished original field is the
corresponding fixing subgroup of the full normal-closure Galois group. -/
noncomputable def finiteNormalClosureOriginalFixingSubgroupEquiv :
    Gal(finiteNormalClosure K L /
        finiteNormalClosureOriginalField K L) ≃*
      finiteNormalClosureOriginalFixingSubgroup K L := by
  change
    Gal(finiteNormalClosure K L /
        finiteNormalClosureOriginalField K L) ≃*
      (finiteNormalClosureOriginalField K L).fixingSubgroup
  exact
    (IntermediateField.fixingSubgroupEquiv
      (finiteNormalClosureOriginalField K L)).symm

/-- The largest abelian Galois intermediate field of the finite normal
closure that is contained in the distinguished copy of the original field. -/
noncomputable def finiteNormalClosureMaximalAbelianSubfield :
    IntermediateField K (finiteNormalClosure K L) :=
  IntermediateField.fixedField
    (finiteNormalClosureOriginalFixingSubgroup K L ⊔
      _root_.commutator Gal(finiteNormalClosure K L / K))

/-- The maximal abelian subfield is contained in the distinguished copy of
the original extension. -/
theorem finiteNormalClosureMaximalAbelianSubfield_le_originalField :
    finiteNormalClosureMaximalAbelianSubfield K L ≤
      finiteNormalClosureOriginalField K L := by
  let N := finiteNormalClosure K L
  let E : IntermediateField K N :=
    finiteNormalClosureOriginalField K L
  let G := Gal(N/K)
  let H : Subgroup G :=
    finiteNormalClosureOriginalFixingSubgroup K L
  change
    IntermediateField.fixedField
        (H ⊔ _root_.commutator G) ≤ E
  calc
    IntermediateField.fixedField
        (H ⊔ _root_.commutator G) ≤
        IntermediateField.fixedField H :=
      IntermediateField.fixedField_le le_sup_left
    _ = E := by
      change IntermediateField.fixedField E.fixingSubgroup = E
      exact IsGalois.fixedField_fixingSubgroup E

/-- The maximal abelian subfield is abelian Galois over the base field. -/
noncomputable instance
    finiteNormalClosureMaximalAbelianSubfield_isAbelianGalois :
    IsAbelianGalois K
      (finiteNormalClosureMaximalAbelianSubfield K L) := by
  let N := finiteNormalClosure K L
  let G := Gal(N/K)
  let H : Subgroup G :=
    finiteNormalClosureOriginalFixingSubgroup K L
  let S : Subgroup G := H ⊔ _root_.commutator G
  let M : IntermediateField K N :=
    IntermediateField.fixedField S
  change IsAbelianGalois K M
  let : S.Normal := inferInstance
  let hM : IsGalois K M :=
    IsGalois.of_fixedField_normal_subgroup S
  let e :
      Gal(M/K) ≃*
        Abelianization G ⧸
          H.map (Abelianization.of : G →* Abelianization G) :=
    (IsGalois.normalAutEquivQuotient S).symm.trans
      H.quotientSupCommutatorEquivMapAbelianization
  have hcomm : IsMulCommutative Gal(M/K) :=
    ⟨⟨fun sigma tau => by
      apply e.injective
      rw [map_mul, map_mul, mul_comm]⟩⟩
  exact
    { toIsGalois := hM
      toIsMulCommutative := hcomm }

/-- Every abelian Galois intermediate field contained in the distinguished
original field is contained in the maximal abelian subfield. -/
theorem finiteNormalClosureMaximalAbelianSubfield_greatest
    (F : IntermediateField K (finiteNormalClosure K L))
    [IsAbelianGalois K F]
    (hF : F ≤ finiteNormalClosureOriginalField K L) :
    F ≤ finiteNormalClosureMaximalAbelianSubfield K L := by
  let N := finiteNormalClosure K L
  let E : IntermediateField K N :=
    finiteNormalClosureOriginalField K L
  let G := Gal(N/K)
  let H : Subgroup G :=
    finiteNormalClosureOriginalFixingSubgroup K L
  change
    F ≤ IntermediateField.fixedField
      (H ⊔ _root_.commutator G)
  apply
    (IntermediateField.le_iff_le
      (H ⊔ _root_.commutator G) F).2
  apply sup_le
  · change E.fixingSubgroup ≤ F.fixingSubgroup
    exact IntermediateField.fixingSubgroup_le hF
  · rw [← F.restrictNormalHom_ker]
    exact Abelianization.commutator_subset_ker
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) F)
