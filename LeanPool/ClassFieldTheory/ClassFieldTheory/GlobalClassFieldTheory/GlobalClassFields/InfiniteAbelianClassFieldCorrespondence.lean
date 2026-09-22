/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel
/-!
# Infinite abelian class-field correspondence

Maximal abelian reciprocity transports closed subgroups of the idele-class
component quotient to closed subgroups of the maximal abelian Galois group.
Composing this transport with the infinite Galois correspondence gives the
order-reversing infinite abelian class-field correspondence.
-/

open scoped NumberField

noncomputable section

namespace ClosedSubgroup

variable {G H : Type*}
  [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H]

open scoped Classical in
/-- Transport a closed subgroup along a continuous multiplicative
equivalence. -/
noncomputable def mapContinuousMulEquiv
    (e : G ≃ₜ* H) (S : ClosedSubgroup G) : ClosedSubgroup H where
  toSubgroup := e.toMulEquiv.mapSubgroup S.toSubgroup
  isClosed' := by
    change IsClosed (e '' (S : Set G))
    exact e.toHomeomorph.isClosedMap (S : Set G) S.isClosed'

open scoped Classical in
/-- A continuous multiplicative equivalence induces an order equivalence on
closed subgroups. -/
noncomputable def orderIsoMapContinuousMulEquiv
    (e : G ≃ₜ* H) : ClosedSubgroup G ≃o ClosedSubgroup H where
  toFun := mapContinuousMulEquiv e
  invFun := mapContinuousMulEquiv e.symm
  left_inv S := by
    apply ClosedSubgroup.toSubgroup_injective
    change
      e.symm.toMulEquiv.mapSubgroup
          (e.toMulEquiv.mapSubgroup S.toSubgroup) =
        S.toSubgroup
    exact e.toMulEquiv.mapSubgroup.left_inv S.toSubgroup
  right_inv T := by
    apply ClosedSubgroup.toSubgroup_injective
    change
      e.toMulEquiv.mapSubgroup
          (e.symm.toMulEquiv.mapSubgroup T.toSubgroup) =
        T.toSubgroup
    exact e.toMulEquiv.mapSubgroup.right_inv T.toSubgroup
  map_rel_iff' {S T} := by
    change
      e.toMulEquiv.mapSubgroup S.toSubgroup ≤
          e.toMulEquiv.mapSubgroup T.toSubgroup ↔
        S.toSubgroup ≤ T.toSubgroup
    exact e.toMulEquiv.mapSubgroup.le_iff_le

open scoped Classical in
/-- The order-dual form of closed-subgroup transport. -/
noncomputable def orderDualIsoMapContinuousMulEquiv
    (e : G ≃ₜ* H) :
    (ClosedSubgroup G)ᵒᵈ ≃o (ClosedSubgroup H)ᵒᵈ where
  toFun S := OrderDual.toDual
    (mapContinuousMulEquiv e (OrderDual.ofDual S))
  invFun T := OrderDual.toDual
    (mapContinuousMulEquiv e.symm (OrderDual.ofDual T))
  left_inv S := by
    exact congrArg OrderDual.toDual
      ((orderIsoMapContinuousMulEquiv e).left_inv (OrderDual.ofDual S))
  right_inv T := by
    exact congrArg OrderDual.toDual
      ((orderIsoMapContinuousMulEquiv e).right_inv (OrderDual.ofDual T))
  map_rel_iff' {S T} := by
    change
      mapContinuousMulEquiv e (OrderDual.ofDual T) ≤
          mapContinuousMulEquiv e (OrderDual.ofDual S) ↔
        OrderDual.ofDual T ≤ OrderDual.ofDual S
    exact (orderIsoMapContinuousMulEquiv e).le_iff_le

open scoped Classical in
@[simp]
theorem coe_mapContinuousMulEquiv
    (e : G ≃ₜ* H) (S : ClosedSubgroup G) :
    (mapContinuousMulEquiv e S : Set H) = e '' (S : Set G) := by
  change
    (↑(Subgroup.map e.toMonoidHom S.toSubgroup) : Set H) =
      e.toMonoidHom '' (S : Set G)
  exact Subgroup.coe_map e.toMonoidHom S.toSubgroup

end ClosedSubgroup

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- The infinite abelian class-field correspondence.  The order dual in the
domain records that larger closed idele-class subgroups correspond to smaller
intermediate fields. -/
noncomputable def infiniteAbelianClassFieldCorrespondence :
    (ClosedSubgroup (ideleClassComponentQuotient K))ᵒᵈ ≃o
      IntermediateField K (maximalAbelianExtension K) :=
  (ClosedSubgroup.orderDualIsoMapContinuousMulEquiv
      (ideleClassComponentQuotientEquivMaximalAbelianGalois K)).trans
    (InfiniteGalois.IntermediateFieldEquivClosedSubgroup
      (k := K) (K := maximalAbelianExtension K)).symm

open scoped Classical in
/-- Forward evaluation is the fixed field of the transported closed
idele-class subgroup. -/
@[simp]
theorem infiniteAbelianClassFieldCorrespondence_apply
    (H : ClosedSubgroup (ideleClassComponentQuotient K)) :
    infiniteAbelianClassFieldCorrespondence K (OrderDual.toDual H) =
      IntermediateField.fixedField
        (ClosedSubgroup.mapContinuousMulEquiv
          (ideleClassComponentQuotientEquivMaximalAbelianGalois K) H) :=
  rfl

open scoped Classical in
/-- The inverse correspondence is the fixing subgroup transported back to
the idele-class component quotient. -/
@[simp]
theorem infiniteAbelianClassFieldCorrespondence_symm_apply
    (L : IntermediateField K (maximalAbelianExtension K)) :
    (infiniteAbelianClassFieldCorrespondence K).symm L =
      OrderDual.toDual
        (ClosedSubgroup.mapContinuousMulEquiv
          (ideleClassComponentQuotientEquivMaximalAbelianGalois K).symm
          { toSubgroup := L.fixingSubgroup
            isClosed' := InfiniteGalois.fixingSubgroup_isClosed L }) :=
  rfl

open scoped Classical in
/-- The fixing subgroup of the field corresponding to `H` is exactly the
transport of `H` by maximal abelian reciprocity. -/
theorem infiniteAbelianClassFieldCorrespondence_fixingSubgroup
    (H : ClosedSubgroup (ideleClassComponentQuotient K)) :
    (infiniteAbelianClassFieldCorrespondence K
        (OrderDual.toDual H)).fixingSubgroup =
      (ClosedSubgroup.mapContinuousMulEquiv
        (ideleClassComponentQuotientEquivMaximalAbelianGalois K) H).toSubgroup := by
  rw [infiniteAbelianClassFieldCorrespondence_apply]
  exact InfiniteGalois.fixingSubgroup_fixedField _

open scoped Classical in
/-- A field in the infinite abelian correspondence is finite over the base
exactly when the corresponding closed idele-class subgroup is open. -/
theorem infiniteAbelianClassFieldCorrespondence_finite_iff_open
    (H : ClosedSubgroup (ideleClassComponentQuotient K)) :
    FiniteDimensional K
        (infiniteAbelianClassFieldCorrespondence K
          (OrderDual.toDual H)) ↔
      IsOpen (H : Set (ideleClassComponentQuotient K)) := by
  let L :=
    infiniteAbelianClassFieldCorrespondence K (OrderDual.toDual H)
  let e := ideleClassComponentQuotientEquivMaximalAbelianGalois K
  let T := ClosedSubgroup.mapContinuousMulEquiv e H
  have hfix : L.fixingSubgroup = T.toSubgroup := by
    simpa only [L, T, e] using
      infiniteAbelianClassFieldCorrespondence_fixingSubgroup K H
  calc
    FiniteDimensional K L ↔
        IsOpen (L.fixingSubgroup : Set
          Gal(maximalAbelianExtension K/K)) :=
      (InfiniteGalois.isOpen_iff_finite L).symm
    _ ↔ IsOpen (T : Set Gal(maximalAbelianExtension K/K)) := by
      rw [hfix]
      change
        IsOpen (T : Set Gal(maximalAbelianExtension K/K)) ↔
          IsOpen (T : Set Gal(maximalAbelianExtension K/K))
      exact Iff.rfl
    _ ↔ IsOpen (H : Set (ideleClassComponentQuotient K)) := by
      change
        IsOpen (e '' (H : Set (ideleClassComponentQuotient K))) ↔
          IsOpen (H : Set (ideleClassComponentQuotient K))
      exact e.toHomeomorph.isOpen_image

end GlobalClassFields
end GlobalClassFieldTheory
