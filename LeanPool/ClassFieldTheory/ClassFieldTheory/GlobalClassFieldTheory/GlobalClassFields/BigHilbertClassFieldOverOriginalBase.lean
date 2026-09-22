/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldRealization
/-!
# The big Hilbert class field over the original number field

The selected big Hilbert class field is constructed over a canonical
fixed-field copy of the input number field.  The canonical equivalence
with the original field supplies the actual scalar map used here.  Thus
the selected field is a finite abelian Galois extension of the original
number field, with degree equal to the narrow class number.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- The canonical base fixed field of the big Hilbert realization,
regarded as an algebra over the original number field. -/
noncomputable instance bigHilbertClassFieldBaseAlgebraOverOriginal :
    Algebra K (bigHilbertClassFieldBase K) :=
  (bigHilbertClassFieldBaseEquiv (K := K)).toRingHom.toAlgebra

open scoped Classical in
/-- The canonical base-field identification as an equivalence of
algebras over the original number field. -/
noncomputable def bigHilbertClassFieldBaseEquivOverOriginal :
    K ≃ₐ[K] bigHilbertClassFieldBase K :=
  AlgEquiv.ofRingEquiv
    (f :=
      (bigHilbertClassFieldBaseEquiv (K := K)).toRingEquiv)
    (fun _ => rfl)

open scoped Classical in
/-- The selected big Hilbert class field as an algebra over the
original number field. -/
noncomputable instance bigHilbertClassFieldAlgebraOverOriginal :
    Algebra K (bigHilbertClassField K) :=
  ((algebraMap
      (bigHilbertClassFieldBase K)
      (bigHilbertClassField K)).comp
    (algebraMap K
      (bigHilbertClassFieldBase K))).toAlgebra

open scoped Classical in
/-- The scalar map into the selected big Hilbert class field is the
canonical base equivalence followed by fixed-field inclusion. -/
@[simp]
theorem bigHilbertClassField_algebraMap_original
    (x : K) :
    algebraMap K (bigHilbertClassField K) x =
      algebraMap
        (bigHilbertClassFieldBase K)
        (bigHilbertClassField K)
        (bigHilbertClassFieldBaseEquiv (K := K) x) :=
  rfl

open scoped Classical in
/-- The canonical base fixed field has degree one over the original
number field. -/
noncomputable instance
    bigHilbertClassFieldBaseFiniteDimensionalOverOriginal :
    FiniteDimensional K (bigHilbertClassFieldBase K) :=
  (bigHilbertClassFieldBaseEquivOverOriginal K)
    |>.toLinearEquiv.finiteDimensional

open scoped Classical in
/-- The original field, its fixed-field copy, and the selected big
Hilbert class field form the literal scalar tower. -/
noncomputable instance bigHilbertClassFieldScalarTowerOverOriginal :
    IsScalarTower K
      (bigHilbertClassFieldBase K)
      (bigHilbertClassField K) :=
  IsScalarTower.of_algebraMap_eq' rfl

open scoped Classical in
/-- The selected big Hilbert class field is finite-dimensional over
the original number field. -/
noncomputable instance
    bigHilbertClassFieldFiniteDimensionalOverOriginal :
    FiniteDimensional K (bigHilbertClassField K) :=
  FiniteDimensional.trans K
    (bigHilbertClassFieldBase K)
    (bigHilbertClassField K)

open scoped Classical in
/-- The canonical base fixed field has relative degree one. -/
@[simp]
theorem bigHilbertClassFieldBase_finrank_over_original :
    Module.finrank K (bigHilbertClassFieldBase K) = 1 := by
  simpa only [Module.finrank_self] using
    (LinearEquiv.finrank_eq
      (bigHilbertClassFieldBaseEquivOverOriginal K).toLinearEquiv).symm

open scoped Classical in
/-- The degree of the selected big Hilbert class field over the
original number field is the order of the narrow class group. -/
theorem bigHilbertClassField_finrank_over_original_eq_narrowClassGroup_card :
    Module.finrank K (bigHilbertClassField K) =
      Nat.card (RayClass.NarrowClassGroup K) := by
  calc
    Module.finrank K (bigHilbertClassField K) =
        (bigHilbertClassFieldNormSubgroup (K := K)).index :=
      closedFiniteIndexClassField_finrank_eq_index
        (bigHilbertClassFieldNormSubgroup (K := K))
        (bigHilbertClassFieldNormSubgroup_isClosed (K := K))
    _ = Nat.card
          (IdeleClassGroup K ⧸
            bigHilbertClassFieldNormSubgroup (K := K)) :=
      Subgroup.index_eq_card
        (bigHilbertClassFieldNormSubgroup (K := K))
    _ = Nat.card (RayClass.NarrowClassGroup K) :=
      Nat.card_congr
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K)).toEquiv

open scoped Classical in
/-- The selected big Hilbert class field is Galois over the original
number field. -/
noncomputable instance bigHilbertClassFieldIsGaloisOverOriginal :
    IsGalois K (bigHilbertClassField K) := by
  let e :=
    bigHilbertClassFieldBaseEquiv (K := K)
  apply IsGalois.of_equiv_equiv
    (F := bigHilbertClassFieldBase K)
    (E := bigHilbertClassField K)
    (f := e.symm.toRingEquiv)
    (g := RingEquiv.refl (bigHilbertClassField K))
  apply RingHom.ext
  intro x
  calc
    ((algebraMap K (bigHilbertClassField K)).comp
        e.symm.toRingEquiv) x =
        algebraMap K (bigHilbertClassField K) (e.symm x) := rfl
    _ = algebraMap
          (bigHilbertClassFieldBase K)
          (bigHilbertClassField K)
          (bigHilbertClassFieldBaseEquiv (K := K) (e.symm x)) :=
      bigHilbertClassField_algebraMap_original
        (K := K) (e.symm x)
    _ = algebraMap
          (bigHilbertClassFieldBase K)
          (bigHilbertClassField K) x := by
      simpa only [e] using
        congrArg
          (algebraMap
            (bigHilbertClassFieldBase K)
            (bigHilbertClassField K))
          ((bigHilbertClassFieldBaseEquiv
            (K := K)).apply_symm_apply x)
    _ = ((RingEquiv.refl
            (bigHilbertClassField K)).toRingHom.comp
          (algebraMap
            (bigHilbertClassFieldBase K)
            (bigHilbertClassField K))) x := rfl

open scoped Classical in
/-- The selected big Hilbert class field is an abelian Galois
extension of the original number field. -/
noncomputable instance bigHilbertClassFieldIsAbelianGaloisOverOriginal :
    IsAbelianGalois K (bigHilbertClassField K) :=
  IsAbelianGalois.of_base_equiv
    (bigHilbertClassFieldBaseEquiv (K := K)).toRingEquiv
    (bigHilbertClassField_algebraMap_original (K := K))

end GlobalClassFields
end GlobalClassFieldTheory
