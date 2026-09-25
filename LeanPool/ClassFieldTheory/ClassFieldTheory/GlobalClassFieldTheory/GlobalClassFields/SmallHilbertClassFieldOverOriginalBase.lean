/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldRealization
/-!
# The small Hilbert class field over the original number field

The finite class-field construction realizes the small Hilbert class
field over a canonical fixed-field copy of the input number field.
The fixed-field copy is canonically `ℚ`-algebra equivalent to the
original field.  This file uses that equivalence as the actual scalar
map, so the selected Hilbert class field becomes a finite abelian
Galois extension of the original field itself.

This is the scalar structure used by the final extension-of-ideals map
in the principal ideal theorem.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- The canonical fixed-field copy underlying the selected small
Hilbert class field, regarded as an algebra over the original number
field. -/
noncomputable instance smallHilbertClassFieldBaseAlgebraOverOriginal :
    Algebra K (smallHilbertClassFieldBase K) :=
  (smallHilbertClassFieldBaseEquiv (K := K)).toRingHom.toAlgebra

open scoped Classical in
/-- The canonical base-field identification, now regarded as an
equivalence of algebras over the original field. -/
noncomputable def smallHilbertClassFieldBaseEquivOverOriginal :
    K ≃ₐ[K] smallHilbertClassFieldBase K :=
  AlgEquiv.ofRingEquiv
    (f :=
      (smallHilbertClassFieldBaseEquiv (K := K)).toRingEquiv)
    (fun _ => rfl)

open scoped Classical in
/-- The selected small Hilbert class field, regarded as an algebra over
the original number field through the canonical fixed-field copy. -/
noncomputable instance smallHilbertClassFieldAlgebraOverOriginal :
    Algebra K (smallHilbertClassField K) :=
  ((algebraMap
      (smallHilbertClassFieldBase K)
      (smallHilbertClassField K)).comp
    (algebraMap K
      (smallHilbertClassFieldBase K))).toAlgebra

open scoped Classical in
/-- The scalar map from the original number field into the selected
small Hilbert class field is literally the canonical base equivalence
followed by the fixed-field inclusion. -/
@[simp]
theorem smallHilbertClassField_algebraMap_original
    (x : K) :
    algebraMap K (smallHilbertClassField K) x =
      algebraMap
        (smallHilbertClassFieldBase K)
        (smallHilbertClassField K)
        (smallHilbertClassFieldBaseEquiv (K := K) x) :=
  rfl

open scoped Classical in
/-- The canonical fixed-field copy has degree one over the original
number field. -/
noncomputable instance
    smallHilbertClassFieldBaseFiniteDimensionalOverOriginal :
    FiniteDimensional K (smallHilbertClassFieldBase K) :=
  (smallHilbertClassFieldBaseEquivOverOriginal K)
    |>.toLinearEquiv.finiteDimensional

open scoped Classical in
/-- The original field, its canonical fixed-field copy, and the
selected small Hilbert class field form the literal scalar tower used
by extension of ideals. -/
noncomputable instance smallHilbertClassFieldScalarTowerOverOriginal :
    IsScalarTower K
      (smallHilbertClassFieldBase K)
      (smallHilbertClassField K) :=
  IsScalarTower.of_algebraMap_eq' rfl

open scoped Classical in
/-- The selected small Hilbert class field is finite-dimensional over
the original number field. -/
noncomputable instance
    smallHilbertClassFieldFiniteDimensionalOverOriginal :
    FiniteDimensional K (smallHilbertClassField K) :=
  FiniteDimensional.trans K
    (smallHilbertClassFieldBase K)
    (smallHilbertClassField K)

open scoped Classical in
/-- The canonical fixed-field copy has relative degree one over the
original number field. -/
@[simp]
theorem smallHilbertClassFieldBase_finrank_over_original :
    Module.finrank K (smallHilbertClassFieldBase K) = 1 := by
  simpa only [Module.finrank_self] using
    (LinearEquiv.finrank_eq
      (smallHilbertClassFieldBaseEquivOverOriginal K).toLinearEquiv).symm

open scoped Classical in
/-- The degree of the selected small Hilbert class field over the
original number field is its ordinary class number. -/
theorem smallHilbertClassField_finrank_over_original_eq_classNumber :
    Module.finrank K (smallHilbertClassField K) =
      NumberField.classNumber K := by
  calc
    Module.finrank K (smallHilbertClassField K) =
        (smallHilbertClassFieldNormSubgroup (K := K)).index :=
      closedFiniteIndexClassField_finrank_eq_index
        (smallHilbertClassFieldNormSubgroup (K := K))
        (smallHilbertClassFieldNormSubgroup_isClosed (K := K))
    _ = Nat.card
          (IdeleClassGroup K ⧸
            smallHilbertClassFieldNormSubgroup (K := K)) :=
      Subgroup.index_eq_card
        (smallHilbertClassFieldNormSubgroup (K := K))
    _ = NumberField.classNumber K :=
      smallHilbertClassFieldQuotient_card_eq_classNumber
        (K := K)

open scoped Classical in
/-- The selected small Hilbert class field is Galois over the original
number field, not only over its canonically equivalent fixed-field
copy. -/
noncomputable instance smallHilbertClassFieldIsGaloisOverOriginal :
    IsGalois K (smallHilbertClassField K) := by
  let e :=
    smallHilbertClassFieldBaseEquiv (K := K)
  apply IsGalois.of_equiv_equiv
    (F := smallHilbertClassFieldBase K)
    (E := smallHilbertClassField K)
    (f := e.symm.toRingEquiv)
    (g := RingEquiv.refl (smallHilbertClassField K))
  apply RingHom.ext
  intro x
  calc
    ((algebraMap K (smallHilbertClassField K)).comp
        e.symm.toRingEquiv) x =
        algebraMap K (smallHilbertClassField K) (e.symm x) := rfl
    _ = algebraMap
          (smallHilbertClassFieldBase K)
          (smallHilbertClassField K)
          (smallHilbertClassFieldBaseEquiv (K := K) (e.symm x)) :=
      smallHilbertClassField_algebraMap_original
        (K := K) (e.symm x)
    _ = algebraMap
          (smallHilbertClassFieldBase K)
          (smallHilbertClassField K) x := by
      simpa only [e] using
        congrArg
          (algebraMap
            (smallHilbertClassFieldBase K)
            (smallHilbertClassField K))
          ((smallHilbertClassFieldBaseEquiv
            (K := K)).apply_symm_apply x)
    _ = ((RingEquiv.refl
            (smallHilbertClassField K)).toRingHom.comp
          (algebraMap
            (smallHilbertClassFieldBase K)
            (smallHilbertClassField K))) x := rfl

open scoped Classical in
/-- The selected small Hilbert class field is an abelian Galois
extension of the original number field. -/
noncomputable instance
    smallHilbertClassFieldIsAbelianGaloisOverOriginal :
    IsAbelianGalois K (smallHilbertClassField K) :=
  IsAbelianGalois.of_base_equiv
    (smallHilbertClassFieldBaseEquiv (K := K)).toRingEquiv
    (smallHilbertClassField_algebraMap_original (K := K))

end GlobalClassFields
end GlobalClassFieldTheory
