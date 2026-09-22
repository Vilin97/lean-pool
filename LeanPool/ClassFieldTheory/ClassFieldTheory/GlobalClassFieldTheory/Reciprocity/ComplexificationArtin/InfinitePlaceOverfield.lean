/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RationalComplexification
/-!
# The complex-conjugation overfield at an infinite place

This module realizes the embedded field `L(i)` inside `ℂ`, constructs its
complex place, and identifies ambient complex conjugation on that field.
-/

open scoped IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K]
    [Field L] [NumberField L] [Algebra K L]

open scoped Classical in
/-- The field range of a complex embedding is preserved by complex
conjugation when a relative automorphism realizes that conjugation. -/
theorem complexEmbeddingFieldRange_map_complexConjugation
    (φ : L →+* ℂ)
    (σ : L ≃ₐ[K] L)
    (hσ : NumberField.ComplexEmbedding.IsConj φ σ) :
    φ.toRatAlgHom.fieldRange.map
        (Complex.conjAe.restrictScalars ℚ).toAlgHom =
      φ.toRatAlgHom.fieldRange := by
  rw [AlgHom.map_fieldRange]
  apply SetLike.ext
  intro z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨σ x, ?_⟩
    exact hσ.eq x
  · rintro ⟨x, rfl⟩
    refine ⟨σ.symm x, ?_⟩
    calc
      (Complex.conjAe.restrictScalars ℚ)
          (φ (σ.symm x)) =
          φ (σ (σ.symm x)) :=
        (hσ.eq (σ.symm x)).symm
      _ = φ x := by rw [σ.apply_symm_apply]

variable
    [NumberField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

open scoped Classical in
/-- The concrete field `L(i)` inside `ℂ`, formed using the complex
embedding belonging to the chosen place above `v`. -/
def infinitePlaceComplexificationOverfield
    (v : InfinitePlace K) :
    IntermediateField ℚ ℂ :=
  (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom.fieldRange ⊔
    complexFourthRootField

open scoped Classical in
/-- The complex overfield attached to an infinite place carries its intermediate-field rational
algebra structure. -/
@[reducible]
noncomputable local instance
    infinitePlaceComplexificationOverfieldRationalAlgebra
    (v : InfinitePlace K) :
    Algebra ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (infinitePlaceComplexificationOverfield
    (K := K) (L := L) v).algebra'

attribute [local instance] infinitePlaceComplexificationOverfieldRationalAlgebra

open scoped Classical in
noncomputable instance
    infinitePlaceComplexificationOverfield_finiteDimensional
    (v : InfinitePlace K) :
    FiniteDimensional ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) := by
  let φ :=
    (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom
  let : FiniteDimensional ℚ φ.fieldRange :=
    φ.equivFieldRange.toLinearEquiv.finiteDimensional
  exact
    IntermediateField.finiteDimensional_sup
      φ.fieldRange complexFourthRootField

open scoped Classical in
noncomputable instance
    infinitePlaceComplexificationOverfield_numberField
    (v : InfinitePlace K) :
    NumberField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  NumberField.of_module_finite ℚ
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

open scoped Classical in
/-- The chosen top-field embedding `L → L(i)`. -/
noncomputable def infinitePlaceComplexificationOverfieldEmbedding
    (v : InfinitePlace K) :
    L →ₐ[ℚ]
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v :=
  let φ :=
    (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom
  φ.codRestrict
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v).toSubalgebra
    (fun x =>
      (show
        φ.fieldRange ≤
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v from
        le_sup_left)
        (show φ x ∈ φ.fieldRange from
          (AlgHom.mem_fieldRange).mpr ⟨x, rfl⟩))

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The chosen embedding into the complexification overfield agrees
with the original complex embedding after coercion to `ℂ`. -/
@[simp]
theorem infinitePlaceComplexificationOverfieldEmbedding_coe
    (v : InfinitePlace K) (x : L) :
    ((infinitePlaceComplexificationOverfieldEmbedding
        (K := K) (L := L) v x :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) : ℂ) =
      InfinitePlace.embedding
        (chosenInfinitePlaceAbove (L := L) v) x := by
  change
    (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom x =
      InfinitePlace.embedding
        (chosenInfinitePlaceAbove (L := L) v) x
  rfl

open scoped Classical in
noncomputable instance
    infinitePlaceComplexificationOverfieldAlgebra
    (v : InfinitePlace K) :
    Algebra L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (infinitePlaceComplexificationOverfieldEmbedding
    (K := K) (L := L) v).toRingHom.toAlgebra

open scoped Classical in
/-- The scalar action belonging to the chosen top-field embedding. -/
noncomputable instance
    infinitePlaceComplexificationOverfieldSmul
    (v : InfinitePlace K) :
    SMul L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (infinitePlaceComplexificationOverfieldAlgebra
    (K := K) (L := L) v).toSMul

open scoped Classical in
instance
    infinitePlaceComplexificationOverfield_ratScalarTower
    (v : InfinitePlace K) :
    IsScalarTower ℚ L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IsScalarTower.of_algebraMap_eq'
    (infinitePlaceComplexificationOverfieldEmbedding
      (K := K) (L := L) v).comp_algebraMap.symm

open scoped Classical in
noncomputable instance
    infinitePlaceComplexificationOverfieldBaseAlgebra
    (v : InfinitePlace K) :
    Algebra K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  ((infinitePlaceComplexificationOverfieldEmbedding
      (K := K) (L := L) v).comp
    (IsScalarTower.toAlgHom ℚ K L)).toRingHom.toAlgebra

open scoped Classical in
/-- The scalar action induced from the original base-field embedding. -/
noncomputable instance
    infinitePlaceComplexificationOverfieldBaseSmul
    (v : InfinitePlace K) :
    SMul K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (infinitePlaceComplexificationOverfieldBaseAlgebra
    (K := K) (L := L) v).toSMul

open scoped Classical in
instance
    infinitePlaceComplexificationOverfield_baseRatScalarTower
    (v : InfinitePlace K) :
    IsScalarTower ℚ K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IsScalarTower.of_algebraMap_eq'
    (((infinitePlaceComplexificationOverfieldEmbedding
        (K := K) (L := L) v).comp
      (IsScalarTower.toAlgHom ℚ K L)).comp_algebraMap).symm

open scoped Classical in
instance
    infinitePlaceComplexificationOverfield_scalarTower
    (v : InfinitePlace K) :
    IsScalarTower K L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IsScalarTower.of_algebraMap_eq' rfl

open scoped Classical in
noncomputable instance
    infinitePlaceComplexificationOverfield_finiteDimensional_over_extension
    (v : InfinitePlace K) :
    FiniteDimensional L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  FiniteDimensional.right ℚ L
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

open scoped Classical in
/-- The cyclotomic fourth-root field embeds into the concrete
overfield through its copy in `ℂ`. -/
noncomputable def
    rationalComplexificationEmbeddingInInfinitePlaceOverfield
    (v : InfinitePlace K) :
    rationalComplexificationCyclotomicField →ₐ[ℚ]
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v :=
  (IntermediateField.inclusion
      (show
        complexFourthRootField ≤
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v from
        le_sup_right)).comp
    (rationalComplexificationComplexEquiv.toAlgHom)

open scoped Classical in
omit [NumberField K] [FiniteDimensional K L] in
/-- The fourth-root-field embedding preserves the chosen complex value. -/
theorem rationalComplexificationEmbeddingInInfinitePlaceOverfield_coe
    (v : InfinitePlace K) (x : rationalComplexificationCyclotomicField) :
    ((rationalComplexificationEmbeddingInInfinitePlaceOverfield
      (K := K) (L := L) v x :
        infinitePlaceComplexificationOverfield (K := K) (L := L) v) : ℂ) =
      (rationalComplexificationComplexEquiv x : ℂ) := rfl

open scoped Classical in
noncomputable instance
    rationalComplexificationInfinitePlaceOverfieldAlgebra
    (v : InfinitePlace K) :
    Algebra rationalComplexificationCyclotomicField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (rationalComplexificationEmbeddingInInfinitePlaceOverfield
    (K := K) (L := L) v).toRingHom.toAlgebra

open scoped Classical in
/-- The scalar action induced by the concrete fourth-root-field
embedding.  Declaring it directly keeps instance search away from
unrelated intermediate-field algebra structures. -/
noncomputable instance
    rationalComplexificationInfinitePlaceOverfieldSmul
    (v : InfinitePlace K) :
    SMul rationalComplexificationCyclotomicField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (rationalComplexificationInfinitePlaceOverfieldAlgebra
    (K := K) (L := L) v).toSMul

open scoped Classical in
instance
    rationalComplexification_infinitePlaceOverfield_scalarTower
    (v : InfinitePlace K) :
    IsScalarTower ℚ rationalComplexificationCyclotomicField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IsScalarTower.of_algebraMap_eq'
    (rationalComplexificationEmbeddingInInfinitePlaceOverfield
      (K := K) (L := L) v).comp_algebraMap.symm

open scoped Classical in
/-- The copy of the given abelian extension inside the concrete
complexification overfield, viewed over the original base field. -/
noncomputable def infinitePlaceEmbeddedExtensionField
    (v : InfinitePlace K) :
    IntermediateField K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (IsScalarTower.toAlgHom K L
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)).fieldRange

open scoped Classical in
noncomputable instance
    infinitePlaceEmbeddedExtensionField_isAbelianGalois
    (v : InfinitePlace K) :
    IsAbelianGalois K
      (infinitePlaceEmbeddedExtensionField
        (K := K) (L := L) v) :=
  IsAbelianGalois.of_algHom
    (IsScalarTower.toAlgHom K L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)).equivFieldRange.symm.toAlgHom

open scoped Classical in
/-- The fourth-root cyclotomic factor over the original base field,
inside the concrete complexification overfield. -/
noncomputable def infinitePlaceBaseFourthRootField
    (v : InfinitePlace K) :
    IntermediateField K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IntermediateField.adjoin K
    {z :
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v |
      ∃ n ∈ ({4} : Set ℕ), n ≠ 0 ∧ z ^ n = 1}

open scoped Classical in
noncomputable instance
    infinitePlaceBaseFourthRootField_isCyclotomic
    (v : InfinitePlace K) :
    IsCyclotomicExtension {4} K
      (infinitePlaceBaseFourthRootField
        (K := K) (L := L) v) := by
  apply
    IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      ({4} : Set ℕ) K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)
  intro n hn _hn0
  rw [Set.mem_singleton_iff] at hn
  subst n
  let C :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let ζ : C :=
    ⟨Complex.I,
      (show complexFourthRootField ≤ C from le_sup_right)
        (IntermediateField.subset_adjoin
          ℚ
          {z : ℂ |
            ∃ n ∈ ({4} : Set ℕ),
              n ≠ 0 ∧ z ^ n = 1}
          ⟨4, Set.mem_singleton 4, by norm_num,
            by norm_num [pow_succ, Complex.I_sq]⟩)⟩
  refine ⟨ζ, ?_⟩
  apply IsPrimitiveRoot.of_map_of_injective
    (f :=
      (C.val : C →ₐ[ℚ] ℂ))
    (ζ := ζ)
    (k := 4)
  · change IsPrimitiveRoot Complex.I 4
    exact complexI_isPrimitiveRoot_four
  · exact C.val.injective

open scoped Classical in
noncomputable instance
    infinitePlaceBaseFourthRootField_isAbelianGalois
    (v : InfinitePlace K) :
    IsAbelianGalois K
      (infinitePlaceBaseFourthRootField
        (K := K) (L := L) v) :=
  IsCyclotomicExtension.isAbelianGalois
    ({4} : Set ℕ) K
    (infinitePlaceBaseFourthRootField
      (K := K) (L := L) v)

omit [FiniteDimensional K L] in
open scoped Classical in
private noncomputable def infinitePlaceRatEmbeddedExtensionField
    (v : InfinitePlace K) :
    IntermediateField ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  let φ :=
    (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom
  φ.fieldRange.restrict
    (show
      φ.fieldRange ≤
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v from
      le_sup_left)

omit [FiniteDimensional K L] in
open scoped Classical in
private noncomputable def infinitePlaceRatFourthRootField
    (v : InfinitePlace K) :
    IntermediateField ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  complexFourthRootField.restrict
    (show
      complexFourthRootField ≤
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v from
      le_sup_right)

omit [FiniteDimensional K L] in
open scoped Classical in
private noncomputable def infinitePlaceRatComplexificationFactors
    (v : InfinitePlace K) :
    IntermediateField ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (infinitePlaceEmbeddedExtensionField
      (K := K) (L := L) v ⊔
    infinitePlaceBaseFourthRootField
      (K := K) (L := L) v).restrictScalars ℚ

omit [FiniteDimensional K L] in
open scoped Classical in
private theorem infinitePlaceRatEmbeddedExtensionField_le_factors
    (v : InfinitePlace K) :
    infinitePlaceRatEmbeddedExtensionField
          (K := K) (L := L) v ≤
      infinitePlaceRatComplexificationFactors
          (K := K) (L := L) v := by
  let C :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let φ :=
    (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom
  let A :=
    infinitePlaceEmbeddedExtensionField
      (K := K) (L := L) v
  let B :=
    infinitePlaceBaseFourthRootField
      (K := K) (L := L) v
  intro x hx
  have hx' :
      (x : C).1 ∈ φ.fieldRange :=
    (IntermediateField.mem_restrict
      (show φ.fieldRange ≤ C from le_sup_left) x).mp hx
  obtain ⟨y, hy⟩ := hx'
  change (x : C) ∈ A ⊔ B
  apply (show A ≤ A ⊔ B from le_sup_left)
  change
    (x : C) ∈
      (IsScalarTower.toAlgHom K L C).fieldRange
  refine ⟨y, ?_⟩
  apply Subtype.ext
  calc
    ((IsScalarTower.toAlgHom K L C y : C) : ℂ) =
        InfinitePlace.embedding
          (chosenInfinitePlaceAbove (L := L) v) y := by
      change
        ((infinitePlaceComplexificationOverfieldEmbedding
            (K := K) (L := L) v y : C) : ℂ) = _
      exact
        infinitePlaceComplexificationOverfieldEmbedding_coe
          (K := K) (L := L) v y
    _ = (x : C).1 := hy

omit [FiniteDimensional K L] in
open scoped Classical in
private theorem infinitePlaceRatFourthRootField_le_factors
    (v : InfinitePlace K) :
    infinitePlaceRatFourthRootField
          (K := K) (L := L) v ≤
      infinitePlaceRatComplexificationFactors
          (K := K) (L := L) v := by
  let C :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let A :=
    infinitePlaceEmbeddedExtensionField
      (K := K) (L := L) v
  let B :=
    infinitePlaceBaseFourthRootField
      (K := K) (L := L) v
  intro x hx
  have hx' :
      (x : C).1 ∈ complexFourthRootField :=
    (IntermediateField.mem_restrict
      (show complexFourthRootField ≤ C from le_sup_right) x).mp hx
  let y : complexFourthRootField := ⟨(x : C).1, hx'⟩
  let i : complexFourthRootField →ₐ[ℚ] C :=
    IntermediateField.inclusion
      (show complexFourthRootField ≤ C from le_sup_right)
  have hy :
      y ∈
        Algebra.adjoin ℚ
          {z : complexFourthRootField |
            ∃ n ∈ ({4} : Set ℕ),
              n ≠ 0 ∧ z ^ n = 1} :=
    IsCyclotomicExtension.adjoin_roots y
  have hiy : i y ∈ B := by
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hy
    · intro z hz
      change
        i z ∈
          IntermediateField.adjoin K
            {w : C |
              ∃ n ∈ ({4} : Set ℕ),
                n ≠ 0 ∧ w ^ n = 1}
      apply IntermediateField.subset_adjoin K
      rcases hz with ⟨n, hn, hn0, hz⟩
      exact
        ⟨n, hn, hn0, by
          rw [← map_pow, hz, map_one]⟩
    · intro q
      rw [i.commutes,
        IsScalarTower.algebraMap_apply ℚ K C]
      exact B.algebraMap_mem (algebraMap ℚ K q)
    · intro z w _hz _hw hiz hiw
      exact B.add_mem hiz hiw
    · intro z w _hz _hw hiz hiw
      exact B.mul_mem hiz hiw
  change (x : C) ∈ A ⊔ B
  apply (show B ≤ A ⊔ B from le_sup_right)
  have hiyx : i y = (x : C) := by
    apply Subtype.ext
    rfl
  rw [← hiyx]
  exact hiy

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
private theorem infinitePlaceRatComplexificationFactors_sup
    (v : InfinitePlace K) :
    infinitePlaceRatEmbeddedExtensionField
          (K := K) (L := L) v ⊔
        infinitePlaceRatFourthRootField
          (K := K) (L := L) v =
      ⊤ := by
  apply IntermediateField.lift_injective
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)
  rw [infinitePlaceRatEmbeddedExtensionField,
    infinitePlaceRatFourthRootField,
    IntermediateField.lift_sup,
    IntermediateField.lift_restrict,
    IntermediateField.lift_restrict,
    IntermediateField.lift_top]
  rfl

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The embedded abelian extension and the base-changed fourth-root
factor generate the whole concrete complexification overfield. -/
theorem infinitePlaceComplexificationFactors_sup
    (v : InfinitePlace K) :
    infinitePlaceEmbeddedExtensionField
          (K := K) (L := L) v ⊔
        infinitePlaceBaseFourthRootField
          (K := K) (L := L) v =
      ⊤ := by
  apply
    (IntermediateField.restrictScalars_eq_top_iff
      (K := ℚ)).mp
  change
    infinitePlaceRatComplexificationFactors
        (K := K) (L := L) v =
      ⊤
  apply top_unique
  rw [← infinitePlaceRatComplexificationFactors_sup
    (K := K) (L := L) v]
  exact sup_le
    (infinitePlaceRatEmbeddedExtensionField_le_factors
      (K := K) (L := L) v)
    (infinitePlaceRatFourthRootField_le_factors
      (K := K) (L := L) v)

open scoped Classical in
noncomputable instance
    infinitePlaceComplexificationOverfield_isAbelianGalois_over_base
    (v : InfinitePlace K) :
    IsAbelianGalois K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) := by
  let C :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let A :=
    infinitePlaceEmbeddedExtensionField
      (K := K) (L := L) v
  let B :=
    infinitePlaceBaseFourthRootField
      (K := K) (L := L) v
  let : FiniteDimensional K A :=
    (IsScalarTower.toAlgHom K L C).equivFieldRange.toLinearEquiv
      |>.finiteDimensional
  let : FiniteDimensional K B :=
    IsCyclotomicExtension.finiteDimensional
      ({4} : Set ℕ) K B
  let :
      IsAbelianGalois K
        (⊤ : IntermediateField K C) := by
    rw [← infinitePlaceComplexificationFactors_sup
      (K := K) (L := L) v]
    exact
      AlgebraicNumberTheory.isAbelianGalois_sup K A B
  exact
    IsAbelianGalois.of_algHom
      (IntermediateField.topEquiv.symm.toAlgHom :
        C →ₐ[K] (⊤ : IntermediateField K C))

open scoped Classical in
noncomputable instance
    infinitePlaceComplexificationOverfield_isTotallyComplex
    (v : InfinitePlace K) :
    IsTotallyComplex
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  NumberField.isTotallyComplex_of_algebra
    rationalComplexificationCyclotomicField
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

open scoped Classical in
/-- The infinite place on the concrete overfield induced by its
inclusion into `ℂ`. -/
noncomputable def infinitePlaceComplexificationOverfieldComplexPlace
    (v : InfinitePlace K) :
    InfinitePlace
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  InfinitePlace.mk
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v).val.toRingHom

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- Complex conjugation preserves the concrete overfield `L(i)` at a
ramified chosen place.  Preservation of the `L`-factor is the actual
local Artin value being a conjugation; preservation of the fourth-root
factor is intrinsic. -/
theorem infinitePlaceComplexificationOverfield_map_complexConjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v).map
        (Complex.conjAe.restrictScalars ℚ).toAlgHom =
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v := by
  rw [infinitePlaceComplexificationOverfield,
    IntermediateField.map_sup,
    complexEmbeddingFieldRange_map_complexConjugation
      (K := K)
      (L := L)
      (φ :=
        InfinitePlace.embedding
          (chosenInfinitePlaceAbove (L := L) v))
      (σ :=
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (-1 : v.Completionˣ))
      (hσ :=
        chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
          (K := K) (L := L) v hRamified),
    complexFourthRootField_map_complexConjugation]

open scoped Classical in
/-- Complex conjugation restricted to the actual overfield `L(i)`. -/
noncomputable def ramifiedInfinitePlaceOverfieldConjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    infinitePlaceComplexificationOverfield
          (K := K) (L := L) v ≃ₐ[ℚ]
      infinitePlaceComplexificationOverfield
          (K := K) (L := L) v :=
  (IntermediateField.equivMap
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)
      (Complex.conjAe.restrictScalars ℚ).toAlgHom).trans
    (IntermediateField.equivOfEq
      (infinitePlaceComplexificationOverfield_map_complexConjugation
        (K := K) (L := L) v hRamified))

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The restricted overfield automorphism acts by ambient complex
conjugation. -/
@[simp]
theorem ramifiedInfinitePlaceOverfieldConjugation_apply
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (z :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :
    (ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified z : ℂ) =
      star (z : ℂ) := by
  rfl

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The restricted overfield complex conjugation is an involution. -/
@[simp]
theorem ramifiedInfinitePlaceOverfieldConjugation_sq
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified *
        ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified =
      1 := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  change
    (ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified
        (ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified z) : ℂ) =
      (z : ℂ)
  simp only [ramifiedInfinitePlaceOverfieldConjugation_apply,
    star_star]

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
