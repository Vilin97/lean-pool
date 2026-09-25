/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.EmbeddedAbelianSubextension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormTowerConductor
/-!
# Containment of finite abelian class fields

For actual finite abelian extensions of a number field, containment is
exactly reverse containment of their genuine idèle-class norm ranges.

The proof first realizes an arbitrary extension in the same rational
separable closure as the class field selected by a closed finite-index
subgroup.  The abstract finite-abelian classification then gives a
literal inclusion of fixing subgroups, which restricts the chosen
ambient embedding to an actual algebra embedding into the selected
class field.  Applying this construction to the norm range of a second
extension yields the intrinsic containment criterion over the original
number field.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open RamificationTheory
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
private theorem subgroup_map_toAddSubgroup_mulEquiv_eq
    {G G₂ : Type*} [Group G] [Group G₂]
    (S : Subgroup G) (T : Subgroup G₂) (e : G ≃* G₂)
    (hmap : S.map e.toMonoidHom = T) :
    T.toAddSubgroup =
      S.toAddSubgroup.map
        (MulEquiv.toAdditive e).toAddMonoidHom := by
  rw [← hmap]
  exact (MonoidHom.coe_toAdditive_map e.toMonoidHom S).symm

open scoped Classical in
private theorem subgroup_toAddSubgroup_map_mono_mulEquiv
    {G G₂ : Type*} [Group G] [Group G₂]
    (S T : Subgroup G) (e : G ≃* G₂)
    (h : S ≤ T) :
    S.toAddSubgroup.map
        (MulEquiv.toAdditive e).toAddMonoidHom ≤
      T.toAddSubgroup.map
        (MulEquiv.toAdditive e).toAddMonoidHom :=
  AddSubgroup.map_mono h

open scoped Classical in
/-- The distinguished embedding of the original number field into the
rational separable closure underlying the class field selected by
`H`. -/
noncomputable def closedFiniteIndexClassFieldBaseEmbedding
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  numberFieldTowerLowerEmbedding K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed)

open scoped Classical in
/-- The canonical fixed-field equivalence has the distinguished base
embedding as its underlying map into the rational separable closure. -/
@[simp]
theorem closedFiniteIndexClassFieldBaseEquiv_coe
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (x : K) :
    ((closedFiniteIndexClassFieldBaseEquiv
        (K := K) H hclosed x :
      closedFiniteIndexClassFieldBase
        (K := K) H hclosed) :
      SeparableClosure ℚ) =
      closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed x := by
  rfl

open scoped Classical in
private noncomputable def
    finiteAbelianClassFieldContainmentIdeleClassEquiv
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IdeleClassGroup K ≃*
      IdeleClassGroup
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed) :=
  ideleClassCongr
    (closedFiniteIndexClassFieldBaseEquiv
      (K := K) H hclosed)

open scoped Classical in
/-- An actual finite extension of `K`, embedded into the rational
separable closure compatibly with the selected class-field copy of
`K`. -/
noncomputable def closedFiniteIndexClassFieldCompatibleEmbedding
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] :
    E →ₐ[ℚ] SeparableClosure ℚ :=
  Classical.choose
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ) (L := K) (E := E)
      (M := SeparableClosure ℚ)
      (closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed))

open scoped Classical in
/-- The compatible top embedding restricts to the distinguished
embedding of the original base field. -/
@[simp]
theorem
    closedFiniteIndexClassFieldCompatibleEmbedding_restrictDomain
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] :
    (closedFiniteIndexClassFieldCompatibleEmbedding
      (K := K) H hclosed E).domRestrict K =
      closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed :=
  Classical.choose_spec
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ) (L := K) (E := E)
      (M := SeparableClosure ℚ)
      (closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed))

open scoped Classical in
/-- Evaluation on the original scalar map agrees with the
distinguished base embedding. -/
@[simp]
theorem closedFiniteIndexClassFieldCompatibleEmbedding_algebraMap
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    (x : K) :
    closedFiniteIndexClassFieldCompatibleEmbedding
        (K := K) H hclosed E
        (algebraMap K E x) =
      closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed x := by
  have h :=
    DFunLike.congr_fun
      (closedFiniteIndexClassFieldCompatibleEmbedding_restrictDomain
        (K := K) H hclosed E) x
  exact h

open scoped Classical in
/-- The fixing subgroup of the compatible embedded copy of `K` is the
base subgroup used by the selected class field. -/
@[simp]
theorem closedFiniteIndexClassFieldCompatibleEmbedding_baseSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] :
    numberFieldEmbeddedBaseSubgroup K E
        (closedFiniteIndexClassFieldCompatibleEmbedding
          (K := K) H hclosed E) =
      closedFiniteIndexClassFieldBaseSubgroup
        (K := K) H hclosed := by
  change
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
        ((closedFiniteIndexClassFieldCompatibleEmbedding
          (K := K) H hclosed E).domRestrict K).fieldRange =
      closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (closedFiniteIndexClassFieldBaseEmbedding
          (K := K) H hclosed).fieldRange
  rw [
    closedFiniteIndexClassFieldCompatibleEmbedding_restrictDomain
      (K := K) H hclosed E]

open scoped Classical in
/-- An actual finite abelian extension, represented inside the same
rational absolute Galois group as the class field selected by `H`. -/
noncomputable def
    closedFiniteIndexClassFieldEmbeddedAbelianSubextension
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    FiniteAbelianSubextension
      (closedFiniteIndexClassFieldBaseSubgroup
        (K := K) H hclosed) :=
  numberFieldEmbeddedAbelianSubextension K E
    (closedFiniteIndexClassFieldCompatibleEmbedding
      (K := K) H hclosed E)
    (closedFiniteIndexClassFieldBaseSubgroup
      (K := K) H hclosed)
    (closedFiniteIndexClassFieldCompatibleEmbedding_baseSubgroup
      (K := K) H hclosed E)

open scoped Classical in
/-- The top subgroup of the embedded abelian subextension is exactly
the fixing subgroup of the compatible embedded copy of `E`. -/
@[simp]
theorem
    closedFiniteIndexClassFieldEmbeddedAbelianSubextension_field
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
      (K := K) H hclosed E).field =
      numberFieldEmbeddedTopSubgroup K E
        (closedFiniteIndexClassFieldCompatibleEmbedding
          (K := K) H hclosed E) := by
  exact
    numberFieldEmbeddedAbelianSubextension_field K E
      (closedFiniteIndexClassFieldCompatibleEmbedding
        (K := K) H hclosed E)
      (closedFiniteIndexClassFieldBaseSubgroup
        (K := K) H hclosed)
      (closedFiniteIndexClassFieldCompatibleEmbedding_baseSubgroup
        (K := K) H hclosed E)

open scoped Classical in
/-- The abstract norm subgroup of the compatibly embedded extension is
the genuine idèle-class norm range of the original extension,
transported through the selected base-field equivalence. -/
private theorem
    ordinaryIdeleClassNormSubgroup_embeddedAbelianSubextension_named
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    ordinaryIdeleClassNormSubgroup
        (numberFieldTowerFiniteAbstractField K
          (closedFiniteIndexClassFieldNormAmbient
            (K := K) H hclosed))
        (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
          (K := K) H hclosed E) =
      (_root_.ideleClassNorm K E).range.toAddSubgroup.map
        (MulEquiv.toAdditive
          (finiteAbelianClassFieldContainmentIdeleClassEquiv
            (K := K) H hclosed)).toAddMonoidHom := by
  let Q :=
    numberFieldTowerFiniteAbstractField K
      (closedFiniteIndexClassFieldNormAmbient
        (K := K) H hclosed)
  let P :=
    closedFiniteIndexClassFieldEmbeddedAbelianSubextension
      (K := K) H hclosed E
  let A :=
    ordinaryIdeleClassNormExtension Q P
  let j :=
    closedFiniteIndexClassFieldCompatibleEmbedding
      (K := K) H hclosed E
  let eK :=
    closedFiniteIndexClassFieldBaseEquiv
      (K := K) H hclosed
  let hANumberField : NumberField A :=
    ordinaryIdeleClassNormExtensionNumberField Q P
  let eQ :=
    numberFieldEmbeddedAbstractTopFieldEquiv K E j
  have hPField :
      P.field = numberFieldEmbeddedTopSubgroup K E j := by
    simpa only [P, j] using
      (closedFiniteIndexClassFieldEmbeddedAbelianSubextension_field
        (K := K) H hclosed E)
  let RawField :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K E j)
  let eRestrict : (RawField.restrictScalars ℚ) ≃+* A :=
    { toFun := fun x =>
        ⟨x.1, by
          change x.1 ∈
            abstractFixedField ℚ (SeparableClosure ℚ) P.field
          rw [hPField]
          exact x.2⟩
      invFun := fun x =>
        ⟨x.1, by
          change x.1 ∈
            abstractFixedField ℚ (SeparableClosure ℚ)
              (numberFieldEmbeddedTopSubgroup K E j)
          rw [← hPField]
          exact x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl }
  let eERing : E ≃+* A := by
    exact eQ.toRingEquiv.trans eRestrict
  let eE : E ≃ₐ[ℚ] A :=
    AlgEquiv.ofRingEquiv (f := eERing)
      (fun x => DFunLike.congr_fun
        (RingHom.ext_rat
          (eERing.toRingHom.comp (algebraMap ℚ E))
          (algebraMap ℚ A)) x)
  have hcompat :
      ∀ x : K,
        eE (algebraMap K E x) =
          algebraMap
            (closedFiniteIndexClassFieldBase
              (K := K) H hclosed) A (eK x) := by
    intro x
    apply Subtype.ext
    change
      ((eERing (algebraMap K E x) : A) : SeparableClosure ℚ) =
        ((eK x : closedFiniteIndexClassFieldBase
          (K := K) H hclosed) : SeparableClosure ℚ)
    calc
      ((eERing (algebraMap K E x) : A) : SeparableClosure ℚ) =
          j (algebraMap K E x) := by
        rfl
      _ = ((eK x : closedFiniteIndexClassFieldBase
          (K := K) H hclosed) : SeparableClosure ℚ) := by
        rw [
          closedFiniteIndexClassFieldCompatibleEmbedding_algebraMap
            (K := K) H hclosed E,
          closedFiniteIndexClassFieldBaseEquiv_coe
            (K := K) H hclosed]
  have hRange :
      (_root_.ideleClassNorm K E).range.map
          (finiteAbelianClassFieldContainmentIdeleClassEquiv
            (K := K) H hclosed).toMonoidHom =
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed) A).range := by
    change
      (_root_.ideleClassNorm K E).range.map
          (ideleClassCongr eK).toMonoidHom =
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed) A).range
    exact
      ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv
        eK eE hcompat
  calc
    ordinaryIdeleClassNormSubgroup Q P =
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed) A).range.toAddSubgroup :=
      ordinaryIdeleClassNormSubgroup_eq_namedNormRange Q P
    _ =
        (_root_.ideleClassNorm K E).range.toAddSubgroup.map
          (MulEquiv.toAdditive
            (finiteAbelianClassFieldContainmentIdeleClassEquiv
              (K := K) H hclosed)).toAddMonoidHom :=
      subgroup_map_toAddSubgroup_mulEquiv_eq
        (_root_.ideleClassNorm K E).range
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed) A).range
        (finiteAbelianClassFieldContainmentIdeleClassEquiv
          (K := K) H hclosed) hRange

open scoped Classical in
/-- The abstract norm subgroup of the compatibly embedded extension is
the genuine idèle-class norm range of the original extension, expressed at
the concrete selected base-field endpoint. -/
theorem
    ordinaryIdeleClassNormSubgroup_embeddedAbelianSubextension
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    ordinaryIdeleClassNormSubgroup
        (numberFieldTowerFiniteAbstractField K
          (closedFiniteIndexClassFieldNormAmbient
            (K := K) H hclosed))
        (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
          (K := K) H hclosed E) =
      (_root_.ideleClassNorm K E).range.toAddSubgroup.map
        (MulEquiv.toAdditive
          (ideleClassCongr
            (closedFiniteIndexClassFieldBaseEquiv
              (K := K) H hclosed))).toAddMonoidHom := by
  change
    ordinaryIdeleClassNormSubgroup
        (numberFieldTowerFiniteAbstractField K
          (closedFiniteIndexClassFieldNormAmbient
            (K := K) H hclosed))
        (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
          (K := K) H hclosed E) =
      (_root_.ideleClassNorm K E).range.toAddSubgroup.map
        (MulEquiv.toAdditive
          (finiteAbelianClassFieldContainmentIdeleClassEquiv
            (K := K) H hclosed)).toAddMonoidHom
  exact
    ordinaryIdeleClassNormSubgroup_embeddedAbelianSubextension_named
      (K := K) H hclosed E

open scoped Classical in
private theorem
    ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassFieldSubextension_named
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    ordinaryIdeleClassNormSubgroup
        (numberFieldTowerFiniteAbstractField K
          (closedFiniteIndexClassFieldNormAmbient
            (K := K) H hclosed))
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed) =
      H.toAddSubgroup.map
        (MulEquiv.toAdditive
          (finiteAbelianClassFieldContainmentIdeleClassEquiv
            (K := K) H hclosed)).toAddMonoidHom := by
  change
    ordinaryIdeleClassNormSubgroup
        (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
          (K := K) H hclosed)
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed) =
      H.toAddSubgroup.map
        (MulEquiv.toAdditive
          (ideleClassCongr
            (closedFiniteIndexClassFieldBaseEquiv
              (K := K) H hclosed))).toAddMonoidHom
  exact
    ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassFieldSubextension
      (K := K) H hclosed

open scoped Classical in
/-- If `H` is contained in the genuine norm range of an actual finite
abelian extension, its compatible embedded subextension lies below the
finite abelian subextension selected by `H`. -/
theorem
    embeddedAbelianSubextension_le_closedFiniteIndexClassFieldSubextension
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (hH :
      H ≤ (_root_.ideleClassNorm K E).range) :
    closedFiniteIndexClassFieldEmbeddedAbelianSubextension
        (K := K) H hclosed E ≤
      closedFiniteIndexClassFieldSubextension
        (K := K) H hclosed := by
  apply
    (le_iff_ordinaryIdeleClassNormSubgroup_le
      (numberFieldTowerFiniteAbstractField K
        (closedFiniteIndexClassFieldNormAmbient
          (K := K) H hclosed))
      (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
        (K := K) H hclosed E)
      (closedFiniteIndexClassFieldSubextension
        (K := K) H hclosed)).2
  calc
    ordinaryIdeleClassNormSubgroup
        (numberFieldTowerFiniteAbstractField K
          (closedFiniteIndexClassFieldNormAmbient
            (K := K) H hclosed))
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed) =
        H.toAddSubgroup.map
          (MulEquiv.toAdditive
            (finiteAbelianClassFieldContainmentIdeleClassEquiv
              (K := K) H hclosed)).toAddMonoidHom :=
      ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassFieldSubextension_named
        (K := K) H hclosed
    _ ≤
        (_root_.ideleClassNorm K E).range.toAddSubgroup.map
          (MulEquiv.toAdditive
            (finiteAbelianClassFieldContainmentIdeleClassEquiv
              (K := K) H hclosed)).toAddMonoidHom :=
      subgroup_toAddSubgroup_map_mono_mulEquiv
        H (_root_.ideleClassNorm K E).range
        (finiteAbelianClassFieldContainmentIdeleClassEquiv
          (K := K) H hclosed)
        hH
    _ =
        ordinaryIdeleClassNormSubgroup
          (numberFieldTowerFiniteAbstractField K
            (closedFiniteIndexClassFieldNormAmbient
              (K := K) H hclosed))
          (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
            (K := K) H hclosed E) :=
      (ordinaryIdeleClassNormSubgroup_embeddedAbelianSubextension_named
        (K := K) H hclosed E).symm

open scoped Classical in
/-- The compatible ambient embedding agrees with the selected base
equivalence on scalars from the original number field. -/
private theorem
    finiteAbelianExtensionEmbedding_ambient_algebraMap_eq_baseEquiv
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    (x : K) :
    closedFiniteIndexClassFieldCompatibleEmbedding
        (K := K) H hclosed E (algebraMap K E x) =
      ((closedFiniteIndexClassFieldBaseEquiv
          (K := K) H hclosed x :
        closedFiniteIndexClassFieldBase
          (K := K) H hclosed) :
        SeparableClosure ℚ) := by
  rw [
    closedFiniteIndexClassFieldCompatibleEmbedding_algebraMap
      (K := K) H hclosed E,
    closedFiniteIndexClassFieldBaseEquiv_coe
      (K := K) H hclosed]

open scoped Classical in
/-- A point of a compatibly embedded subextension belongs to the
selected class field whenever the corresponding finite abelian
subextension lies below the selected one. -/
private theorem
    finiteAbelianExtensionEmbedding_codRestrict_mem
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (hcontain :
      closedFiniteIndexClassFieldEmbeddedAbelianSubextension
          (K := K) H hclosed E ≤
        closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed)
    (x : E) :
    closedFiniteIndexClassFieldCompatibleEmbedding
        (K := K) H hclosed E x ∈
      abstractFixedField ℚ (SeparableClosure ℚ)
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed).field := by
  have hxP :
      closedFiniteIndexClassFieldCompatibleEmbedding
          (K := K) H hclosed E x ∈
        abstractFixedField ℚ (SeparableClosure ℚ)
          (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
            (K := K) H hclosed E).field := by
    rw [closedFiniteIndexClassFieldEmbeddedAbelianSubextension_field]
    change
      closedFiniteIndexClassFieldCompatibleEmbedding
          (K := K) H hclosed E x ∈
        IntermediateField.fixedField
          (closedFiniteIndexClassFieldCompatibleEmbedding
            (K := K) H hclosed E).fieldRange.fixingSubgroup
    rw [InfiniteGalois.fixedField_fixingSubgroup]
    exact ⟨x, rfl⟩
  have hsubgroup :
      (closedFiniteIndexClassFieldSubextension
        (K := K) H hclosed).field.toSubgroup ≤
        (closedFiniteIndexClassFieldEmbeddedAbelianSubextension
          (K := K) H hclosed E).field.toSubgroup :=
    hcontain
  exact
    (abstractFixedField_le
      ℚ (SeparableClosure ℚ) hsubgroup) hxP

open scoped Classical in
/-- Every finite abelian extension whose genuine norm range contains
`H` admits an actual `K`-algebra embedding into the class field selected
by `H`. -/
noncomputable def
    finiteAbelianExtensionEmbeddingIntoClosedFiniteIndexClassField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (hH :
      H ≤ (_root_.ideleClassNorm K E).range) :
    E →ₐ[K]
      closedFiniteIndexClassField
        (K := K) H hclosed := by
  let j :=
    closedFiniteIndexClassFieldCompatibleEmbedding
      (K := K) H hclosed E
  have hcontain :
      closedFiniteIndexClassFieldEmbeddedAbelianSubextension
          (K := K) H hclosed E ≤
        closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed :=
    embeddedAbelianSubextension_le_closedFiniteIndexClassFieldSubextension
      (K := K) H hclosed E hH
  let jClassField :
      E →+*
        closedFiniteIndexClassField
          (K := K) H hclosed :=
    j.toRingHom.codRestrict
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed).below).toSubring
      (finiteAbelianExtensionEmbedding_codRestrict_mem
        (K := K) H hclosed E hcontain)
  exact
    { jClassField with
      commutes' := fun x =>
        Subtype.ext
          (finiteAbelianExtensionEmbedding_ambient_algebraMap_eq_baseEquiv
            (K := K) H hclosed E x) }

open scoped Classical in
/-- Containment in a selected finite abelian class field, stated as
existence of an actual algebra embedding over the original base. -/
theorem
    finiteAbelianExtension_nonempty_algHom_closedFiniteIndexClassField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (hH :
      H ≤ (_root_.ideleClassNorm K E).range) :
    Nonempty
      (E →ₐ[K]
        closedFiniteIndexClassField
          (K := K) H hclosed) :=
  ⟨finiteAbelianExtensionEmbeddingIntoClosedFiniteIndexClassField
    (K := K) H hclosed E hH⟩

open scoped Classical in
/-- A finite abelian extension is isomorphic over the original base to
the class field selected by its own genuine idèle-class norm range. -/
noncomputable def
    finiteAbelianExtensionEquivClosedFiniteIndexNormClassField
    (E : Type) [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    E ≃ₐ[K]
      closedFiniteIndexClassField
        (K := K)
        (_root_.ideleClassNorm K E).range
        (ideleClassNorm_range_isClosed
          (K := K) (L := E)) := by
  let H :=
    (_root_.ideleClassNorm K E).range
  let hclosed :
      IsClosed (H : Set (IdeleClassGroup K)) :=
    ideleClassNorm_range_isClosed
      (K := K) (L := E)
  let f :
      E →ₐ[K]
        closedFiniteIndexClassField
          (K := K) H hclosed :=
    finiteAbelianExtensionEmbeddingIntoClosedFiniteIndexClassField
      (K := K) H hclosed E le_rfl
  have hdim :
      Module.finrank K E =
        Module.finrank K
          (closedFiniteIndexClassField
            (K := K) H hclosed) := by
    calc
      Module.finrank K E =
          H.index :=
        (ideleClassNorm_index_eq_finrank_abelian K E).symm
      _ =
          Module.finrank K
            (closedFiniteIndexClassField
              (K := K) H hclosed) :=
        (closedFiniteIndexClassField_finrank_eq_index
          (K := K) H hclosed).symm
  have hsurjective :
      Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hdim (f := f.toLinearMap)).mp f.injective
  simpa only [H, hclosed] using
    AlgEquiv.ofBijective f
      ⟨f.injective, hsurjective⟩

open scoped Classical in
/-- An algebra embedding of finite extensions reverses inclusion of
their genuine idèle-class norm ranges. -/
theorem ideleClassNorm_range_le_of_algHom
    (L₁ L₂ : Type)
    [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (f : L₁ →ₐ[K] L₂) :
    (_root_.ideleClassNorm K L₂).range ≤
      (_root_.ideleClassNorm K L₁).range := by
  let : Algebra L₁ L₂ :=
    f.toRingHom.toAlgebra
  let : IsScalarTower K L₁ L₂ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      exact (f.commutes x).symm
  let : FiniteDimensional L₁ L₂ :=
    FiniteDimensional.right K L₁ L₂
  exact
    ideleClassNorm_range_le_of_tower
      (K := K) (M := L₁) (L := L₂)

open scoped Classical in
/-- Reverse inclusion of genuine idèle-class norm ranges constructs an
actual algebra embedding of the corresponding finite abelian
extensions over the original base field. -/
noncomputable def finiteAbelianExtensionEmbeddingOfNormRangeLE
    (L₁ L₂ : Type)
    [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsAbelianGalois K L₁] [IsAbelianGalois K L₂]
    (h :
      (_root_.ideleClassNorm K L₂).range ≤
        (_root_.ideleClassNorm K L₁).range) :
    L₁ →ₐ[K] L₂ := by
  let H :=
    (_root_.ideleClassNorm K L₂).range
  let hclosed :
      IsClosed (H : Set (IdeleClassGroup K)) :=
    ideleClassNorm_range_isClosed
      (K := K) (L := L₂)
  let f₁ :
      L₁ →ₐ[K]
        closedFiniteIndexClassField
          (K := K) H hclosed :=
    finiteAbelianExtensionEmbeddingIntoClosedFiniteIndexClassField
      (K := K) H hclosed L₁ h
  let e₂ :
      L₂ ≃ₐ[K]
        closedFiniteIndexClassField
          (K := K) H hclosed := by
    simpa only [H, hclosed] using
      finiteAbelianExtensionEquivClosedFiniteIndexNormClassField
        (K := K) L₂
  exact
    e₂.symm.toAlgHom.comp f₁

open scoped Classical in
/-- Reverse norm-range inclusion implies actual field containment over
the original number field. -/
theorem finiteAbelianExtension_nonempty_algHom_of_normRange_le
    (L₁ L₂ : Type)
    [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsAbelianGalois K L₁] [IsAbelianGalois K L₂]
    (h :
      (_root_.ideleClassNorm K L₂).range ≤
        (_root_.ideleClassNorm K L₁).range) :
    Nonempty (L₁ →ₐ[K] L₂) :=
  ⟨finiteAbelianExtensionEmbeddingOfNormRangeLE
    (K := K) L₁ L₂ h⟩

open scoped Classical in
/-- Actual containment of finite abelian extensions is equivalent to
reverse inclusion of their genuine idèle-class norm ranges. -/
theorem nonempty_algHom_iff_ideleClassNorm_range_le
    (L₁ L₂ : Type)
    [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    Nonempty (L₁ →ₐ[K] L₂) ↔
      (_root_.ideleClassNorm K L₂).range ≤
        (_root_.ideleClassNorm K L₁).range := by
  constructor
  · rintro ⟨f⟩
    exact
      ideleClassNorm_range_le_of_algHom
        (K := K) L₁ L₂ f
  · exact
      finiteAbelianExtension_nonempty_algHom_of_normRange_le
        (K := K) L₁ L₂

open scoped Classical in
/-- Equality of genuine norm ranges characterizes isomorphism of
finite abelian extensions over the original number field. -/
theorem nonempty_algEquiv_iff_ideleClassNorm_range_eq
    (L₁ L₂ : Type)
    [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    Nonempty (L₁ ≃ₐ[K] L₂) ↔
      (_root_.ideleClassNorm K L₁).range =
        (_root_.ideleClassNorm K L₂).range := by
  constructor
  · rintro ⟨e⟩
    apply le_antisymm
    · exact
        ideleClassNorm_range_le_of_algHom
          (K := K) L₂ L₁ e.symm.toAlgHom
    · exact
        ideleClassNorm_range_le_of_algHom
          (K := K) L₁ L₂ e.toAlgHom
  · intro h
    let f :
        L₁ →ₐ[K] L₂ :=
      finiteAbelianExtensionEmbeddingOfNormRangeLE
        (K := K) L₁ L₂ h.symm.le
    have hdim :
        Module.finrank K L₁ =
          Module.finrank K L₂ := by
      calc
        Module.finrank K L₁ =
            (_root_.ideleClassNorm K L₁).range.index :=
          (ideleClassNorm_index_eq_finrank_abelian
            K L₁).symm
        _ =
            (_root_.ideleClassNorm K L₂).range.index :=
          congrArg Subgroup.index h
        _ =
            Module.finrank K L₂ :=
          ideleClassNorm_index_eq_finrank_abelian
            K L₂
    have hsurjective :
        Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hdim (f := f.toLinearMap)).mp f.injective
    exact
      ⟨AlgEquiv.ofBijective f
        ⟨f.injective, hsurjective⟩⟩

end GlobalClassFields
end GlobalClassFieldTheory
