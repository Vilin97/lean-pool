/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.FixedFieldLattice
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicZHatBaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedInertiaComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.FixedFieldNormQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.FixedFieldSpecialization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.AbsoluteValueExtensions
/-!
# Finite Galois number-field extensions in the rational separable closure

An actual tower `L / K / ℚ` must be realized by compatible embeddings
before the rational absolute class formation can be applied.  We choose
only the upper embedding `L →ₐ[ℚ] SeparableClosure ℚ`; the lower embedding
is its restriction along `K →ₐ[ℚ] L`.  Thus the two field ranges, their
fixing subgroups, and the norm comparison all come from the existing
mathlib and LCFT constructions.

No second model of a number field, an idele class group, or a norm
quotient is introduced here.
-/

@[expose] public section

open scoped NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The embedding of the lower field obtained by restricting the one
chosen embedding of the top field. -/
noncomputable def numberFieldTowerLowerEmbedding :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  (numberFieldSeparableClosureEmbedding L).comp
    (IsScalarTower.toAlgHom ℚ K L)

/-- The copy of `K` obtained from the chosen copy of `L`; this is the
lower field in the compatible realization of `L / K`. -/
def numberFieldTowerBaseField :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  (numberFieldTowerLowerEmbedding K L).fieldRange

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The compatible embedded copy of `K` lies in the chosen embedded copy
of `L`. -/
theorem numberFieldTowerBaseField_le_topField :
    numberFieldTowerBaseField K L ≤
      numberFieldInRationalSeparableClosure L := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨algebraMap K L y, rfl⟩

/-- The standard inclusion algebra on the two nested field ranges. -/
noncomputable instance numberFieldTowerBaseFieldAlgebra :
    Algebra (numberFieldTowerBaseField K L)
      (numberFieldInRationalSeparableClosure L) :=
  (IntermediateField.inclusion
    (numberFieldTowerBaseField_le_topField K L)).toRingHom.toAlgebra

instance numberFieldTowerBaseFieldScalarTower :
    IsScalarTower ℚ (numberFieldTowerBaseField K L)
      (numberFieldInRationalSeparableClosure L) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance numberFieldTowerBaseField_finiteDimensional :
    FiniteDimensional ℚ (numberFieldTowerBaseField K L) :=
  (numberFieldTowerLowerEmbedding K L).equivFieldRange.toLinearEquiv.finiteDimensional

noncomputable instance numberFieldTowerBaseField_numberField :
    NumberField (numberFieldTowerBaseField K L) :=
  NumberField.of_module_finite ℚ (numberFieldTowerBaseField K L)

noncomputable instance numberFieldTowerTopField_finiteDimensional :
    FiniteDimensional (numberFieldTowerBaseField K L)
      (numberFieldInRationalSeparableClosure L) :=
  FiniteDimensional.right ℚ
    (numberFieldTowerBaseField K L)
    (numberFieldInRationalSeparableClosure L)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The two field-range equivalences form the same square as the original
tower `L / K`. -/
@[simp]
theorem numberFieldTowerFieldRangeEquiv_algebraMap (x : K) :
    (numberFieldSeparableClosureEmbedding L).equivFieldRange
        (algebraMap K L x) =
      algebraMap (numberFieldTowerBaseField K L)
        (numberFieldInRationalSeparableClosure L)
        ((numberFieldTowerLowerEmbedding K L).equivFieldRange x) := by
  rfl

noncomputable instance numberFieldTowerTopField_isGalois :
    IsGalois (numberFieldTowerBaseField K L)
      (numberFieldInRationalSeparableClosure L) := by
  let _ : Algebra
      (numberFieldTowerLowerEmbedding K L).fieldRange
      (numberFieldSeparableClosureEmbedding L).fieldRange :=
    numberFieldTowerBaseFieldAlgebra K L
  exact
    IsGalois.of_equiv_equiv
      (F := K) (E := L)
      (M := (numberFieldTowerLowerEmbedding K L).fieldRange)
      (N := (numberFieldSeparableClosureEmbedding L).fieldRange)
      (f :=
        (numberFieldTowerLowerEmbedding K L).equivFieldRange.toRingEquiv)
      (g :=
        (numberFieldSeparableClosureEmbedding L).equivFieldRange.toRingEquiv)
      (by
        apply RingHom.ext
        intro x
        exact
          (numberFieldTowerFieldRangeEquiv_algebraMap K L x).symm)

/-- The closed subgroup representing the compatible embedded copy of
`K`. -/
def numberFieldTowerBaseSubgroup :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseField K L)

/-- The closed subgroup representing the chosen embedded copy of `L`. -/
def numberFieldTowerTopSubgroup :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ)
    (numberFieldInRationalSeparableClosure L)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Inclusion of compatible field ranges gives the contravariant
inclusion of their fixing subgroups. -/
theorem numberFieldTowerTopSubgroup_le_baseSubgroup :
    (numberFieldTowerTopSubgroup L).toSubgroup ≤
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  change
    (numberFieldInRationalSeparableClosure L).fixingSubgroup ≤
      (numberFieldTowerBaseField K L).fixingSubgroup
  exact
    (numberFieldTowerBaseField K L).fixingSubgroup_le
      (numberFieldTowerBaseField_le_topField K L)

/-- The separable closure of `K` is identified with
`SeparableClosure ℚ` endowed with the algebra structure induced by the
compatible lower embedding. -/
noncomputable def numberFieldTowerSeparableClosureEquiv :
    let i := numberFieldTowerLowerEmbedding K L
    letI : Algebra K (SeparableClosure ℚ) :=
      i.toRingHom.toAlgebra
    SeparableClosure K ≃ₐ[K] SeparableClosure ℚ := by
  dsimp only
  let i := numberFieldTowerLowerEmbedding K L
  let _ : Algebra K (SeparableClosure ℚ) :=
    i.toRingHom.toAlgebra
  letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  letI : Algebra.IsSeparable K (SeparableClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      ℚ K (SeparableClosure ℚ)
  letI : IsSepClosure K (SeparableClosure ℚ) :=
    ⟨inferInstance, inferInstance⟩
  exact
    IsSepClosure.equiv K
      (SeparableClosure K) (SeparableClosure ℚ)

/-- The algebra structure on the rational separable closure induced by
the compatible lower embedding in a number-field tower. -/
@[reducible]
noncomputable def numberFieldTowerSeparableClosureBaseAlgebra :
    Algebra K (SeparableClosure ℚ) :=
  (numberFieldTowerLowerEmbedding K L).toRingHom.toAlgebra

/-- The algebra structure on the rational separable closure induced by
the chosen embedding of the top number field. -/
@[reducible]
noncomputable def numberFieldTowerSeparableClosureTopAlgebra :
    Algebra L (SeparableClosure ℚ) :=
  (numberFieldSeparableClosureEmbedding L).toRingHom.toAlgebra

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The compatible lower embedding also realizes the standard
`ℚ → K` scalar tower inside the rational separable closure. -/
theorem numberFieldTowerSeparableClosureBaseScalarTower :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    IsScalarTower ℚ K (SeparableClosure ℚ) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  exact
    IsScalarTower.of_algebraMap_eq'
      (numberFieldTowerLowerEmbedding K L).comp_algebraMap.symm

/-- The chosen top-field embedding realizes the standard
`ℚ → L` scalar tower inside the rational separable closure. -/
theorem numberFieldTowerSeparableClosureTopScalarTower :
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    IsScalarTower ℚ L (SeparableClosure ℚ) := by
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  exact
    IsScalarTower.of_algebraMap_eq'
      (numberFieldSeparableClosureEmbedding L).comp_algebraMap.symm

/-- With the algebra structure induced by its chosen rational
embedding, the rational separable closure is a genuine Galois
overfield of a number field. -/
theorem numberFieldSeparableClosureTop_isGalois :
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    IsGalois L (SeparableClosure ℚ) := by
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower ℚ L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopScalarTower L
  let : Algebra.IsSeparable L (SeparableClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      ℚ L (SeparableClosure ℚ)
  let : IsSepClosure L (SeparableClosure ℚ) :=
    ⟨inferInstance, inferInstance⟩
  exact
    IsGalois.of_algEquiv
      (IsSepClosure.equiv L
        (SeparableClosure L) (SeparableClosure ℚ))

/-- The actual cyclotomic `ZHat`-compositum of a number field and the
chosen rational separable closure form the expected scalar tower. -/
theorem
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower :
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) := by
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  exact IsScalarTower.of_algebraMap_eq' rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The two compatible embeddings make the rational separable closure
an actual scalar tower over `K → L`. -/
theorem numberFieldTowerSeparableClosureScalarTower :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    IsScalarTower K L (SeparableClosure ℚ) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  exact IsScalarTower.of_algebraMap_eq' rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- With the compatible lower embedding, the rational separable
closure is a genuine Galois overfield of the original base field. -/
theorem numberFieldTowerSeparableClosure_isGalois :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    IsGalois K (SeparableClosure ℚ) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  exact
    IsGalois.of_algEquiv
      (numberFieldTowerSeparableClosureEquiv K L)

/-- Continuous restriction from the compatible separable closure to
the actual finite Galois extension in the original number-field
tower. -/
noncomputable def numberFieldTowerSeparableClosureRestriction :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    Gal(SeparableClosure ℚ/K) →ₜ*
      Gal(L/K) := by
  letI : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let _ : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let _ : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let eL : L →ₐ[K] SeparableClosure ℚ :=
    IsScalarTower.toAlgHom K L (SeparableClosure ℚ)
  let E : IntermediateField K (SeparableClosure ℚ) :=
    eL.fieldRange
  letI : FiniteDimensional K E :=
    eL.equivFieldRange.toLinearEquiv.finiteDimensional
  letI : IsGalois K E :=
    IsGalois.of_algEquiv eL.equivFieldRange
  let c :
      Gal(L/K) ≃*
        Gal(E/K) :=
    AlgEquiv.autCongr eL.equivFieldRange
  let rE :
      Gal(SeparableClosure ℚ/K) →*
        Gal(E/K) :=
    AlgEquiv.restrictNormalHom E
  refine
    { toMonoidHom :=
        AlgEquiv.restrictNormalHom L
      continuous_toFun := ?_ }
  have hrE : Continuous rE :=
    InfiniteGalois.restrictNormalHom_continuous E
  have hc : Continuous c.symm :=
    continuous_of_discreteTopology
  apply (hc.comp hrE).congr
  intro σ
  apply AlgEquiv.ext
  intro x
  apply eL.injective
  change
    eL
        (((AlgEquiv.autCongr eL.equivFieldRange).symm
          (AlgEquiv.restrictNormalHom E σ)) x) =
      eL ((AlgEquiv.restrictNormalHom L σ) x)
  have he (y : E) :
      eL (eL.equivFieldRange.symm y) = E.val y := by
    exact
      congrArg Subtype.val
        (eL.equivFieldRange.apply_symm_apply y)
  calc
    eL
          (((AlgEquiv.autCongr eL.equivFieldRange).symm
            (AlgEquiv.restrictNormalHom E σ)) x) =
        E.val
          ((AlgEquiv.restrictNormalHom E σ)
            (eL.equivFieldRange x)) := by
      simpa only [AlgEquiv.autCongr_symm,
        AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
        AlgEquiv.symm_symm] using
        he
          ((AlgEquiv.restrictNormalHom E σ)
            (eL.equivFieldRange x))
    _ = σ (eL x) := by
      exact
        AlgEquiv.restrictNormal_commutes σ E
          (eL.equivFieldRange x)
    _ = eL ((AlgEquiv.restrictNormalHom L σ) x) := by
      exact
        (AlgEquiv.restrictNormal_commutes σ L x).symm

/-- The compatible continuous restriction evaluates as ordinary
normal-field restriction. -/
@[simp]
theorem numberFieldTowerSeparableClosureRestriction_apply
    (σ :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      letI : Algebra L (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureTopAlgebra L
      letI : IsScalarTower K L (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureScalarTower K L
      Gal(SeparableClosure ℚ/K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    numberFieldTowerSeparableClosureRestriction K L σ =
      AlgEquiv.restrictNormalHom L σ := by
  let _ : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let _ : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let _ : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  change
    (numberFieldTowerSeparableClosureRestriction K L).toMonoidHom σ =
      AlgEquiv.restrictNormalHom L σ
  rfl

/-- Restriction from the compatible separable closure onto the finite
Galois top field is surjective. -/
theorem numberFieldTowerSeparableClosureRestriction_surjective :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    Function.Surjective
      (numberFieldTowerSeparableClosureRestriction K L) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let _ : IsGalois K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosure_isGalois K L
  intro τ
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := L) (E := SeparableClosure ℚ) τ
  refine ⟨σ, ?_⟩
  rw [numberFieldTowerSeparableClosureRestriction_apply]
  exact hσ

/-- A `K`-automorphism of the common rational separable closure,
viewed as the corresponding rational automorphism fixing the embedded
copy of `K`. -/
noncomputable def numberFieldTowerSeparableClosureToBaseSubgroup :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    Gal(SeparableClosure ℚ/K) →*
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  let _ : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  refine
    { toFun := fun σ =>
        ⟨AlgEquiv.restrictScalars ℚ σ, ?_⟩
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' := by
        intro σ τ
        apply Subtype.ext
        rfl }
  change
    AlgEquiv.restrictScalars ℚ σ ∈
      (numberFieldTowerBaseField K L).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact σ.commutes y

/-- The compatible `K`-absolute Galois group is exactly the fixing
subgroup of the embedded copy of `K` inside the rational absolute
Galois group. -/
noncomputable def numberFieldTowerSeparableClosureEquivBaseSubgroup :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    Gal(SeparableClosure ℚ/K) ≃*
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  letI : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  refine
    { toFun := numberFieldTowerSeparableClosureToBaseSubgroup K L
      invFun := fun τ =>
        { τ.1 with
          commutes' := fun x => ?_ }
      left_inv := ?_
      right_inv := ?_
      map_mul' := map_mul
        (numberFieldTowerSeparableClosureToBaseSubgroup K L) }
  · have hτ :
        ∀ z ∈ numberFieldTowerBaseField K L,
          τ.1 z = z := by
      exact
        (IntermediateField.mem_fixingSubgroup_iff
          (numberFieldTowerBaseField K L) τ.1).1 τ.2
    exact
      hτ
        (numberFieldTowerLowerEmbedding K L x)
        ⟨x, rfl⟩
  · intro σ
    apply AlgEquiv.ext
    intro x
    rfl
  · intro τ
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Coercing the base-subgroup comparison equivalence gives restriction of
scalars to the rational base. -/
@[simp]
theorem numberFieldTowerSeparableClosureEquivBaseSubgroup_apply_coe
    (σ :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      Gal(SeparableClosure ℚ/K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    ((numberFieldTowerSeparableClosureEquivBaseSubgroup K L σ :
        (numberFieldTowerBaseSubgroup K L).toSubgroup) :
      Gal(SeparableClosure ℚ/ℚ)) =
      AlgEquiv.restrictScalars ℚ σ := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  change
    (numberFieldTowerSeparableClosureToBaseSubgroup K L σ).1 =
      AlgEquiv.restrictScalars ℚ σ
  rfl

end Reciprocity
end GlobalClassFieldTheory
