/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedStandardLevelTransport
/-!
# The finite standard/changed compositum in the completed p-adic level

The completed level contains two finite abelian extensions of `ℚ_[p]`:

* the image of the ordinary standard multiplicative Lubin--Tate level;
* the fixed field of the inverse-unit completed Frobenius lift, identified
  with the changed-uniformizer level.

Their compositum is therefore a genuine finite abelian extension.  The
inverse of the Frobenius lift preserves this compositum, fixes the changed
factor, and acts on the standard factor by the direct unit parameter.  This
is the finite automorphism which the changed-uniformizer norm calculation
will identify with the actual local Artin symbol.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The copy of the ordinary standard multiplicative level inside the
completed level. -/
def padicCompletedStandardLevelField
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IntermediateField ℚ_[p] (padicCompletedLevelField p n) :=
  (padicStandardLevelEmbedding p n).fieldRange

/-- The ordinary standard level is equivalent to its image in the completed
level. -/
noncomputable def padicStandardLevelEquivCompletedStandardLevelField
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ≃ₐ[ℚ_[p]]
        padicCompletedStandardLevelField p n :=
  AlgEquiv.ofInjectiveField (padicStandardLevelEmbedding p n)

noncomputable instance
    padicCompletedStandardLevelField_finiteDimensional
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FiniteDimensional ℚ_[p]
      (padicCompletedStandardLevelField p n) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let : FiniteDimensional ℚ_[p]
      (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let e := padicStandardLevelEquivCompletedStandardLevelField p n
  exact e.toLinearEquiv.finiteDimensional

noncomputable instance
    padicCompletedStandardLevelField_isAbelianGalois
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsAbelianGalois ℚ_[p]
      (padicCompletedStandardLevelField p n) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let : IsAbelianGalois ℚ_[p] (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_isAbelianGalois (padicLocalField p)
      (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  exact IsAbelianGalois.of_algHom
    (padicStandardLevelEquivCompletedStandardLevelField p n).symm.toAlgHom

noncomputable instance
    padicCompletedChangedUniformizerFixedField_finiteDimensional
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    FiniteDimensional ℚ_[p]
      (padicCompletedChangedUniformizerFixedField p u n) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let : FiniteDimensional ℚ_[p]
      (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let e := padicChangedUniformizerLevelEquivCompletedFixedField p u n
  exact e.toLinearEquiv.finiteDimensional

noncomputable instance
    padicCompletedChangedUniformizerFixedField_isAbelianGalois
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsAbelianGalois ℚ_[p]
      (padicCompletedChangedUniformizerFixedField p u n) :=
  IsAbelianGalois.of_algHom
    (padicChangedUniformizerLevelEquivCompletedFixedField p u n).symm.toAlgHom

/-- The finite compositum of the standard level and the actual
changed-uniformizer fixed field inside the completed level. -/
def padicCompletedStandardChangedCompositum
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IntermediateField ℚ_[p] (padicCompletedLevelField p n) :=
  padicCompletedStandardLevelField p n ⊔
    padicCompletedChangedUniformizerFixedField p u n

noncomputable instance
    padicCompletedStandardChangedCompositum_finiteDimensional
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    FiniteDimensional ℚ_[p]
      (padicCompletedStandardChangedCompositum p u n) :=
  IntermediateField.finiteDimensional_sup
    (padicCompletedStandardLevelField p n)
    (padicCompletedChangedUniformizerFixedField p u n)

noncomputable instance
    padicCompletedStandardChangedCompositum_isAbelianGalois
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsAbelianGalois ℚ_[p]
      (padicCompletedStandardChangedCompositum p u n) :=
  AlgebraicNumberTheory.isAbelianGalois_sup ℚ_[p]
    (padicCompletedStandardLevelField p n)
    (padicCompletedChangedUniformizerFixedField p u n)

noncomputable instance
    padicCompletedStandardChangedCompositumChangedFieldAlgebra
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Algebra (padicCompletedChangedUniformizerFixedField p u n)
      (padicCompletedStandardChangedCompositum p u n) :=
  (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra

instance padicCompletedStandardChangedCompositum_changedFieldScalarTower
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsScalarTower ℚ_[p]
      (padicCompletedChangedUniformizerFixedField p u n)
      (padicCompletedStandardChangedCompositum p u n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The standard/changed compositum is also abelian Galois over its
changed-uniformizer factor.  Relative automorphisms embed faithfully into
the already commutative Galois group over `ℚ_p`. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_relative_isAbelianGalois
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsAbelianGalois
      (padicCompletedChangedUniformizerFixedField p u n)
      (padicCompletedStandardChangedCompositum p u n) :=
  IsAbelianGalois.tower_top ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)
    (padicCompletedStandardChangedCompositum p u n)

/-- The standard finite level embedded into the finite standard/changed
compositum. -/
noncomputable def padicStandardLevelToCompletedChangedCompositum
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      →ₐ[ℚ_[p]]
        padicCompletedStandardChangedCompositum p u n :=
  (padicStandardLevelEmbedding p n).codRestrict
    (padicCompletedStandardChangedCompositum p u n).toSubalgebra
    (fun x =>
      (show padicCompletedStandardLevelField p n ≤
          padicCompletedStandardChangedCompositum p u n from le_sup_left)
      (show padicStandardLevelEmbedding p n x ∈
          padicCompletedStandardLevelField p n from
        ⟨x, rfl⟩))

/-- The changed fixed field included into the finite standard/changed
compositum. -/
noncomputable def
    padicCompletedChangedFixedFieldToStandardChangedCompositum
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedChangedUniformizerFixedField p u n
      →ₐ[ℚ_[p]]
        padicCompletedStandardChangedCompositum p u n :=
  IntermediateField.inclusion le_sup_right

/-- The inverse-unit Frobenius inverse carries the standard completed copy
to itself. -/
theorem
    padicCompletedChangedUniformizerFrobenius_symm_map_standard_le
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedStandardLevelField p n).map
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv
          p u n).symm.toAlgHom ≤
      padicCompletedStandardLevelField p n := by
  rw [IntermediateField.map_le_iff_le_comap]
  intro x hx
  change
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm x ∈
      padicCompletedStandardLevelField p n
  change x ∈ (padicStandardLevelEmbedding p n).fieldRange at hx
  change
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm x ∈
      (padicStandardLevelEmbedding p n).fieldRange
  rw [AlgHom.mem_fieldRange] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine
    ⟨standardLubinTateUnitParameterAlgEquiv
        (padicLocalField p)
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u) y, ?_⟩
  exact
    (padicCompletedInverseUnitFrobeniusLiftEquiv_standardLevelEmbedding
      p n u y).symm

/-- Every element of the changed fixed field is fixed by the inverse of its
defining Frobenius lift. -/
theorem
    padicCompletedChangedUniformizerFrobenius_symm_fixed
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : padicCompletedChangedUniformizerFixedField p u n) :
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm
      (x : padicCompletedLevelField p n) =
        x := by
  have hxFixed :
      padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n
          (x : padicCompletedLevelField p n) =
        x := by
    have hxmem := x.property
    change
      (x : padicCompletedLevelField p n) ∈
        IntermediateField.fixedField
          (padicCompletedChangedUniformizerFrobeniusSubgroup p u n)
      at hxmem
    rw [IntermediateField.mem_fixedField_iff] at hxmem
    exact hxmem
      (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n)
      (Subgroup.mem_zpowers
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n))
  calc
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm
        (x : padicCompletedLevelField p n) =
      (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n x) := by
          rw [hxFixed]
    _ = x :=
      (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm_apply_apply x

/-- The inverse defining Frobenius carries the changed fixed field to
itself. -/
theorem
    padicCompletedChangedUniformizerFrobenius_symm_map_fixedField_le
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedChangedUniformizerFixedField p u n).map
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv
          p u n).symm.toAlgHom ≤
      padicCompletedChangedUniformizerFixedField p u n := by
  rw [IntermediateField.map_le_iff_le_comap]
  intro x hx
  change
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm x ∈
      padicCompletedChangedUniformizerFixedField p u n
  have hfixed :=
    padicCompletedChangedUniformizerFrobenius_symm_fixed p u n
      ⟨x, hx⟩
  rw [hfixed]
  exact hx

/-- The inverse defining Frobenius preserves the finite standard/changed
compositum. -/
theorem
    padicCompletedChangedUniformizerFrobenius_symm_map_compositum_le
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedStandardChangedCompositum p u n).map
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv
          p u n).symm.toAlgHom ≤
      padicCompletedStandardChangedCompositum p u n := by
  rw [padicCompletedStandardChangedCompositum,
    IntermediateField.map_sup]
  exact sup_le_sup
    (padicCompletedChangedUniformizerFrobenius_symm_map_standard_le
      p u n)
    (padicCompletedChangedUniformizerFrobenius_symm_map_fixedField_le
      p u n)

/-- The inverse defining Frobenius restricted to the genuine finite
standard/changed compositum. -/
noncomputable def padicCompletedChangedUniformizerArtinCandidateAlgHom
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedStandardChangedCompositum p u n
      →ₐ[ℚ_[p]]
        padicCompletedStandardChangedCompositum p u n :=
  (((padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm.toAlgHom).comp
        (padicCompletedStandardChangedCompositum p u n).val).codRestrict
    (padicCompletedStandardChangedCompositum p u n).toSubalgebra
    (fun x => by
      apply
        padicCompletedChangedUniformizerFrobenius_symm_map_compositum_le
          p u n
      rw [IntermediateField.mem_map]
      exact ⟨x, x.property, rfl⟩)

/-- The finite Artin candidate is an automorphism. -/
noncomputable def padicCompletedChangedUniformizerArtinCandidate
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedStandardChangedCompositum p u n
      ≃ₐ[ℚ_[p]]
        padicCompletedStandardChangedCompositum p u n := by
  let f :=
    padicCompletedChangedUniformizerArtinCandidateAlgHom p u n
  apply AlgEquiv.ofBijective f
  refine ⟨f.injective, ?_⟩
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) rfl).mp f.injective

/-- On the standard factor, the finite Artin candidate is the direct
unit-parameter automorphism. -/
@[simp]
theorem
    padicCompletedChangedUniformizerArtinCandidate_standardLevel
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    padicCompletedChangedUniformizerArtinCandidate p u n
        (padicStandardLevelToCompletedChangedCompositum p u n x) =
      padicStandardLevelToCompletedChangedCompositum p u n
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x) := by
  apply Subtype.ext
  exact
    padicCompletedInverseUnitFrobeniusLiftEquiv_standardLevelEmbedding
      p n u x

/-- On the changed factor, the finite Artin candidate is the identity. -/
@[simp]
theorem
    padicCompletedChangedUniformizerArtinCandidate_fixedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : padicCompletedChangedUniformizerFixedField p u n) :
    padicCompletedChangedUniformizerArtinCandidate p u n
        (padicCompletedChangedFixedFieldToStandardChangedCompositum
          p u n x) =
      padicCompletedChangedFixedFieldToStandardChangedCompositum
        p u n x := by
  apply Subtype.ext
  exact
    padicCompletedChangedUniformizerFrobenius_symm_fixed p u n x

/-- The finite Artin candidate as an automorphism over the changed fixed
field that it fixes pointwise. -/
noncomputable def
    padicCompletedChangedUniformizerRelativeArtinCandidate
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedStandardChangedCompositum p u n
      ≃ₐ[padicCompletedChangedUniformizerFixedField p u n]
        padicCompletedStandardChangedCompositum p u n where
  __ := (padicCompletedChangedUniformizerArtinCandidate p u n).toRingEquiv
  commutes' x :=
    padicCompletedChangedUniformizerArtinCandidate_fixedField
      p u n x

/-- Forgetting the changed-field scalar structure recovers the original
finite candidate. -/
@[simp]
theorem padicCompletedChangedUniformizerRelativeArtinCandidate_apply
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : padicCompletedStandardChangedCompositum p u n) :
    padicCompletedChangedUniformizerRelativeArtinCandidate p u n x =
      padicCompletedChangedUniformizerArtinCandidate p u n x :=
  rfl

end LubinTate

end
