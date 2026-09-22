/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
/-!
# Global norm residue on actual fixed fields

An abstract finite abelian subextension of the rational absolute Galois
group determines an actual finite abelian extension between its two
fixed number fields.  This file transports the abstract norm-residue
symbol directly to the ordinary idele-class norm quotient of those
fixed fields.

Keeping this construction in one ambient separable closure is essential
for the norm--restriction diagrams: no independently chosen embedding of
either field is introduced.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

/-- The algebra structure on the rational separable closure induced by a
specified rational field embedding.  It is deliberately not an instance:
different embeddings of the same field need not induce definitionally equal
algebra structures. -/
@[reducible]
noncomputable def rationalEmbeddingSeparableClosureAlgebra
    {F : Type} [Field F] [Algebra ℚ F]
    (i : F →ₐ[ℚ] SeparableClosure ℚ) :
    Algebra F (SeparableClosure ℚ) :=
  i.toRingHom.toAlgebra

/-- Two rational embeddings of the same number field into the fixed
rational separable closure differ by an automorphism of that
separable closure. -/
theorem exists_numberFieldEmbeddingComparisonAutomorphism
    {F : Type} [Field F] [NumberField F]
    (i j : F →ₐ[ℚ] SeparableClosure ℚ) :
    ∃ σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ,
      ∀ x : F, σ (i x) = j x := by
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    rationalEmbeddingSeparableClosureAlgebra i
  let hScalarTower : IsScalarTower ℚ F (SeparableClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  let hSeparable : Algebra.IsSeparable F (SeparableClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      ℚ F (SeparableClosure ℚ)
  obtain ⟨φ, hφ⟩ :=
    (IsSepClosed.surjective_domRestrict_of_isSeparable
      (K := ℚ) (L := F)
      (M := SeparableClosure ℚ)
      (E := SeparableClosure ℚ)) j
  let σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ :=
    AlgEquiv.ofBijective φ
      (Normal.toIsAlgebraic.algHom_bijective₂
        φ (AlgHom.id ℚ (SeparableClosure ℚ))).1
  refine ⟨σ, ?_⟩
  intro x
  have hx :=
    congrArg (fun ψ : F →ₐ[ℚ] SeparableClosure ℚ => ψ x) hφ
  exact hx

/-- The canonical comparison automorphism between two rational
embeddings of one number field into the fixed separable closure. -/
noncomputable def numberFieldEmbeddingComparisonAutomorphism
    {F : Type} [Field F] [NumberField F]
    (i j : F →ₐ[ℚ] SeparableClosure ℚ) :
    SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ :=
  Classical.choose
    (exists_numberFieldEmbeddingComparisonAutomorphism i j)

/-- The comparison automorphism carries the first embedded copy of the
number field to the second one pointwise. -/
@[simp]
theorem numberFieldEmbeddingComparisonAutomorphism_apply
    {F : Type} [Field F] [NumberField F]
    (i j : F →ₐ[ℚ] SeparableClosure ℚ)
    (x : F) :
    numberFieldEmbeddingComparisonAutomorphism i j (i x) =
      j x :=
  Classical.choose_spec
    (exists_numberFieldEmbeddingComparisonAutomorphism i j) x

/-- Conjugating the fixing subgroup of one embedded copy of a number
field by the comparison automorphism gives the fixing subgroup of the
other embedded copy. -/
theorem conjugateClosedFixingSubgroup_embeddingRange
    {F : Type} [Field F] [NumberField F]
    (i j : F →ₐ[ℚ] SeparableClosure ℚ) :
    conjugateClosedSubgroup
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) i.fieldRange)
        (numberFieldEmbeddingComparisonAutomorphism j i) =
      RamificationTheory.closedFixingSubgroup
        ℚ (SeparableClosure ℚ) j.fieldRange := by
  let s :=
    numberFieldEmbeddingComparisonAutomorphism j i
  ext τ
  change
    τ ∈ conjugateClosedSubgroup
        (closedFixingSubgroup ℚ (SeparableClosure ℚ) i.fieldRange) s ↔
      τ ∈ closedFixingSubgroup ℚ (SeparableClosure ℚ) j.fieldRange
  rw [conjugateClosedSubgroup_mem]
  change
    s * τ * s⁻¹ ∈ i.fieldRange.fixingSubgroup ↔
      τ ∈ j.fieldRange.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    rcases hx with ⟨y, rfl⟩
    have hi := h (i y) ⟨y, rfl⟩
    have hs :
        s (j y) = i y :=
      numberFieldEmbeddingComparisonAutomorphism_apply j i y
    change s (τ (s.symm (i y))) = i y at hi
    have hpre : s.symm (i y) = j y := by
      rw [← hs, s.symm_apply_apply]
    rw [hpre, ← hs] at hi
    exact s.injective hi
  · intro h x hx
    rcases hx with ⟨y, rfl⟩
    have hj := h (j y) ⟨y, rfl⟩
    have hs :
        s (j y) = i y :=
      numberFieldEmbeddingComparisonAutomorphism_apply j i y
    change s (τ (s.symm (i y))) = i y
    have hpre : s.symm (i y) = j y := by
      rw [← hs, s.symm_apply_apply]
    rw [hpre, hj, hs]

section EmbeddedNumberFieldRealization

local instance numberFieldEmbeddedIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance numberFieldEmbeddedIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The lower embedding obtained by restricting an explicitly supplied
embedding of the top field into the rational separable closure. -/
noncomputable def numberFieldEmbeddedLowerEmbedding
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  j.comp (IsScalarTower.toAlgHom ℚ K L)

/-- The exact algebra structure on the rational separable closure induced by
the lower embedding of an explicitly embedded number-field tower.  Keeping
this as a reducible definition lets every use of the associated separable-
closure equivalence share one definitionally identical algebra structure. -/
@[reducible]
noncomputable def numberFieldEmbeddedSeparableClosureAlgebra
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Algebra K (SeparableClosure ℚ) :=
  rationalEmbeddingSeparableClosureAlgebra
    (numberFieldEmbeddedLowerEmbedding K L j)

/-- The fixing subgroup of the explicitly embedded lower field. -/
abbrev numberFieldEmbeddedBaseSubgroup
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedLowerEmbedding K L j).fieldRange

/-- The fixing subgroup of the explicitly embedded top field. -/
abbrev numberFieldEmbeddedTopSubgroup
    (_K L : Type) [Field L] [NumberField L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ) j.fieldRange

/-- The top fixing subgroup lies in the lower fixing subgroup. -/
theorem numberFieldEmbeddedTopSubgroup_le_baseSubgroup
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (numberFieldEmbeddedTopSubgroup K L j).toSubgroup ≤
      (numberFieldEmbeddedBaseSubgroup K L j).toSubgroup := by
  change
    j.fieldRange.fixingSubgroup ≤
      (numberFieldEmbeddedLowerEmbedding K L j).fieldRange.fixingSubgroup
  apply
    (numberFieldEmbeddedLowerEmbedding K L j).fieldRange.fixingSubgroup_le
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨algebraMap K L y, rfl⟩

/-- The separable closure of the actual lower field, identified with
the rational separable closure carrying the algebra structure induced
by an explicit compatible embedding. -/
noncomputable def numberFieldEmbeddedSeparableClosureEquiv
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldEmbeddedSeparableClosureAlgebra K L j
    SeparableClosure K ≃ₐ[K] SeparableClosure ℚ := by
  letI : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  letI hScalarTower : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq'
      (numberFieldEmbeddedLowerEmbedding K L j).comp_algebraMap.symm
  letI hseparable : Algebra.IsSeparable K (SeparableClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      ℚ K (SeparableClosure ℚ)
  letI hSepClosure : IsSepClosure K (SeparableClosure ℚ) :=
    ⟨IsSepClosure.sep_closed ℚ, hseparable⟩
  exact
    IsSepClosure.equiv K
      (SeparableClosure K) (SeparableClosure ℚ)

/-- The relative subgroup arising from an explicit compatible
number-field embedding is normal. -/
theorem numberFieldEmbeddedExtensionSubgroup_normal
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).Normal := by
  let i := numberFieldEmbeddedLowerEmbedding K L j
  let hAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  let e := numberFieldEmbeddedSeparableClosureEquiv K L j
  change
    (CyclicCohomology.extensionSubgroup
      (closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (AlgHom.fieldRange i))
      (closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (AlgHom.fieldRange j)) _).Normal
  exact ambientEmbeddedExtensionSubgroup_normal ℚ K L j e

/-- The normality witness for an explicitly embedded tower, registered at
the precise subgroup used by the downstream quotient constructions. -/
noncomputable local instance
    numberFieldEmbeddedExtensionSubgroupNormal
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).Normal :=
  numberFieldEmbeddedExtensionSubgroup_normal K L j

/-- The relative quotient arising from an explicit compatible
number-field embedding is finite. -/
theorem numberFieldEmbeddedExtensionQuotient_finite
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L j).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) := by
  let i := numberFieldEmbeddedLowerEmbedding K L j
  let hAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  let e := numberFieldEmbeddedSeparableClosureEquiv K L j
  change
    Finite
      ((closedFixingSubgroup ℚ (SeparableClosure ℚ)
          (AlgHom.fieldRange i)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (closedFixingSubgroup ℚ (SeparableClosure ℚ)
            (AlgHom.fieldRange i))
          (closedFixingSubgroup ℚ (SeparableClosure ℚ)
            (AlgHom.fieldRange j)) _)
  exact ambientEmbeddedExtensionQuotient_finite ℚ K L j e

/-- The relative-index witness for an explicitly embedded tower, registered
at the exact quotient consumed by `FiniteNormQuotient`. -/
noncomputable local instance
    numberFieldEmbeddedExtensionQuotientFinite
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L j).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  numberFieldEmbeddedExtensionQuotient_finite K L j

/-- The finite abstract field determined by the lower member of an
explicitly embedded number-field tower. -/
noncomputable abbrev numberFieldEmbeddedFiniteAbstractField
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  field := numberFieldEmbeddedBaseSubgroup K L j
  finite := by
    simpa only [numberFieldEmbeddedBaseSubgroup] using
      (ambientEmbeddedAbsoluteQuotientFinite
        ℚ K (numberFieldEmbeddedLowerEmbedding K L j))

/-- The absolute-index witness for the lower member of an explicitly embedded
tower, registered at its specialized quotient type. -/
noncomputable local instance
    numberFieldEmbeddedAbsoluteQuotientFinite
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          (numberFieldEmbeddedBaseSubgroup K L j)
          (le_baseField
            (numberFieldEmbeddedBaseSubgroup K L j))) :=
  (numberFieldEmbeddedFiniteAbstractField K L j).finite

/-- The finite Galois subextension determined by an explicitly embedded
number-field tower. -/
noncomputable abbrev numberFieldEmbeddedFiniteGaloisSubextension
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteGaloisSubextension
      (numberFieldEmbeddedBaseSubgroup K L j) where
  field := numberFieldEmbeddedTopSubgroup K L j
  below := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  normal := numberFieldEmbeddedExtensionSubgroup_normal K L j
  finite := numberFieldEmbeddedExtensionQuotient_finite K L j

/-- Shared finite-dimensional data for the fixed field of the lower subgroup
in an explicitly embedded number-field tower. -/
noncomputable local instance
    numberFieldEmbeddedAbstractFixedFieldFiniteDimensional
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j)) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L j)
    (numberFieldEmbeddedAbsoluteQuotientFinite K L j)

/-- Shared relative finite-dimensional data for the two fixed fields of an
explicitly embedded number-field tower. -/
noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldFiniteDimensional
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
    (numberFieldEmbeddedAbsoluteQuotientFinite K L j)
    (numberFieldEmbeddedExtensionQuotientFinite K L j)

local instance numberFieldEmbeddedAbstractFixedFieldScalarTower
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldAbsoluteFiniteDimensional
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup K L j))
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))

noncomputable local instance
    numberFieldEmbeddedAbstractFixedFieldNumberField
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j)) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup K L j))

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldNumberField
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsFiniteDimensional
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).restrictScalars ℚ) := by
  change FiniteDimensional ℚ
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))
  infer_instance

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsNumberField
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).restrictScalars ℚ) :=
  NumberField.of_module_finite ℚ _

/-- Inclusion of abstract fixed fields gives the scalar-restricted relative fixed field an algebra
structure over the base fixed field. -/
noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsAlgebra

    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Algebra
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).restrictScalars ℚ) :=
  (IntermediateField.inclusion
    (abstractFixedField_le ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))).toRingHom.toAlgebra

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldIsGalois
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
    (numberFieldEmbeddedExtensionSubgroupNormal K L j)

/-- The quotient of the two explicitly embedded fixing subgroups is
the actual relative Galois group. -/
noncomputable def
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (numberFieldEmbeddedFiniteGaloisSubextension K L j).extensionQuotient ≃*
      Gal(L / K) := by
  let i := numberFieldEmbeddedLowerEmbedding K L j
  letI hAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  let e := numberFieldEmbeddedSeparableClosureEquiv K L j
  let H₀ :=
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change j.fieldRange.fixingSubgroup ≤ i.fieldRange.fixingSubgroup
    apply i.fieldRange.fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap K L y, rfl⟩
  letI : (CyclicCohomology.extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal ℚ K L j e
  change
    (H₀.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H₀ J₀ hJH) ≃*
      Gal(L / K)
  exact ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ K L j e

/-- The original lower field is canonically equivalent to the fixed
field of its explicitly embedded fixing subgroup. -/
noncomputable def numberFieldEmbeddedAbstractBaseFieldEquiv
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    K ≃ₐ[ℚ]
      abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j) :=
  (numberFieldEmbeddedLowerEmbedding K L j).equivFieldRange.trans
    (IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_fixingSubgroup
        (numberFieldEmbeddedLowerEmbedding K L j).fieldRange).symm)

/-- The original top field is canonically equivalent to the relative
fixed field of its explicitly embedded fixing subgroup. -/
noncomputable def numberFieldEmbeddedAbstractTopFieldEquiv
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    L ≃ₐ[ℚ]
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup
          K L j)).restrictScalars ℚ :=
  j.equivFieldRange.trans
    (IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_fixingSubgroup j.fieldRange).symm)

/-- The two explicit fixed-field equivalences commute with the tower
algebra maps. -/
theorem numberFieldEmbeddedAbstractFieldEquiv_algebraMap
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (x : K) :
    numberFieldEmbeddedAbstractTopFieldEquiv K L j
        (algebraMap K L x) =
      algebraMap
        (abstractFixedField ℚ (SeparableClosure ℚ)
          (numberFieldEmbeddedBaseSubgroup K L j))
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))
        (numberFieldEmbeddedAbstractBaseFieldEquiv K L j x) := by
  apply Subtype.ext
  rfl

/-- The ordinary idele class group of the explicitly embedded lower
field, transported to the fixed part of the rational absolute
idele-class representation. -/
noncomputable def numberFieldEmbeddedIdeleClassEquivAmbientFixed
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Additive (IdeleClassGroup K) ≃+
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K L j) := by
  let H := numberFieldEmbeddedBaseSubgroup K L j
  exact
    (MulEquiv.toAdditive
      (ideleClassCongr
        (numberFieldEmbeddedAbstractBaseFieldEquiv K L j))).trans
      (rationalAbstractFixedFieldIdeleClassEquivFixed H)

/-- The abstract finite norm quotient of an explicitly embedded tower
is its genuine ordinary idele-class norm quotient. -/
noncomputable def
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K L j)
        (numberFieldEmbeddedTopSubgroup K L j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j) ≃+
      Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) := by
  let hnormal :=
    numberFieldEmbeddedExtensionSubgroupNormal K L j
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let J := numberFieldEmbeddedTopSubgroup K L j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let fixedFieldEquiv :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
      H J hJH hnormal
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  exact
    fixedFieldEquiv.trans
      (MulEquiv.toAdditive actualFieldEquiv.symm)

private theorem numberFieldEmbeddedOrdinaryNormQuotientCongr_symm_mk
    {K₀ L₀ K₁ L₁ : Type}
    [Field K₀] [NumberField K₀]
    [Field L₀] [NumberField L₀] [Algebra K₀ L₀]
    [Field K₁] [NumberField K₁]
    [Field L₁] [NumberField L₁] [Algebra K₁ L₁]
    (eK : K₀ ≃ₐ[ℚ] K₁)
    (eL : L₀ ≃ₐ[ℚ] L₁)
    (h : ∀ x : K₀,
      eL (algebraMap K₀ L₀ x) =
        algebraMap K₁ L₁ (eK x))
    (c : IdeleClassGroup K₁) :
    (ordinaryIdeleClassNormQuotientCongrOfAlgEquiv eK eL h).symm
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K₁ L₁).range c) =
      QuotientGroup.mk'
        (_root_.ideleClassNorm K₀ L₀).range
        ((ideleClassCongr eK).symm c) := by
  let e := ordinaryIdeleClassNormQuotientCongrOfAlgEquiv eK eL h
  apply e.injective
  rw [e.apply_symm_apply,
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk,
    MulEquiv.apply_symm_apply]

private noncomputable def numberFieldEmbeddedFiniteNormClassPublicValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
        K L j
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
          a)

private noncomputable def numberFieldEmbeddedFiniteNormClassExpectedValue

    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  Additive.ofMul
    (QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range
      (Additive.toMul
        ((numberFieldEmbeddedIdeleClassEquivAmbientFixed K L j).symm a)))

private noncomputable def
    numberFieldEmbeddedFiniteNormClassDirectComparisonValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  let hnormal :=
    numberFieldEmbeddedExtensionSubgroupNormal K L j
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let J := numberFieldEmbeddedTopSubgroup K L j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let fixedFieldEquiv :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
      H J hJH hnormal
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  exact
    MulEquiv.toAdditive actualFieldEquiv.symm
      (fixedFieldEquiv
        (finiteNormClass rationalIdeleClassRepresentation
          H J hJH a))

private theorem
    numberFieldEmbeddedFiniteNormClassPublicValue_eq_directComparison
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedFiniteNormClassPublicValue K L j a =
      numberFieldEmbeddedFiniteNormClassDirectComparisonValue K L j a := by
  unfold numberFieldEmbeddedFiniteNormClassPublicValue
  unfold numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
  unfold numberFieldEmbeddedFiniteNormClassDirectComparisonValue
  rfl

private noncomputable def numberFieldEmbeddedActualNormClassRepresentativeValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hJH
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  exact
    Additive.ofMul
      (actualFieldEquiv.symm
        (QuotientGroup.mk'
          (_root_.ideleClassNorm F E).range
          (Additive.toMul
            ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm a))))

private theorem
    numberFieldEmbeddedFiniteNormClassDirectComparison_eq_actualValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedFiniteNormClassDirectComparisonValue K L j a =
      numberFieldEmbeddedActualNormClassRepresentativeValue K L j a := by
  let hnormal := numberFieldEmbeddedExtensionSubgroupNormal K L j
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let J := numberFieldEmbeddedTopSubgroup K L j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  have hfixed :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
      H J hJH hnormal a
  unfold numberFieldEmbeddedFiniteNormClassDirectComparisonValue
  unfold numberFieldEmbeddedActualNormClassRepresentativeValue
  exact congrArg (MulEquiv.toAdditive actualFieldEquiv.symm) hfixed

private theorem numberFieldEmbeddedActualNormClassRepresentativeValue_eq_expected
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedActualNormClassRepresentativeValue K L j a =
      numberFieldEmbeddedFiniteNormClassExpectedValue K L j a := by
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hJH
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  let c : IdeleClassGroup F :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm a)
  unfold numberFieldEmbeddedActualNormClassRepresentativeValue
  unfold numberFieldEmbeddedFiniteNormClassExpectedValue
  change
    Additive.ofMul
        (actualFieldEquiv.symm
          (QuotientGroup.mk'
            (_root_.ideleClassNorm F E).range c)) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range
          ((ideleClassCongr
            (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)).symm c))
  exact
    congrArg Additive.ofMul
      (numberFieldEmbeddedOrdinaryNormQuotientCongr_symm_mk
        (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
        (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
        (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j) c)

/-- On a finite norm-class representative, the explicit fixed-field
comparison is the genuine ordinary idele-class quotient. -/
@[simp]
theorem
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient K L j
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j) a) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range
          (Additive.toMul
            ((numberFieldEmbeddedIdeleClassEquivAmbientFixed K L j).symm a))) := by
  change
    numberFieldEmbeddedFiniteNormClassPublicValue K L j a =
      numberFieldEmbeddedFiniteNormClassExpectedValue K L j a
  exact
    (numberFieldEmbeddedFiniteNormClassPublicValue_eq_directComparison
      K L j a).trans
      ((numberFieldEmbeddedFiniteNormClassDirectComparison_eq_actualValue
        K L j a).trans
        (numberFieldEmbeddedActualNormClassRepresentativeValue_eq_expected
          K L j a))

/-- On an ordinary idele class, the explicit fixed-part realization
followed by the abstract finite norm-class map is the genuine quotient
class modulo the ordinary idele-class norm. -/
theorem
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K) :
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient K L j
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
          (numberFieldEmbeddedIdeleClassEquivAmbientFixed
            K L j (Additive.ofMul c))) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c) := by
  simpa only [AddEquiv.symm_apply_apply, toMul_ofMul] using
    (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
      K L j
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K L j (Additive.ofMul c)))

variable [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The abelianized quotient of the explicitly embedded tower is the
actual abelian Galois group. -/
noncomputable def
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Additive
      (Abelianization
        (numberFieldEmbeddedFiniteGaloisSubextension K L j).extensionQuotient) ≃+
      Additive Gal(L / K) :=
  MulEquiv.toAdditive
    ((MulEquiv.abelianizationCongr
      (numberFieldEmbeddedExtensionQuotientEquivGaloisGroup K L j)).trans
        (Abelianization.equivOfComm :
          Gal(L / K) ≃*
            Abelianization Gal(L / K)).symm)

/-- The actual global norm-residue equivalence constructed from an
explicit compatible embedding of a finite abelian number-field
extension into the rational separable closure. -/
noncomputable def globalNormResidueEquivOfEmbedding
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃+
      Additive Gal(L / K) := by
  let eNorm :
      FiniteNormQuotient rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j) ≃+
        Additive
          (Abelianization
            (numberFieldEmbeddedFiniteGaloisSubextension K L j).extensionQuotient) :=
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      (numberFieldEmbeddedFiniteAbstractField K L j)
      (numberFieldEmbeddedFiniteGaloisSubextension K L j)
  exact
    (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
        K L j).symm.trans
      (eNorm.trans
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L j))

/-- The explicit-embedding norm-residue equivalence on a finite norm class. -/
theorem globalNormResidueEquivOfEmbedding_finiteNormClass
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :
    globalNormResidueEquivOfEmbedding K L j
        (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K L j x) =
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup K L j
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K L j)
          (numberFieldEmbeddedFiniteGaloisSubextension K L j) x) := by
  simp only [globalNormResidueEquivOfEmbedding, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]

/-- The global norm-residue homomorphism obtained from an explicit
compatible embedding. -/
noncomputable def globalNormResidueMonoidHomOfEmbedding
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    IdeleClassGroup K →* Gal(L / K) := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Gal(L / K) :=
    AddEquiv.toMultiplicative
      (globalNormResidueEquivOfEmbedding K L j)
  exact
    e.toMonoidHom.comp
      (QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range)

/-- Evaluation of the explicit-embedding global norm-residue map is
the abstract norm-residue symbol evaluated on the corresponding genuine
fixed-part finite norm class. -/
@[simp]
theorem globalNormResidueMonoidHomOfEmbedding_apply
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K) :
    globalNormResidueMonoidHomOfEmbedding K L j c =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L j
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K L j)
            (numberFieldEmbeddedFiniteGaloisSubextension K L j)
            (finiteNormClass rationalIdeleClassRepresentation
              (numberFieldEmbeddedBaseSubgroup K L j)
              (numberFieldEmbeddedTopSubgroup K L j)
              (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
              (numberFieldEmbeddedIdeleClassEquivAmbientFixed
                K L j (Additive.ofMul c))))) := by
  have hclass :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L j c
  change
    Additive.toMul
      (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
        K L j
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K L j)
          (numberFieldEmbeddedFiniteGaloisSubextension K L j)
          ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
            K L j).symm
            (Additive.ofMul
              (QuotientGroup.mk'
                (_root_.ideleClassNorm K L).range c))))) =
      _
  rw [← hclass,
    (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
      K L j).symm_apply_apply]

omit [FiniteDimensional K L] [IsAbelianGalois K L] in
/-- The ambient-fixed idèle-class transport for the standard embedding is
the same map as the transport for an explicitly supplied embedding.  This
comparison is kept at the transport boundary, before forming norm quotients
or applying reciprocity. -/
theorem numberFieldTowerIdeleClassEquivAmbientFixed_eq_embedded_standard :
    numberFieldTowerIdeleClassEquivAmbientFixed K L =
      numberFieldEmbeddedIdeleClassEquivAmbientFixed K L
        (numberFieldSeparableClosureEmbedding L) := by
  let j := numberFieldSeparableClosureEmbedding L
  have hBase :
      numberFieldTowerAbstractBaseFieldEquiv K L =
        numberFieldEmbeddedAbstractBaseFieldEquiv K L j := by
    rfl
  unfold numberFieldTowerIdeleClassEquivAmbientFixed
    numberFieldEmbeddedIdeleClassEquivAmbientFixed
  rw [hBase]
  dsimp only
  congr 1

/- At the chosen embedding, both constructions use the same fixed tower and
abstract reciprocity data.  We compare their values on the particular fixed
idele class needed below; the two implementations of the finite norm-quotient
equivalence are deliberately not compared as dependent structures. -/
private theorem numberFieldTowerNormResidueValue_eq_embedded_standard
    (c : IdeleClassGroup K) :
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L)
          (finiteNormClass rationalIdeleClassRepresentation
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
            (numberFieldTowerIdeleClassEquivAmbientFixed K L (Additive.ofMul c)))) =
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
        K L (numberFieldSeparableClosureEmbedding L)
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K L
            (numberFieldSeparableClosureEmbedding L))
          (numberFieldEmbeddedFiniteGaloisSubextension K L
            (numberFieldSeparableClosureEmbedding L))
          (finiteNormClass rationalIdeleClassRepresentation
            (numberFieldEmbeddedBaseSubgroup K L
              (numberFieldSeparableClosureEmbedding L))
            (numberFieldEmbeddedTopSubgroup K L
              (numberFieldSeparableClosureEmbedding L))
            (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L
              (numberFieldSeparableClosureEmbedding L))
            (numberFieldEmbeddedIdeleClassEquivAmbientFixed K L
              (numberFieldSeparableClosureEmbedding L) (Additive.ofMul c)))) := by
  have hIdeleClassEquiv :
      numberFieldTowerIdeleClassEquivAmbientFixed K L =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed K L
          (numberFieldSeparableClosureEmbedding L) := by
    exact numberFieldTowerIdeleClassEquivAmbientFixed_eq_embedded_standard K L
  have hFiniteAbstractField :
      numberFieldTowerReciprocityFiniteAbstractField K L =
        numberFieldEmbeddedFiniteAbstractField K L
          (numberFieldSeparableClosureEmbedding L) := by
    rfl
  have hSubextension :
      numberFieldTowerFiniteGaloisSubextension K L =
        numberFieldEmbeddedFiniteGaloisSubextension K L
          (numberFieldSeparableClosureEmbedding L) := by
    rfl
  have hGaloisComparison :
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L =
        numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L (numberFieldSeparableClosureEmbedding L) := by
    rfl
  simp only [← hGaloisComparison]
  cases hFiniteAbstractField
  cases hSubextension
  rw [← hIdeleClassEquiv]
  rfl

/-- At the standard embedding, the two global norm-residue equivalences
agree on the actual norm quotient.  The comparison is extensional: it uses
surjectivity of the quotient map and the established evaluation formulas,
not definitional equality of the two quotient constructions. -/
theorem globalNormResidueEquiv_eq_ofEmbedding_standard :
    globalNormResidueEquiv K L =
      globalNormResidueEquivOfEmbedding K L
        (numberFieldSeparableClosureEmbedding L) := by
  apply AddEquiv.ext
  intro q
  obtain ⟨c, hc⟩ :=
    QuotientGroup.mk'_surjective
      (_root_.ideleClassNorm K L).range (Additive.toMul q)
  have hq :
      Additive.ofMul
          (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c) = q :=
    Additive.toMul.injective hc
  rw [← hq]
  have hTower :=
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L c
  have hEmbedded :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L (numberFieldSeparableClosureEmbedding L) c
  conv_lhs =>
    rw [← hTower, globalNormResidueEquiv_finiteNormClass]
  conv_rhs =>
    rw [← hEmbedded, globalNormResidueEquivOfEmbedding_finiteNormClass]
  exact numberFieldTowerNormResidueValue_eq_embedded_standard K L c

/-- The existing global norm-residue map is the explicit-embedding
construction for the standard chosen embedding of the top field. -/
theorem globalNormResidueMonoidHom_eq_ofEmbedding_standard :
    globalNormResidueMonoidHom K L =
      globalNormResidueMonoidHomOfEmbedding K L
        (numberFieldSeparableClosureEmbedding L) := by
  apply MonoidHom.ext
  intro c
  apply Additive.toMul.injective
  change
    globalNormResidueEquiv K L
        (Additive.ofMul
          (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c)) =
      globalNormResidueEquivOfEmbedding K L
        (numberFieldSeparableClosureEmbedding L)
        (Additive.ofMul
          (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c))
  exact congrArg
    (fun e :
      Additive
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) ≃+
        Additive (Gal(L / K)) =>
      e (Additive.ofMul
        (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c)))
    (globalNormResidueEquiv_eq_ofEmbedding_standard K L)

end EmbeddedNumberFieldRealization

section EmbeddedNumberFieldRestriction

variable
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']

/-- A compatible common embedding reverses the inclusion of the two base
fields into an inclusion of their fixing subgroups. -/
theorem numberFieldEmbeddedBaseSubgroup_le_of_tower
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    (numberFieldEmbeddedBaseSubgroup K' L' j).toSubgroup ≤
      (numberFieldEmbeddedBaseSubgroup K L jLower).toSubgroup := by
  dsimp only
  change
    (numberFieldEmbeddedLowerEmbedding K' L' j).fieldRange.fixingSubgroup ≤
      (numberFieldEmbeddedLowerEmbedding K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))).fieldRange.fixingSubgroup
  apply
    (numberFieldEmbeddedLowerEmbedding K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L'))).fieldRange.fixingSubgroup_le
  intro x hx
  rcases hx with ⟨y, rfl⟩
  refine ⟨algebraMap K K' y, ?_⟩
  change
    j (algebraMap K' L' (algebraMap K K' y)) =
      j (algebraMap L L' (algebraMap K L y))
  rw [← IsScalarTower.algebraMap_apply K K' L',
    ← IsScalarTower.algebraMap_apply K L L']

omit [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Algebra K K'] [Algebra K L] [Algebra K L'] [Algebra K' L']
    [IsScalarTower K K' L'] [IsScalarTower K L L'] in
/-- A compatible common embedding reverses the inclusion of the two top
fields into an inclusion of their fixing subgroups. -/
theorem numberFieldEmbeddedTopSubgroup_le_of_tower
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    (numberFieldEmbeddedTopSubgroup K' L' j).toSubgroup ≤
      (numberFieldEmbeddedTopSubgroup K L jLower).toSubgroup := by
  dsimp only
  change
    j.fieldRange.fixingSubgroup ≤
      (j.comp
        (IsScalarTower.toAlgHom ℚ L L')).fieldRange.fixingSubgroup
  apply
    (j.comp
      (IsScalarTower.toAlgHom ℚ L L')).fieldRange.fixingSubgroup_le
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨algebraMap L L' y, rfl⟩

end EmbeddedNumberFieldRestriction

variable
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)

local instance abstractFixedFieldBaseQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K.field (le_baseField K.field)) :=
  K.finite

local instance abstractFixedFieldRelativeQuotientFinite :
    Finite
      (K.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K.field L.field L.below) :=
  L.finite

local instance abstractFixedFieldRelativeQuotientIsMulCommutative :
    IsMulCommutative L.extensionQuotient :=
  L.commutative

noncomputable local instance abstractFixedFieldFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K.field K.finite

noncomputable local instance abstractRelativeFixedFieldFiniteDimensional :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below K.finite L.finite

local instance abstractFixedFieldRelativeScalarTower :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance abstractRelativeFixedFieldAbsoluteFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance abstractFixedFieldNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)

/-- The lower fixed idèle-class group is commutative.  Naming the mixin
before the public quotient declarations avoids delayed normality synthesis
inside their definition bodies. -/
local instance
    abstractFixedFieldIdeleClassGroupIsMulCommutative :
    IsMulCommutative
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

noncomputable local instance abstractRelativeFixedFieldNumberField :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

/-- Use the same explicit Galois witness as the fixed-field quotient
comparison.  Deriving it through `IsAbelianGalois` produces an equivalent
but much larger dependent instance path. -/
noncomputable local instance
    abstractRelativeFixedFieldIsGalois :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below L.normal

noncomputable local instance abstractRelativeFixedFieldIsAbelianGalois :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois L

/-- Use one opaque normality witness for the actual fixed-field norm range.
This keeps every occurrence of its quotient group on the same instance path. -/
local instance
    abstractFixedFieldIdeleClassNormRangeNormal :
    ((_root_.ideleClassNorm
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below)).range).Normal := by
  infer_instance

/-- The abelianized abstract extension quotient is the actual Galois
group of the corresponding pair of fixed fields. -/
noncomputable def
    abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    Additive
        (Abelianization
          (FiniteGaloisSubextension.extensionQuotient
            L.toFiniteGaloisExtension)) ≃+
      Additive (Gal(E / F)) := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let e :
      L.extensionQuotient ≃*
        Gal(E / F) :=
    L.extensionQuotientMulEquiv.trans
      (abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        K.field L.field L.below L.normal)
  exact
    MulEquiv.toAdditive
      ((Abelianization.equivOfComm :
          L.extensionQuotient ≃*
            Abelianization L.extensionQuotient).symm.trans e)

/-- The actual fixed-field global norm-residue equivalence

`C_F / N_{E/F} C_E ≃ Gal(E/F)`

attached to an abstract finite abelian subextension in the rational
absolute class formation. -/
noncomputable def abstractFixedFieldGlobalNormResidueEquiv :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    Additive
        (IdeleClassGroup F ⧸
          (_root_.ideleClassNorm F E).range) ≃+
      Additive (Gal(E / F)) := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let eNorm :
      FiniteNormQuotient rationalIdeleClassRepresentation
          K.field L.field L.below ≃+
        Additive
          (Abelianization L.toFiniteGaloisExtension.extensionQuotient) :=
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      K L.toFiniteGaloisExtension
  exact
    (rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        K.field L.field L.below L.normal).symm.trans
      (eNorm.trans
        (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
          K L))

/-- The abstract finite norm-residue equivalence with its dependent source
instance fixed to the public finite norm quotient. -/
private noncomputable def abstractFixedFieldFiniteNormResidueGaloisEquiv :
    FiniteNormQuotient rationalIdeleClassRepresentation
        K.field L.field L.below ≃+
      Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field))) := by
  letI : AddCommGroup
      (FiniteNormQuotient rationalIdeleClassRepresentation
        K.field L.field L.below) :=
    finiteNormQuotientAddCommGroup rationalIdeleClassRepresentation
      K.field L.field L.below
  exact
    @AddEquiv.trans
      (FiniteNormQuotient rationalIdeleClassRepresentation
        K.field L.field L.below)
      (Additive
        (Abelianization
          L.toFiniteGaloisExtension.extensionQuotient))
      (Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field))))
      inferInstance inferInstance inferInstance
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        K L.toFiniteGaloisExtension)
      (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
        K L)

/-- The abstract norm-residue symbol on the fixed part of the rational
absolute idele-class representation, with its value transported to the
actual Galois group of the two fixed fields.  This is the form consumed
directly by the abstract norm--restriction naturality theorem. -/
noncomputable def ambientFixedGlobalNormResidueAddMonoidHom :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field →+
      Additive (Gal(E / F)) := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  exact
    (abstractFixedFieldFiniteNormResidueGaloisEquiv K L).toAddMonoidHom.comp
      (finiteNormClassHom rationalIdeleClassRepresentation
        K.field L.field L.below)

/-- The ordinary idele class group of the lower fixed field, transported
to the fixed part of the rational absolute idele-class representation. -/
private noncomputable def abstractFixedFieldIdeleClassToAmbientFixedMonoidHom :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    IdeleClassGroup F →*
      Multiplicative
        (ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field) :=
  (rationalAbstractFixedFieldIdeleClassEquivFixed
    K.field).toAddMonoidHom.toMultiplicativeRight

/-- The actual norm-residue homomorphism on the ordinary idele class
group of the lower fixed field, constructed without choosing a second
field embedding. -/
noncomputable def abstractFixedFieldGlobalNormResidueMonoidHom :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    IdeleClassGroup F →* Gal(E / F) :=
  (ambientFixedGlobalNormResidueAddMonoidHom K L).toMultiplicative.comp
    (abstractFixedFieldIdeleClassToAmbientFixedMonoidHom K)

/-- Pointwise form of the ambient fixed-part norm-residue homomorphism. -/
private theorem ambientFixedGlobalNormResidueAddMonoidHom_apply
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :
    ambientFixedGlobalNormResidueAddMonoidHom K L a =
      abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
        K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          K L.toFiniteGaloisExtension
          (finiteNormClass rationalIdeleClassRepresentation
            K.field L.field L.below a)) := by
  change
    abstractFixedFieldFiniteNormResidueGaloisEquiv K L
        (finiteNormClass rationalIdeleClassRepresentation
          K.field L.field L.below a) = _
  rfl

/-- Pointwise form of the transported fixed-field norm-residue homomorphism. -/
private theorem abstractFixedFieldGlobalNormResidueMonoidHom_apply :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    ∀ c : IdeleClassGroup F,
      abstractFixedFieldGlobalNormResidueMonoidHom K L c =
        Additive.toMul
          (ambientFixedGlobalNormResidueAddMonoidHom K L
            ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
              (Additive.ofMul c))) := by
  dsimp only
  intro c
  rfl

/-- Transporting an ordinary fixed-field idele class to the ambient
fixed part and applying the abstract norm-residue map gives exactly the
actual fixed-field norm-residue value. -/
@[simp]
theorem abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :
    abstractFixedFieldGlobalNormResidueMonoidHom K L
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed
            K.field).symm a)) =
      Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom K L a) := by
  rw [abstractFixedFieldGlobalNormResidueMonoidHom_apply]
  change
    Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom K L
          ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
            ((rationalAbstractFixedFieldIdeleClassEquivFixed
              K.field).symm a))) =
      Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom K L a)
  rw [(rationalAbstractFixedFieldIdeleClassEquivFixed
    K.field).apply_symm_apply]

/-- The ambient fixed-part reciprocity value vanishes precisely when its
finite norm class vanishes. -/
private theorem ambientFixedGlobalNormResidueAddMonoidHom_eq_zero_iff
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :
    ambientFixedGlobalNormResidueAddMonoidHom K L a = 0 ↔
      finiteNormClass rationalIdeleClassRepresentation
        K.field L.field L.below a = 0 := by
  rw [ambientFixedGlobalNormResidueAddMonoidHom_apply]
  change
    abstractFixedFieldFiniteNormResidueGaloisEquiv K L
        (finiteNormClass rationalIdeleClassRepresentation
        K.field L.field L.below a) = 0 ↔
      finiteNormClass rationalIdeleClassRepresentation
        K.field L.field L.below a = 0
  exact
    (abstractFixedFieldFiniteNormResidueGaloisEquiv K L).map_eq_zero_iff

/-- The fixed-field idele-class comparison carries the abstract finite norm
subgroup exactly to the ordinary norm range. -/
private theorem
    rationalAbstractFixedFieldIdeleClassEquivFixed_mem_finiteNormSubgroup_iff
    (c : IdeleClassGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :
    (rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
          (Additive.ofMul c) ∈
        finiteNormSubgroup rationalIdeleClassRepresentation
          K.field L.field L.below ↔
      c ∈
        (_root_.ideleClassNorm
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below)).range := by
  let eK := rationalAbstractFixedFieldIdeleClassEquivFixed K.field
  let S :=
    finiteNormSubgroup rationalIdeleClassRepresentation
      K.field L.field L.below
  let N :=
    (_root_.ideleClassNorm
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below)).range
  have hmap :=
    map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
      K.field L.field L.below L.normal
  have hmem :
      Additive.ofMul c ∈ S.map eK.symm.toAddMonoidHom ↔
        Additive.ofMul c ∈ N.toAddSubgroup :=
    Iff.of_eq (congrArg
      (fun T : AddSubgroup (Additive (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field))) =>
        Additive.ofMul c ∈ T) hmap)
  change eK (Additive.ofMul c) ∈ S ↔ Additive.ofMul c ∈ N.toAddSubgroup
  constructor
  · intro hc
    have hmapped :
        Additive.ofMul c ∈ S.map eK.symm.toAddMonoidHom :=
      ⟨eK (Additive.ofMul c), hc, eK.symm_apply_apply _⟩
    exact hmem.mp hmapped
  · intro hc
    have hmapped :
        Additive.ofMul c ∈ S.map eK.symm.toAddMonoidHom := by
      exact hmem.mpr hc
    rcases hmapped with ⟨a, ha, hac⟩
    have hea : a = eK (Additive.ofMul c) :=
      (eK.apply_symm_apply a).symm.trans (congrArg eK hac)
    exact hea ▸ ha

/-- Triviality of the fixed-field norm-residue symbol is exactly
membership in the actual ordinary idele-class norm range. -/
@[simp]
theorem abstractFixedFieldGlobalNormResidueMonoidHom_eq_one_iff
    (c : IdeleClassGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :
      abstractFixedFieldGlobalNormResidueMonoidHom K L c = 1 ↔
        c ∈
          (_root_.ideleClassNorm
            (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
            (abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) L.below)).range := by
  calc
    abstractFixedFieldGlobalNormResidueMonoidHom K L c = 1
        ↔ abstractFixedFieldGlobalNormResidueMonoidHom K L
            (Additive.toMul
              ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field).symm
                ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
                  (Additive.ofMul c)))) = 1 := by
          rw [(rationalAbstractFixedFieldIdeleClassEquivFixed
            K.field).symm_apply_apply]
          rfl
    _ ↔ Additive.toMul
          (ambientFixedGlobalNormResidueAddMonoidHom K L
            ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
              (Additive.ofMul c))) = 1 := by
          exact Iff.of_eq (congrArg (fun g => g = 1)
            (abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply K L
              ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
                (Additive.ofMul c))))
    _ ↔ ambientFixedGlobalNormResidueAddMonoidHom K L
          ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
            (Additive.ofMul c)) = 0 :=
      toMul_eq_one
    _ ↔ finiteNormClass rationalIdeleClassRepresentation
          K.field L.field L.below
          ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
            (Additive.ofMul c)) = 0 :=
      ambientFixedGlobalNormResidueAddMonoidHom_eq_zero_iff K L _
    _ ↔ (rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
          (Additive.ofMul c) ∈
          finiteNormSubgroup rationalIdeleClassRepresentation
            K.field L.field L.below :=
      finiteNormClass_eq_zero_iff rationalIdeleClassRepresentation
        K.field L.field L.below _
    _ ↔ c ∈
          (_root_.ideleClassNorm
            (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
            (abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) L.below)).range :=
      rationalAbstractFixedFieldIdeleClassEquivFixed_mem_finiteNormSubgroup_iff
        K L c

/-- The ambient fixed-part reciprocity homomorphism is surjective. -/
private theorem ambientFixedGlobalNormResidueAddMonoidHom_surjective :
    Function.Surjective
      (ambientFixedGlobalNormResidueAddMonoidHom K L) := by
  intro y
  obtain ⟨z, hz⟩ :=
    (abstractFixedFieldFiniteNormResidueGaloisEquiv K L).surjective y
  obtain ⟨a, ha⟩ :=
    finiteNormClass_surjective rationalIdeleClassRepresentation
      K.field L.field L.below z
  refine ⟨a, ?_⟩
  rw [ambientFixedGlobalNormResidueAddMonoidHom_apply, ha]
  exact hz

/-- The fixed-field global norm-residue homomorphism is surjective
onto the actual Galois group. -/
theorem abstractFixedFieldGlobalNormResidueMonoidHom_surjective :
    Function.Surjective
      (abstractFixedFieldGlobalNormResidueMonoidHom K L) := by
  intro y
  obtain ⟨a, ha⟩ :=
    ambientFixedGlobalNormResidueAddMonoidHom_surjective K L
      (Additive.ofMul y)
  refine
    ⟨Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field).symm a), ?_⟩
  rw [abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply, ha]
  rfl

/-- The kernel of the fixed-field global norm-residue homomorphism is
the genuine ordinary idele-class norm range. -/
@[simp]
theorem abstractFixedFieldGlobalNormResidueMonoidHom_ker :
    (abstractFixedFieldGlobalNormResidueMonoidHom K L).ker =
      (_root_.ideleClassNorm
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) L.below)).range := by
  ext c
  change
    abstractFixedFieldGlobalNormResidueMonoidHom K L c = 1 ↔
      c ∈
        (_root_.ideleClassNorm
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below)).range
  exact
    abstractFixedFieldGlobalNormResidueMonoidHom_eq_one_iff
      K L c

end Reciprocity
end GlobalClassFieldTheory
