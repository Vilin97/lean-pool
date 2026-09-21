/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinDescent
/-!
# Surjectivity of the infinite global Artin homomorphism

The absolute idele norm is split, up to inversion, by an idele supported at
one infinite place.  Its local component is positive, so every finite global
Artin homomorphism, and hence the infinite global Artin homomorphism, kills
it.  Multiplication by this section therefore replaces any idele by a
norm-one idele without changing its Artin symbol.
-/

open scoped Classical IsMulCommutative NNReal NumberField Topology
open NumberField IsDedekindDomain
open NumberField.Units.dirichletUnitTheorem

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- Compatibility name for the positive archimedean section. -/
noncomputable def numberFieldPositiveArchimedeanIdele
    (K : Type) [Field K] [NumberField K] :
    ℝ≥0ˣ →* IdeleGroup K :=
  IdeleGroup.positiveArchimedeanSection K

/-- Compatibility evaluation of the finite components of the positive
archimedean section. -/
@[simp]
theorem numberFieldPositiveArchimedeanIdele_finiteComponent
    (r : ℝ≥0ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup.finiteComponent v
        (numberFieldPositiveArchimedeanIdele K r) =
      1 :=
  IdeleGroup.positiveArchimedeanSection_finiteComponent r v

/-- Compatibility form of positivity at every infinite component. -/
theorem numberFieldPositiveArchimedeanIdele_infiniteComponent_mem_positive
    (r : ℝ≥0ˣ) (v : InfinitePlace K) :
    IdeleGroup.infiniteComponent v
        (numberFieldPositiveArchimedeanIdele K r) ∈
      RayClass.infinitePositiveSubgroup v :=
  IdeleGroup.positiveArchimedeanSection_infiniteComponent_mem_positive r v

/-- Compatibility form of the absolute-norm evaluation. -/
@[simp]
theorem numberFieldPositiveArchimedeanIdele_absoluteNorm
    (r : ℝ≥0ˣ) :
    IdeleGroup.absoluteNorm
        (numberFieldPositiveArchimedeanIdele K r) =
      r⁻¹ :=
  IdeleGroup.positiveArchimedeanSection_absoluteNorm r

private theorem globalArtinMonoidHom_positiveArchimedeanSection
    {L : Type}
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (r : ℝ≥0ˣ) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.positiveArchimedeanSection K r) =
      1 := by
  rw [globalArtinMonoidHom_apply]
  have hinfinite :
      (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.infiniteComponent v
            (IdeleGroup.positiveArchimedeanSection K r))) =
        1 := by
    apply Finset.prod_eq_one
    intro v _
    apply
      (chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
        (K := K) (L := L) v _).2
    exact
      (infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
        (K := K) (L := L) v)
        (IdeleGroup.positiveArchimedeanSection_infiniteComponent_mem_positive
          r v)
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v
            (IdeleGroup.positiveArchimedeanSection K r))) =
        1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [IdeleGroup.positiveArchimedeanSection_finiteComponent,
      map_one]
  rw [hinfinite, hfinite, mul_one]

private theorem continuousMulEquivToLimit_infiniteGlobalArtinMonoidHom_apply'
    {K Ω : Type}
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    InfiniteGalois.continuousMulEquivToLimit K Ω
        (infiniteGlobalArtinMonoidHom K Ω a) =
      infiniteGlobalArtinToLimit K Ω a := by
  exact
    (InfiniteGalois.continuousMulEquivToLimit K Ω).apply_symm_apply _

/-- The infinite global Artin homomorphism kills the positive archimedean
section over every number field. -/
@[simp]
theorem infiniteGlobalArtinMonoidHom_positiveArchimedeanSection
    (K Ω : Type)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (r : ℝ≥0ˣ) :
    infiniteGlobalArtinMonoidHom K Ω
        (IdeleGroup.positiveArchimedeanSection K r) =
      1 := by
  let
      (E : FiniteGaloisIntermediateField K Ω) :
      NumberField E :=
    NumberField.of_module_finite K E
  let
      (E : FiniteGaloisIntermediateField K Ω) :
      IsAbelianGalois K E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  apply
    (InfiniteGalois.continuousMulEquivToLimit K Ω).injective
  rw [
    continuousMulEquivToLimit_infiniteGlobalArtinMonoidHom_apply',
    map_one]
  apply Subtype.ext
  funext E
  exact
    globalArtinMonoidHom_positiveArchimedeanSection
      (K := K) (L := E.unop) r

/-- Compatibility form of the Artin evaluation on the positive archimedean
section. -/
@[simp]
theorem infiniteGlobalArtinMonoidHom_numberFieldPositiveArchimedeanIdele
    (K Ω : Type)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (r : ℝ≥0ˣ) :
    infiniteGlobalArtinMonoidHom K Ω
        (numberFieldPositiveArchimedeanIdele K r) =
      1 :=
  infiniteGlobalArtinMonoidHom_positiveArchimedeanSection K Ω r

/-- Every idele has the same infinite global Artin symbol as a norm-one
idele. -/
theorem exists_normOneIdele_same_infiniteGlobalArtin
    (K Ω : Type)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    ∃ b : IdeleGroup.normOneSubgroup (K := K),
      infiniteGlobalArtinMonoidHom K Ω b =
        infiniteGlobalArtinMonoidHom K Ω a := by
  refine
    ⟨IdeleGroup.positiveArchimedeanNormOneCorrection K a, ?_⟩
  rw [IdeleGroup.positiveArchimedeanNormOneCorrection_coe,
    map_mul,
    infiniteGlobalArtinMonoidHom_positiveArchimedeanSection,
    mul_one]

private theorem
    infiniteGlobalIdeleClassArtinContinuousMonoidHom_normOne_denseRange
    (K Ω : Type)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    DenseRange
      (fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
        infiniteGlobalIdeleClassArtinContinuousMonoidHom
          (K := K) (Ω := Ω) (c : IdeleClassGroup K)) := by
  apply
    (infiniteGlobalIdeleClassArtinContinuousMonoidHom_denseRange
      (K := K) (Ω := Ω)).mono
  rintro σ ⟨c, rfl⟩
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup K) c
  obtain ⟨b, hb⟩ :=
    exists_normOneIdele_same_infiniteGlobalArtin K Ω a
  let d : IdeleClassGroup.normOneSubgroup (K := K) :=
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (b : IdeleGroup K),
      (IdeleClassGroup.mk_mem_normOneSubgroup_iff
        (b : IdeleGroup K)).2 b.2⟩
  refine ⟨d, ?_⟩
  change
    infiniteGlobalIdeleClassArtinMonoidHom
        (K := K) (Ω := Ω)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (b : IdeleGroup K)) =
      infiniteGlobalIdeleClassArtinMonoidHom
        (K := K) (Ω := Ω)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a)
  rw [infiniteGlobalIdeleClassArtinMonoidHom_mk,
    infiniteGlobalIdeleClassArtinMonoidHom_mk]
  exact hb

private theorem
    infiniteGlobalIdeleClassArtinContinuousMonoidHom_normOne_surjective
    (K Ω : Type)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    Function.Surjective
      (fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
        infiniteGlobalIdeleClassArtinContinuousMonoidHom
          (K := K) (Ω := Ω) (c : IdeleClassGroup K)) := by
  let f :=
    fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
      infiniteGlobalIdeleClassArtinContinuousMonoidHom
        (K := K) (Ω := Ω) (c : IdeleClassGroup K)
  have hf : Continuous f := by
    exact
      (infiniteGlobalIdeleClassArtinContinuousMonoidHom
        (K := K) (Ω := Ω)).continuous_toFun.comp
          continuous_subtype_val
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf).isClosed
  have hdense : DenseRange f := by
    simpa only [f] using
      (infiniteGlobalIdeleClassArtinContinuousMonoidHom_normOne_denseRange
        K Ω)
  intro σ
  have hσ : σ ∈ closure (Set.range f) := by
    rw [hdense.closure_range]
    trivial
  rwa [hclosed.closure_eq] at hσ

/-- The infinite global Artin homomorphism on idele classes is surjective. -/
theorem infiniteGlobalIdeleClassArtinContinuousMonoidHom_surjective
    (K Ω : Type)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    Function.Surjective
      (infiniteGlobalIdeleClassArtinContinuousMonoidHom
        (K := K) (Ω := Ω)) := by
  intro σ
  obtain ⟨c, hc⟩ :=
    infiniteGlobalIdeleClassArtinContinuousMonoidHom_normOne_surjective
      K Ω σ
  exact ⟨(c : IdeleClassGroup K), hc⟩

/-- The infinite global Artin homomorphism is surjective. -/
theorem infiniteGlobalArtinMonoidHom_surjective
    (K Ω : Type)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    Function.Surjective
      (infiniteGlobalArtinMonoidHom K Ω) := by
  intro σ
  obtain ⟨c, hc⟩ :=
    infiniteGlobalIdeleClassArtinContinuousMonoidHom_surjective
      K Ω σ
  obtain ⟨a, ha⟩ :=
    QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup K) c
  refine ⟨a, ?_⟩
  calc
    infiniteGlobalArtinMonoidHom K Ω a =
        infiniteGlobalIdeleClassArtinContinuousMonoidHom
          (K := K) (Ω := Ω)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a) :=
      (infiniteGlobalIdeleClassArtinMonoidHom_mk
        (K := K) (Ω := Ω) a).symm
    _ = infiniteGlobalIdeleClassArtinContinuousMonoidHom
          (K := K) (Ω := Ω) c := by rw [ha]
    _ = σ := hc

end Reciprocity
end GlobalClassFieldTheory
