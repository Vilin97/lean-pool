/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisDescent
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.Permutation.Module
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness
/-!
# Herbrand cohomology of the relative idele class group

This file realizes the low-degree exact sequence on the actual relative
idele group

`1 → Lˣ → I_L → C_L → 1`.

The Galois actions are the concrete conjugation actions from the
tensor-product model of relative adeles.  The class norm is descended from
the determinant norm on relative ideles, and its relation with the Tate
norm is proved from the Galois product formula.
-/

@[expose] public section

open scoped BigOperators NumberField
open NumberField

noncomputable section


open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

namespace RelativeIdeleGroup
namespace Cohomology

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The natural Galois action on relative ideles, upgraded from the
existing multiplicative action to an action by group automorphisms. -/
@[reducible]
noncomputable def relativeIdeleMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup K L) where
  __ := RelativeIdeleGroup.relativeIdeleMulAction K L
  smul_one σ :=
    map_one (RelativeIdeleGroup.conjugationIdele K L σ)
  smul_mul σ a b :=
    map_mul
      (RelativeIdeleGroup.conjugationIdele K L σ) a b

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem principalRelativeIdele_smul_mem
    (σ : L ≃ₐ[K] L)
    (a : RelativeIdeleGroup K L)
    (ha :
      a ∈ RelativeIdeleGroup.principalSubgroup K L) :
    σ • a ∈
      RelativeIdeleGroup.principalSubgroup K L := by
  rcases ha with ⟨x, rfl⟩
  refine
    ⟨Units.map σ.toRingEquiv.toMonoidHom x, ?_⟩
  exact
    (RelativeIdeleGroup.smul_principalIdele
      K L σ x).symm

/-- The actual quotient Galois action on the relative idele class group,
upgraded to an action by group automorphisms. -/
@[reducible]
noncomputable def ideleClassMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.ClassGroup K L) := by
  letI := relativeIdeleMulDistribMulAction K L
  exact
    stableQuotientMulDistribMulAction
      (RelativeIdeleGroup.principalSubgroup K L)
      (principalRelativeIdele_smul_mem K L)

/-- The restricted Galois action on the actual subgroup of principal
relative ideles. -/
@[reducible]
noncomputable def principalIdeleMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) := by
  letI := relativeIdeleMulDistribMulAction K L
  exact
    stableSubgroupMulDistribMulAction
      (RelativeIdeleGroup.principalSubgroup K L)
      (principalRelativeIdele_smul_mem K L)

/-- The norm on relative ideles, descended through principal ideles to
the actual idele class groups. -/
noncomputable def ideleClassNorm :
    RelativeIdeleGroup.ClassGroup K L →*
      IdeleClassGroup K :=
  QuotientGroup.map
    (RelativeIdeleGroup.principalSubgroup K L)
    (IdeleGroup.principalSubgroup K)
    (RelativeIdeleGroup.norm K L)
    (by
      rintro _ ⟨x, rfl⟩
      refine
        ⟨Units.map (Algebra.norm K) x, ?_⟩
      exact
        (RelativeIdeleGroup.norm_principalIdele
          K L x).symm)

omit [NumberField L] [IsGalois K L] in
theorem ideleClassNorm_mk
    (a : RelativeIdeleGroup K L) :
    ideleClassNorm K L
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K L a) :=
  rfl

/-- The concrete norm quotient `C_K / N_{L/K} C_L`. -/
abbrev IdeleClassNormQuotient :=
  IdeleClassGroup K ⧸ (ideleClassNorm K L).range

section Actions

/-- Galois automorphisms act on relative ideles by conjugation. -/
local instance :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L

/-- The Galois action on relative ideles descends to their class group. -/
local instance :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.ClassGroup K L) :=
  ideleClassMulDistribMulAction K L

/-- The Galois action on relative ideles restricts to the principal subgroup. -/
local instance :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem relativeIdele_smul_def
    (σ : L ≃ₐ[K] L)
    (a : RelativeIdeleGroup K L) :
    σ • a =
      RelativeIdeleGroup.conjugationIdele K L σ a :=
  rfl

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem ideleClass_smul_mk
    (σ : L ≃ₐ[K] L)
    (a : RelativeIdeleGroup K L) :
    σ • QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) a =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        (σ • a) :=
  rfl

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem principalIdele_smul_coe
    (σ : L ≃ₐ[K] L)
    (a :
      RelativeIdeleGroup.principalSubgroup K L) :
    ((σ • a :
        RelativeIdeleGroup.principalSubgroup K L) :
      RelativeIdeleGroup K L) =
        σ • (a : RelativeIdeleGroup K L) :=
  stableSubgroup_smul_coe
    (RelativeIdeleGroup.principalSubgroup K L)
    (principalRelativeIdele_smul_mem K L) σ a

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Equivariance of the principal-idele inclusion. -/
theorem principalIdeleSubtype_equivariant :
    ∀ (σ : L ≃ₐ[K] L)
      (a : RelativeIdeleGroup.principalSubgroup K L),
      (RelativeIdeleGroup.principalSubgroup K L).subtype
          (σ • a) =
        σ •
          (RelativeIdeleGroup.principalSubgroup K L).subtype
            a :=
  stableSubgroup_subtype_equivariant
    (RelativeIdeleGroup.principalSubgroup K L)
    (principalRelativeIdele_smul_mem K L)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Equivariance of the actual quotient map `I_L → C_L`. -/
theorem ideleClassQuotientMap_equivariant :
    ∀ (σ : L ≃ₐ[K] L)
      (a : RelativeIdeleGroup K L),
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (σ • a) =
        σ • QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a :=
  stableSubgroup_quotientMap_equivariant
    (RelativeIdeleGroup.principalSubgroup K L)
    (principalRelativeIdele_smul_mem K L)

omit [NumberField L] in
/-- On relative ideles the Tate norm is the inclusion of the determinant
norm.  This is the Galois product formula, not a separate class-field
hypothesis. -/
theorem relativeIdele_tateNorm_eq_inclusion_norm
    (a : RelativeIdeleGroup K L) :
    tateNorm (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L) a =
      RelativeIdeleGroup.inclusion K L
        (RelativeIdeleGroup.norm K L a) := by
  simpa only [tateNorm] using
    (RelativeIdeleGroup.inclusion_norm_eq_prod_conjugates
      (K := K) (L := L) a).symm

omit [NumberField L] in
/-- The class norm agrees, after Galois descent, with the Tate norm on
the actual relative idele class group. -/
theorem classInclusion_ideleClassNorm_eq_tateNorm
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classInclusion K L
        (ideleClassNorm K L c) =
      tateNorm (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        (RelativeIdeleGroup.inclusion K L
          (RelativeIdeleGroup.norm K L a)) =
      ∏ σ : L ≃ₐ[K] L,
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (σ • a)
  rw [← map_prod]
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L))
    (RelativeIdeleGroup.inclusion_norm_eq_prod_conjugates
      (K := K) (L := L) a)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The fixed subgroup used by Tate cohomology is the concrete
Galois-fixed subgroup from idele-class descent. -/
theorem ideleClass_fixedSubgroup_eq_galoisFixed :
    fixedSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) =
      RelativeIdeleGroup.galoisFixedClassSubgroup K L := by
  ext c
  constructor
  · intro hc σ
    exact hc σ
  · intro hc σ
    exact hc σ

/-- Galois descent as a homomorphism from the base idele class group to
the Tate fixed subgroup. -/
def baseIdeleClassToFixed :
    IdeleClassGroup K →*
      fixedSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) :=
  (RelativeIdeleGroup.classInclusion K L).codRestrict
    (fixedSubgroup (L ≃ₐ[K] L)
      (RelativeIdeleGroup.ClassGroup K L))
    (by
      intro c
      rw [ideleClass_fixedSubgroup_eq_galoisFixed K L]
      exact
        RelativeIdeleGroup.classInclusion_range_le_galoisFixed
          K L ⟨c, rfl⟩)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem baseIdeleClassToFixed_coe
    (c : IdeleClassGroup K) :
    ((baseIdeleClassToFixed K L c :
        fixedSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) :
      RelativeIdeleGroup.ClassGroup K L) =
        RelativeIdeleGroup.classInclusion K L c :=
  rfl

/-- Galois descent packaged as the multiplicative equivalence
`C_K ≃ C_L^G` required by the `H⁰` calculation. -/
noncomputable def baseIdeleClassEquivFixed :
    IdeleClassGroup K ≃*
      fixedSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) :=
  MulEquiv.ofBijective
    (baseIdeleClassToFixed K L)
    ⟨by
      intro a b hab
      apply RelativeIdeleGroup.classInclusion_injective K L
      exact congrArg Subtype.val hab,
    by
      intro c
      have hc :
          (c : RelativeIdeleGroup.ClassGroup K L) ∈
            (RelativeIdeleGroup.classInclusion K L).range := by
        rw [
          RelativeIdeleGroup.classInclusion_range_eq_galoisFixedClassSubgroup
            K L,
          ← ideleClass_fixedSubgroup_eq_galoisFixed K L]
        exact c.property
      rcases hc with ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩⟩

omit [NumberField L] in
@[simp]
theorem baseIdeleClassEquivFixed_coe
    (c : IdeleClassGroup K) :
    ((baseIdeleClassEquivFixed K L c :
        fixedSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) :
      RelativeIdeleGroup.ClassGroup K L) =
        RelativeIdeleGroup.classInclusion K L c :=
  rfl

omit [NumberField L] in
/-- Under Galois descent, the image of the class norm is exactly the
Tate-norm subgroup of the fixed idele classes. -/
theorem ideleClassNorm_range_map_equivFixed :
    (ideleClassNorm K L).range.map
        (baseIdeleClassEquivFixed K L).toMonoidHom =
      (tateNormSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L)).subgroupOf
          (fixedSubgroup (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) := by
  ext x
  constructor
  · rintro ⟨c, ⟨d, rfl⟩, rfl⟩
    change
      RelativeIdeleGroup.classInclusion K L
          (ideleClassNorm K L d) ∈
        tateNormSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)
    exact
      ⟨d,
        (classInclusion_ideleClassNorm_eq_tateNorm
          K L d).symm⟩
  · intro hx
    change
      (x : RelativeIdeleGroup.ClassGroup K L) ∈
        tateNormSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) at hx
    rcases hx with ⟨d, hd⟩
    refine
      ⟨ideleClassNorm K L d, ⟨d, rfl⟩, ?_⟩
    apply Subtype.ext
    exact
      (classInclusion_ideleClassNorm_eq_tateNorm
        K L d).trans hd

omit [NumberField L] in
/-- The Tate norm kernel on idele classes is the kernel of the descended
idele-class norm.  Injectivity of `C_K → C_L` is the descent input. -/
theorem ideleClass_normKernelSubgroup_eq_ker :
    normKernelSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) =
      MonoidHom.ker (ideleClassNorm K L) := by
  ext c
  change
    tateNorm (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) c = 1 ↔
      ideleClassNorm K L c = 1
  constructor
  · intro hc
    apply RelativeIdeleGroup.classInclusion_injective K L
    rw [map_one,
      classInclusion_ideleClassNorm_eq_tateNorm K L c,
      hc]
  · intro hc
    rw [← classInclusion_ideleClassNorm_eq_tateNorm K L c,
      hc, map_one]

/-- The negative-first Tate group for the actual idele class module,
displayed as norm-one classes modulo augmentation classes. -/
noncomputable def ideleClassHerbrandHMinusOneEquiv
    (σ : L ≃ₐ[K] L) :
    HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) σ ≃*
      normKernelSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) ⧸
        (augmentationSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) σ).subgroupOf
            (normKernelSubgroup (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) :=
  HerbrandHMinusOne.equiv
    (G := L ≃ₐ[K] L)
    (A := RelativeIdeleGroup.ClassGroup K L) σ

section NormQuotientIdentification

local instance ideleClassNormQuotient_baseIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The degree-zero Tate group of the actual idele class group is the
class-norm quotient `C_K / N_{L/K} C_L`. -/
noncomputable def ideleClassHerbrandH0EquivNormQuotient :
    HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) ≃*
      IdeleClassNormQuotient K L :=
  (HerbrandH0.equiv
    (G := L ≃ₐ[K] L)
    (A := RelativeIdeleGroup.ClassGroup K L)).trans
      (QuotientGroup.congr
        (ideleClassNorm K L).range
        ((tateNormSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)).subgroupOf
            (fixedSubgroup (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)))
        (baseIdeleClassEquivFixed K L)
        (ideleClassNorm_range_map_equivFixed K L)).symm

omit [NumberField L] in
/-- The norm index is the cardinality of the actual degree-zero Tate
cohomology group.  This statement is valid without silently assigning a
positive finite index to an infinite quotient. -/
theorem ideleClassNorm_index_eq_herbrandH0_card :
    (ideleClassNorm K L).range.index =
      Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) := by
  rw [Subgroup.index_eq_card]
  exact
    (Nat.card_congr
      (ideleClassHerbrandH0EquivNormQuotient
        K L).toEquiv).symm

end NormQuotientIdentification

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Exactness at `I_L` of `Lˣ → I_L → C_L`. -/
theorem principalIdele_ideleClass_exact :
    ∀ a : RelativeIdeleGroup K L,
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a = 1 ↔
        ∃ p : RelativeIdeleGroup.principalSubgroup K L,
          (RelativeIdeleGroup.principalSubgroup K L).subtype p =
            a :=
  stableSubgroup_quotientMap_exact
    (RelativeIdeleGroup.principalSubgroup K L)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The complete short-exactness data for the actual principal-idele
inclusion and idele-class quotient. -/
theorem principalIdele_ideleClass_shortExact :
    (∀ (σ : L ≃ₐ[K] L)
      (p : RelativeIdeleGroup.principalSubgroup K L),
      (RelativeIdeleGroup.principalSubgroup K L).subtype
          (σ • p) =
        σ •
          (RelativeIdeleGroup.principalSubgroup K L).subtype p) ∧
    (∀ (σ : L ≃ₐ[K] L)
      (a : RelativeIdeleGroup K L),
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (σ • a) =
        σ • QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) ∧
    (∀ a : RelativeIdeleGroup K L,
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a = 1 ↔
        ∃ p : RelativeIdeleGroup.principalSubgroup K L,
          (RelativeIdeleGroup.principalSubgroup K L).subtype p =
            a) ∧
    Function.Injective
      (RelativeIdeleGroup.principalSubgroup K L).subtype ∧
    Function.Surjective
      (QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)) := by
  exact
    ⟨principalIdeleSubtype_equivariant K L,
      ideleClassQuotientMap_equivariant K L,
      principalIdele_ideleClass_exact K L,
      (RelativeIdeleGroup.principalSubgroup K L).subtype_injective,
      QuotientGroup.mk'_surjective
        (RelativeIdeleGroup.principalSubgroup K L)⟩

omit [NumberField L] [IsGalois K L] in
/-- Herbrand-quotient multiplicativity for the actual exact sequence
`1 → Lˣ → I_L → C_L → 1`. -/
theorem relativeIdele_herbrandQuotient_eq_principal_mul_class
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    [Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L))]
    [Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) σ)]
    [Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L))]
    [Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L) σ)]
    [Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L))]
    [Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) σ)] :
    herbrandQuotient
        (G := L ≃ₐ[K] L)
        (A := RelativeIdeleGroup K L) σ =
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A :=
            RelativeIdeleGroup.principalSubgroup K L) σ *
        herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := RelativeIdeleGroup.ClassGroup K L) σ := by
  let q :
      RelativeIdeleGroup K L →*
        RelativeIdeleGroup.ClassGroup K L :=
    QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L)
  have hqEquivariant :
      ∀ (τ : L ≃ₐ[K] L)
        (a : RelativeIdeleGroup K L),
        q (τ • a) = τ • q a := by
    exact ideleClassQuotientMap_equivariant K L
  have hqExact :
      ∀ a : RelativeIdeleGroup K L,
        q a = 1 ↔
          ∃ p : RelativeIdeleGroup.principalSubgroup K L,
            (RelativeIdeleGroup.principalSubgroup K L).subtype p =
              a := by
    exact principalIdele_ideleClass_exact K L
  have hqSurjective : Function.Surjective q := by
    exact QuotientGroup.mk'_surjective
      (RelativeIdeleGroup.principalSubgroup K L)
  exact
    @herbrandQuotient_multiplicative_of_shortExact
      (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L)
      (RelativeIdeleGroup K L)
      (RelativeIdeleGroup.ClassGroup K L)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RelativeIdeleGroup.principalSubgroup K L).subtype
      q
      (principalIdeleSubtype_equivariant K L)
      hqEquivariant
      hqExact
      (RelativeIdeleGroup.principalSubgroup K L).subtype_injective
      hqSurjective
      σ hgen
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance

omit [NumberField L] [IsGalois K L] in
/-- Once the Herbrand quotients of principal ideles and relative ideles
have been computed, the actual idele-class quotient is automatically
defined and satisfies the multiplicativity identity.  This is the
connection point for the unrestricted local-factor and `S`-unit calculations. -/
theorem ideleClassHerbrandQuotientDefined_of_principal_relative
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    [Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L))]
    [Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) σ)]
    [Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L))]
    [Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L) σ)] :
    ∃ hC :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) σ,
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := RelativeIdeleGroup K L) σ =
        herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A :=
              RelativeIdeleGroup.principalSubgroup K L) σ *
          @herbrandQuotient
            (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)
            inferInstance inferInstance inferInstance
            (ideleClassMulDistribMulAction K L)
            σ hC.1 hC.2 := by
  let q :
      RelativeIdeleGroup K L →*
        RelativeIdeleGroup.ClassGroup K L :=
    QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L)
  have hqEquivariant :
      ∀ (τ : L ≃ₐ[K] L)
        (a : RelativeIdeleGroup K L),
        q (τ • a) = τ • q a :=
    ideleClassQuotientMap_equivariant K L
  have hqExact :
      ∀ a : RelativeIdeleGroup K L,
        q a = 1 ↔
          ∃ p : RelativeIdeleGroup.principalSubgroup K L,
            (RelativeIdeleGroup.principalSubgroup K L).subtype p =
              a :=
    principalIdele_ideleClass_exact K L
  have hqSurjective : Function.Surjective q :=
    QuotientGroup.mk'_surjective
      (RelativeIdeleGroup.principalSubgroup K L)
  exact
    @herbrandQuotient_multiplicative_of_left_middle_defined
      (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L)
      (RelativeIdeleGroup K L)
      (RelativeIdeleGroup.ClassGroup K L)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RelativeIdeleGroup.principalSubgroup K L).subtype
      q
      (principalIdeleSubtype_equivariant K L)
      hqEquivariant
      hqExact
      (RelativeIdeleGroup.principalSubgroup K L).subtype_injective
      hqSurjective
      σ hgen
      inferInstance inferInstance inferInstance inferInstance

end Actions

end Cohomology
end RelativeIdeleGroup
