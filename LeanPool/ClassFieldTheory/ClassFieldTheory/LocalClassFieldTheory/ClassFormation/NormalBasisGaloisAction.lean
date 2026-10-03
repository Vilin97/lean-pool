/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
public import Mathlib.GroupTheory.GroupAction.Quotient
/-! Provides the public declarations in the
  `LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction` Lean module. -/

@[expose] public section

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable
section

universe uG uA u

open scoped ValuativeRel
open IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Restrict a multiplicative group action to an invariant subgroup.  This
is the honest action used below on the standard subgroups `V^n`. -/
@[implicit_reducible]
def subgroupMulDistribMulActionOfStable
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    MulDistribMulAction G V where
  smul g a := ⟨g • (a : A), hstable g a a.2⟩
  one_smul := by
    intro a
    apply Subtype.ext
    exact one_smul G (a : A)
  mul_smul := by
    intro g h a
    apply Subtype.ext
    exact mul_smul g h (a : A)
  smul_mul := by
    intro g a b
    apply Subtype.ext
    exact MulDistribMulAction.smul_mul g (a : A) (b : A)
  smul_one := by
    intro g
    apply Subtype.ext
    exact MulDistribMulAction.smul_one g

/-- An invariant subgroup satisfies the relation-preservation condition
needed for the action on its quotient. -/
theorem quotientActionOfSubgroupStable
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    MulAction.QuotientAction G V where
  inv_mul_mem g a b hab := by
    have hsmul : g • (a⁻¹ * b) ∈ V := hstable g (a⁻¹ * b) hab
    simpa [MulDistribMulAction.smul_mul, map_inv] using hsmul

/-- Descend an action by group automorphisms to the quotient by an invariant
subgroup. -/
@[implicit_reducible]
def quotientMulDistribMulActionOfSubgroupStable
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    MulDistribMulAction G (A ⧸ V) := by
  letI : MulAction.QuotientAction G V :=
    quotientActionOfSubgroupStable G A V hstable
  exact
    { smul := (· • ·)
      one_smul := one_smul G
      mul_smul := mul_smul
      smul_mul := by
        intro g x y
        refine Quotient.inductionOn₂' x y ?_
        intro a b
        exact congrArg QuotientGroup.mk
          (MulDistribMulAction.smul_mul g a b)
      smul_one := by
        intro g
        exact congrArg QuotientGroup.mk
          (MulDistribMulAction.smul_one g) }

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Every dilate `π_K^n M` of the normal-basis lattice is stable under the
actual action of `Gal(L / K)`. -/
theorem galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice
    (n : Nat) (sigma : Gal(L/K)) {x : L}
    (hx : x ∈ chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L)) :
    sigma x ∈ chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L) := by
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) x).1 hx with
    ⟨y, hy, rfl⟩
  refine (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) _).2
    ⟨sigma y,
      galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
        (K := K) (L := L) sigma hy, ?_⟩
  rw [map_mul]
  change
    algebraMap K L (((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K)) *
        sigma y =
      sigma (algebraMap K L
        (((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K))) * sigma y
  rw [sigma.commutes]

variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The actual integer-unit Galois action preserves each normal-basis
principal-unit set `V^n = 1 + π_K^n M`. -/
theorem galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
    (n : Nat) (sigma : Gal(L/K)) {a : 𝒪[L]ˣ}
    (ha : a ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    sigma • a ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff] at ha ⊢
  have hstable :=
    galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice
      (K := K) (L := L) n sigma ha
  simpa [galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul,
    map_sub, map_one] using hstable

/-- The restricted actual Galois action on any subgroup whose carrier is
the standard `V^n`. -/
@[implicit_reducible]
def chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n) :
    MulDistribMulAction (Gal(L/K)) V := by
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  exact subgroupMulDistribMulActionOfStable (Gal(L/K)) 𝒪[L]ˣ V
    (by
      intro sigma a ha
      change sigma • (a : 𝒪[L]ˣ) ∈ (V : Set 𝒪[L]ˣ)
      rw [hV]
      exact galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
        (K := K) (L := L) n sigma (hV ▸ ha))

/-- The induced Galois action on the principal-unit subgroup agrees with the ambient action. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction_smul
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L/K)) (a : V) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    ((sigma • a : V) : 𝒪[L]ˣ) =
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      sigma • (a : 𝒪[L]ˣ) :=
  rfl

/-- Coercing the subgroup Tate norm gives the ambient product over the Galois group. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (a : V) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ((tateNorm (Gal(L/K)) V a : V) : 𝒪[L]ˣ) =
      tateNorm (Gal(L/K)) 𝒪[L]ˣ (a : 𝒪[L]ˣ) := by
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  unfold tateNorm
  change V.subtype (∏ g : Gal(L/K), g • a) =
    ∏ g : Gal(L/K), g • (a : 𝒪[L]ˣ)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro g _hg
  rfl

/-- Coercion commutes with the `σ - 1` operation on the principal-unit subgroup. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L/K)) (a : V) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ((sigmaMinusOne (Gal(L/K)) V sigma a : V) : 𝒪[L]ˣ) =
      sigmaMinusOne (Gal(L/K)) 𝒪[L]ˣ sigma (a : 𝒪[L]ˣ) := by
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rfl

/-- The quotient action on `𝒪_Lˣ / V^n`, descended from the actual integer-unit
Galois action. -/
@[implicit_reducible]
def chosenNormalBasisIntegerUnitsQuotMulDistribMulAction
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n) :
    MulDistribMulAction (Gal(L/K)) (𝒪[L]ˣ ⧸ V) := by
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  exact quotientMulDistribMulActionOfSubgroupStable
    (Gal(L/K)) 𝒪[L]ˣ V (by
      intro sigma a ha
      change a ∈ (V : Set 𝒪[L]ˣ) at ha
      change sigma • a ∈ (V : Set 𝒪[L]ˣ)
      rw [hV] at ha ⊢
      exact galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
        (K := K) (L := L) n sigma ha)

/-- Inclusion of a chosen normal-basis principal-unit subgroup into all
integer units. -/
def chosenNormalBasisPrincipalUnitSubgroupInclusion
    (V : Subgroup 𝒪[L]ˣ) : V →* 𝒪[L]ˣ :=
  V.subtype

/-- The principal-unit subgroup inclusion returns the underlying integer unit. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_apply
    (V : Subgroup 𝒪[L]ˣ) (a : V) :
    chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V a = a :=
  rfl

/-- Projection of integer units to the quotient by `V^n`. -/
def chosenNormalBasisIntegerUnitsQuotientMap
    (V : Subgroup 𝒪[L]ˣ) : 𝒪[L]ˣ →* (𝒪[L]ˣ ⧸ V) :=
  QuotientGroup.mk' V

/-- The integer-unit quotient map sends a unit to its quotient class. -/
@[simp]
theorem chosenNormalBasisIntegerUnitsQuotientMap_apply
    (V : Subgroup 𝒪[L]ˣ) (a : 𝒪[L]ˣ) :
    chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a =
      QuotientGroup.mk a :=
  rfl

/-- Inclusion of the principal-unit subgroup is Galois equivariant. -/
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L/K)) (a : V) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V (sigma • a) =
      sigma • chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V a :=
  rfl

/-- The quotient map on integer units is Galois equivariant. -/
theorem chosenNormalBasisIntegerUnitsQuotientMap_equivariant
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L/K)) (a : 𝒪[L]ˣ) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
    chosenNormalBasisIntegerUnitsQuotientMap (L := L) V (sigma • a) =
      sigma • chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a := by
  rfl

/-- Inclusion of the principal-unit subgroup is injective. -/
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_injective
    (V : Subgroup 𝒪[L]ˣ) :
    Function.Injective (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V) :=
  Subtype.val_injective

/-- Every integer-unit quotient class has a representative. -/
theorem chosenNormalBasisIntegerUnitsQuotientMap_surjective
    (V : Subgroup 𝒪[L]ˣ) :
    Function.Surjective (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V) :=
  QuotientGroup.mk'_surjective V

/-- Exactness at the integer-unit term of `1 → V^n → 𝒪_Lˣ → 𝒪_Lˣ/V^n
→ 1`. -/
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_range_eq_ker_quotient
    (V : Subgroup 𝒪[L]ˣ) :
    MonoidHom.range (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V) =
      MonoidHom.ker (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V) := by
  ext a
  change (∃ v : V, (v : 𝒪[L]ˣ) = a) ↔ QuotientGroup.mk' V a = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨v, rfl⟩
    exact v.2
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩

end
end LocalClassFieldTheory
