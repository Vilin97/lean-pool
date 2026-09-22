/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateComparison

/-! # Unit Cohomology Axiom -/
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: the unit-cohomology axiom

The coefficient group in the unit-cohomology axiom is the actual unit subgroup `U_L`, with
the action of the actual quotient `G_K / G_L`.  The two Tate groups are the
homology objects of the finite-cyclic norm complexes.
-/

noncomputable section

open CategoryTheory

universe u

section Generic

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite cyclic extension of a bundled finite abstract field.  The
generator and its cyclicity proof travel with the finite normal extension. -/
structure FiniteCyclicSubextension (K : FiniteAbstractField G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.field.toSubgroup
  /-- The top-field subgroup is normal inside the base-field subgroup. -/
  normal : (extensionSubgroup K.field field below).Normal
  /-- The relative Galois quotient is finite. -/
  finite : Finite (K.field.toSubgroup ⧸
    extensionSubgroup K.field field below)
  /-- A chosen generator of the relative Galois quotient. -/
  generator : K.field.toSubgroup ⧸ extensionSubgroup K.field field below
  /-- Every quotient element is a power of the chosen generator. -/
  generates : ∀ x, x ∈ Subgroup.zpowers generator

namespace FiniteCyclicSubextension

variable {K : FiniteAbstractField G}

/-- Forget the cyclic generator and normality, retaining the underlying finite
abstract extension. -/
@[implicit_reducible]
def toFiniteAbstractExtension (E : FiniteCyclicSubextension K) :
    DegreeData.FiniteAbstractExtension G where
  field := E.field
  base := K.field
  below := E.below
  finiteQuotient := E.finite

/-- Structural unramifiedness of the underlying finite extension. -/
def IsUnramified (E : FiniteCyclicSubextension K) (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the underlying finite extension. -/
def IsTotallyRamified (E : FiniteCyclicSubextension K)
    (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsTotallyRamified D

/-- Retain the finite-over-base endpoint bundles as well as the relative
finite quotient. -/
@[implicit_reducible]
noncomputable def toFiniteAbstractFieldExtension
    (E : FiniteCyclicSubextension K) : FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
    E.finite
  exact FiniteAbstractFieldExtension.ofInclusion E.field K E.below

/-- A finite cyclic subextension supplies normality of its representing subgroup. -/
instance (E : FiniteCyclicSubextension K) :
    (extensionSubgroup K.field E.field E.below).Normal :=
  E.normal

/-- A finite cyclic subextension supplies finiteness of its Galois quotient. -/
instance (E : FiniteCyclicSubextension K) :
    Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  E.finite

/-- The finite quotient of a cyclic subextension carries its canonical `Fintype`. -/
noncomputable instance (E : FiniteCyclicSubextension K) :
    Fintype (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  Fintype.ofFinite _

end FiniteCyclicSubextension

end Generic

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- A finite cyclic extension together with the assertion that it is
unramified for the fixed degree datum. -/
structure FiniteUnramifiedCyclicExtension
    (D : DegreeData G) (K : FiniteAbstractField G)
    extends FiniteCyclicSubextension K where
  /-- The underlying finite cyclic extension is unramified for `D`. -/
  unramified : toFiniteCyclicSubextension.IsUnramified D

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- Forget cyclic and unramified structure while retaining both finite
endpoint fields and the relative finite quotient. -/
@[implicit_reducible]
noncomputable def toFiniteAbstractFieldExtension
    (E : FiniteUnramifiedCyclicExtension D K) :
    FiniteAbstractFieldExtension G :=
  E.toFiniteCyclicSubextension.toFiniteAbstractFieldExtension

/-- The unramified proof transported to the canonical finite field-extension
bundle. -/
theorem toFiniteAbstractFieldExtension_isUnramified
    (E : FiniteUnramifiedCyclicExtension D K) :
    E.toFiniteAbstractFieldExtension.IsUnramified D := by
  exact E.unramified

/-- A finite unramified cyclic extension supplies normality of its representing subgroup. -/
instance (E : FiniteUnramifiedCyclicExtension D K) :
    (extensionSubgroup K.field E.field E.below).Normal :=
  E.normal

/-- The quotient over `K` attached to a finite unramified cyclic extension is finite. -/
instance (E : FiniteUnramifiedCyclicExtension D K) :
    Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  E.finite

/-- The absolute quotient attached to a finite unramified cyclic extension is finite. -/
noncomputable instance (E : FiniteUnramifiedCyclicExtension D K) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.field (le_baseField E.field)) :=
  relativeTowerQuotientFinite (baseField G) K.field E.field E.below
    (le_baseField K.field)

/-- The finite quotient over `K` carries the canonical `Fintype` structure. -/
noncomputable instance (E : FiniteUnramifiedCyclicExtension D K) :
    Fintype (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  Fintype.ofFinite _

end FiniteUnramifiedCyclicExtension

namespace FiniteCyclicSubextension

variable {K : FiniteAbstractField G}

/-- The fixed coefficient representation attached to a bundled cyclic
extension. -/
noncomputable def fixedRepresentation (E : FiniteCyclicSubextension K)
    (A : Rep ℤ G) :
    Rep ℤ (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  extensionFixedRepresentation A K.field E.field E.below E.normal

end FiniteCyclicSubextension

/-- Elementwise content of `H⁰(Q,M)=0`: every element fixed by a cyclic
generator is an actual norm. -/
theorem exists_norm_eq_of_tateHZero_isZero
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (M : Rep ℤ Q) (g : Q) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hzero : Limits.IsZero (tateCohomology M 0)) :
    ∀ x : M.V, M.ρ g x = x → ∃ y : M.V, M.norm.hom y = x := by
  let : IsCyclic Q := isCyclic_of_generator g hg
  let : CommGroup Q := IsCyclic.commGroup (α := Q)
  let S := Rep.FiniteCyclicGroup.normHomCompSub M g
  have hSzero : Limits.IsZero S.homology := by
    exact Limits.IsZero.of_iso hzero
      (TateCohomology.isoFiniteCyclicZero M g hg).symm
  have hS : S.Exact := (S.exact_iff_isZero_homology).2 hSzero
  intro x hx
  have hxker : S.g x = 0 := by
    change M.ρ g x - x = 0
    exact sub_eq_zero.mpr hx
  rcases (S.moduleCat_exact_iff.mp hS x hxker) with ⟨y, hy⟩
  exact ⟨y, hy⟩

namespace ValuationData

/-- Normalized valuation is invariant under the Galois action in a finite
tower.  The proof uses transitivity of the actual norm and its invariance
under the normal-extension action. -/
theorem valuationAt_normalExtensionAction
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (k : E.base.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field.field) :
    v.valuationAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) =
      v.valuationAt E.field a := by
  apply Subtype.ext
  apply zHatMulNat_injective (E.field.residueDegree D).property
  calc
    (E.field.residueDegree D : ℕ) •
        ((v.valuationAt E.field
          (normalExtensionAction A E.base.field E.field.field E.below
            hnormal k a) : v.valueGroup) : ZHat) =
      v.normCompositeAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) :=
        v.residueDegree_nsmul_dividedAt E.field _
    _ = v.normCompositeAt E.field a := by
      change v.toAddMonoidHom
          (normToBase A E.field.field
            (normalExtensionAction A E.base.field E.field.field E.below
              hnormal k a)) =
        v.toAddMonoidHom (normToBase A E.field.field a)
      congr 1
      let T : DegreeData.FiniteTower G := {
        top := E.field.field
        middle := E.base.field
        base := baseField G
        top_le_middle := E.below
        middle_le_base := le_baseField E.base.field
        finiteTopQuotient := E.finiteQuotient
        finiteBaseQuotient := E.base.finite }
      calc
        relativeNorm A (baseField G) E.field.field
            (E.below.trans (le_baseField E.base.field))
            (normalExtensionAction A E.base.field E.field.field E.below
              hnormal k a) =
          relativeNorm A (baseField G) E.base.field
            (le_baseField E.base.field)
            (relativeNorm A E.base.field E.field.field E.below
              (normalExtensionAction A E.base.field E.field.field E.below
                hnormal k a)) :=
          (T.norm_trans_apply A _).symm
        _ = relativeNorm A (baseField G) E.base.field
            (le_baseField E.base.field)
            (relativeNorm A E.base.field E.field.field E.below a) := by
          rw [relativeNorm_normalExtensionAction A E.base.field E.field.field
            E.below hnormal k a]
        _ = relativeNorm A (baseField G) E.field.field
            (E.below.trans (le_baseField E.base.field)) a :=
          T.norm_trans_apply A a
    _ = (E.field.residueDegree D : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ZHat) :=
      (v.residueDegree_nsmul_dividedAt E.field a).symm

/-- The action of `G_K` on the actual unit subgroup `U_L`. -/
noncomputable def unitActionLinearMap
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (k : E.base.field.toSubgroup) :
    v.unitAddSubgroup E.field →ₗ[ℤ] v.unitAddSubgroup E.field where
  toFun u := ⟨normalExtensionAction A E.base.field E.field.field E.below
      hnormal k u.1, by
    rw [mem_unitAddSubgroup_iff,
      v.valuationAt_normalExtensionAction E hnormal k u.1]
    exact u.2⟩
  map_add' u w := by
    apply Subtype.ext
    apply Subtype.ext
    change A.ρ k.1 (u.1.1 + w.1.1) = A.ρ k.1 u.1.1 + A.ρ k.1 w.1.1
    exact map_add (A.ρ k.1) _ _
  map_smul' n u := by
    apply Subtype.ext
    apply Subtype.ext
    change A.ρ k.1 (n • u.1.1) = n • A.ρ k.1 u.1.1
    exact map_zsmul (A.ρ k.1) n u.1.1

/-- The `G_K`-representation on `U_L` before descending through `G_L`. -/
noncomputable def unitRepresentationOverK
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal) :
    Rep ℤ E.base.field.toSubgroup :=
  Rep.of
    { toFun := fun k => v.unitActionLinearMap E hnormal k
      map_one' := by
        ext u
        change A.ρ (1 : G) u.1.1 = u.1.1
        simp
      map_mul' := by
        intro k₁ k₂
        ext u
        change A.ρ (k₁.1 * k₂.1) u.1.1 =
          A.ρ k₁.1 (A.ρ k₂.1 u.1.1)
        rw [map_mul]
        rfl }

private theorem unitRepresentationOverK_isTrivialOnExtension
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal) :
    Representation.IsTrivial
      ((v.unitRepresentationOverK E hnormal).ρ.comp
        (extensionSubgroup E.base.field E.field.field E.below).subtype) := by
  constructor
  intro s
  ext u
  apply Subtype.ext
  apply Subtype.ext
  change A.ρ s.1.1 u.1.1 = u.1.1
  exact u.1.2
    ⟨s.1.1, (mem_extensionSubgroup_iff E.base.field E.field.field E.below s.1).1 s.2⟩

/-- The actual quotient representation on the unit group `U_L`. -/
noncomputable def unitRepresentation
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal) :
    Rep ℤ (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below) := by
  letI := hnormal
  letI : Representation.IsTrivial
      ((v.unitRepresentationOverK E hnormal).ρ.comp
        (extensionSubgroup E.base.field E.field.field E.below).subtype) :=
    v.unitRepresentationOverK_isTrivialOnExtension E hnormal
  exact (v.unitRepresentationOverK E hnormal).ofQuotient
    (extensionSubgroup E.base.field E.field.field E.below)

end ValuationData

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- The unit representation carried by a bundled finite unramified cyclic
extension. -/
noncomputable def unitRepresentation
    (E : FiniteUnramifiedCyclicExtension D K) (v : ValuationData D A) :
    Rep ℤ (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  v.unitRepresentation E.toFiniteAbstractFieldExtension E.normal

end FiniteUnramifiedCyclicExtension

namespace ValuationData

/-- The quotient unit representation acts on a representative through the original unit action. -/
theorem unitRepresentation_quotient_mk_apply
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (k : E.base.field.toSubgroup) (u : v.unitAddSubgroup E.field) :
    (v.unitRepresentation E hnormal).ρ
        ((QuotientGroup.mk'
          (extensionSubgroup E.base.field E.field.field E.below)) k) u =
      v.unitActionLinearMap E hnormal k u :=
  rfl

/-- Inclusion of units along an unramified finite extension. -/
def unitInclusion
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hUnramified : E.IsUnramified D) :
    v.unitAddSubgroup E.base →+ v.unitAddSubgroup E.field where
  toFun u := ⟨fixedFieldInclusion A E.base.field E.field.field E.below u.1, by
    rw [mem_unitAddSubgroup_iff]
    exact (v.valuationAt_fixedFieldInclusion_of_unramified E hUnramified u.1).trans
      u.2⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

/-- On underlying coefficients, the quotient action on `U_L` is the same
coset action used in the relative norm. -/
theorem unitRepresentation_action_coe
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (q : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (u : v.unitAddSubgroup E.field) :
    (((v.unitRepresentation E hnormal).ρ q u).1 :
        ambientFixedAddSubgroup A E.field.field).1 =
      relativeCosetAction A E.base.field E.field.field E.below u.1 q := by
  refine Quotient.inductionOn' q ?_
  intro k
  rw [relativeCosetAction_mk]
  rfl

/-- The representation norm on `U_L` is the relative field norm on
underlying coefficients. -/
theorem unitRepresentation_norm_coe
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (u : v.unitAddSubgroup E.field) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
    ((((v.unitRepresentation E hnormal).norm.hom u).1 :
        ambientFixedAddSubgroup A E.field.field) : A.V) =
      ((relativeNorm A E.base.field E.field.field E.below u.1 :
        ambientFixedAddSubgroup A E.base.field) : A.V) := by
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  rw [relativeNorm_apply_coe]
  change
    (((Representation.norm (v.unitRepresentation E hnormal).ρ) u).1 :
      ambientFixedAddSubgroup A E.field.field).1 =
      relativeNormValue A E.base.field E.field.field E.below u.1
  rw [Representation.norm, relativeNormValue]
  let coeToAmbient : v.unitAddSubgroup E.field →+ A.V :=
    (ambientFixedAddSubgroup A E.field.field).subtype.comp
      (v.unitAddSubgroup E.field).subtype
  change coeToAmbient
      ((∑ q, (v.unitRepresentation E hnormal).ρ q) u) =
    ∑ q, relativeCosetAction A E.base.field E.field.field E.below u.1 q
  refine (congrArg coeToAmbient (LinearMap.sum_apply Finset.univ
    (fun q : E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below =>
      (v.unitRepresentation E hnormal).ρ q) u)).trans ?_
  refine (map_sum coeToAmbient _ _).trans ?_
  apply Finset.sum_congr rfl
  intro q _
  exact v.unitRepresentation_action_coe E hnormal q u

/-- Actual `H⁰=0` eliminator needed after the reciprocity construction: every unit of
`K` is the relative norm of a unit of an unramified Galois extension `L`. -/
theorem exists_unit_relativeNorm_eq_of_tateHZero_isZero
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (hUnramified : E.IsUnramified D)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
    Limits.IsZero
        (tateCohomology (v.unitRepresentation E hnormal) 0) →
      ∀ u : v.unitAddSubgroup E.base, ∃ ε : v.unitAddSubgroup E.field,
        relativeNorm A E.base.field E.field.field E.below ε.1 = u.1 := by
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  intro hzero u
  let U := v.unitRepresentation E hnormal
  let uL := v.unitInclusion E hUnramified u
  have hfixed : U.ρ g uL = uL := by
    refine Quotient.inductionOn' g ?_
    intro k
    apply Subtype.ext
    apply Subtype.ext
    change A.ρ k.1 u.1.1 = u.1.1
    exact u.1.2 k
  obtain ⟨ε, hε⟩ := exists_norm_eq_of_tateHZero_isZero
    U g hg hzero uL hfixed
  refine ⟨ε, ?_⟩
  apply Subtype.ext
  calc
    ((relativeNorm A E.base.field E.field.field E.below ε.1 :
        ambientFixedAddSubgroup A E.base.field) : A.V) =
        ((((v.unitRepresentation E hnormal).norm.hom ε).1 :
          ambientFixedAddSubgroup A E.field.field) : A.V) :=
      (v.unitRepresentation_norm_coe E hnormal ε).symm
    _ = ((uL.1 : ambientFixedAddSubgroup A E.field.field) : A.V) :=
      congrArg
        (fun z : v.unitAddSubgroup E.field =>
          ((z.1 : ambientFixedAddSubgroup A E.field.field) : A.V)) hε
    _ = u.1.1 := rfl

/-- Actual `H⁻¹=0` eliminator on units: a unit of relative norm zero is
in the image of `g-1`. -/
theorem exists_unit_sigma_sub_eq_of_tateHMinusOne_isZero
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
    Limits.IsZero
        (tateCohomology (v.unitRepresentation E hnormal) (-1)) →
      ∀ u : (v.unitRepresentation E hnormal).V,
        (v.unitRepresentation E hnormal).norm.hom u = 0 →
        ∃ ε : (v.unitRepresentation E hnormal).V,
          (v.unitRepresentation E hnormal).ρ g ε - ε = u := by
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  intro hzero u hu
  let U := v.unitRepresentation E hnormal
  exact CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
    U g hg hzero u hu

/-- **the unit-cohomology axiom.** For every finite unramified Galois extension `L/K`,
`H⁰(G(L/K),U_L)` and `H⁻¹(G(L/K),U_L)` vanish.

This is a predicate on the abstract valuation datum.  It is the source axiom
used in the subsequent proofs of independence and multiplicativity;
it is not introduced as a Lean axiom. -/
def SatisfiesUnramifiedUnitCohomology
    (D : DegreeData G) (v : ValuationData D A) : Prop :=
  ∀ (K : FiniteAbstractField G)
    (E : FiniteUnramifiedCyclicExtension D K),
    Limits.IsZero (tateCohomology (E.unitRepresentation v) 0) ∧
      Limits.IsZero (tateCohomology (E.unitRepresentation v) (-1))

end ValuationData

end
end ClassFormation
