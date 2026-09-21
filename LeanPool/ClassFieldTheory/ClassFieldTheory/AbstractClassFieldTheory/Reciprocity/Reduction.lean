/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse

/-! # Reduction -/
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity theorem: actual reduction maps

This file isolates the field- and quotient-theoretic content of the three
reductions.  In particular, the Sylow reduction uses an
intermediate field which need not be normal over the base.  We therefore
construct its norm map without a normality assumption on the intermediate
extension.

The reciprocity homomorphisms themselves belong to the finite reciprocity equivalence.  The
lemmas below only construct the actual arrows and prove the algebraic diagram
chases which will be applied to those homomorphisms.
-/

noncomputable section

universe u

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The norm arrow
`A_M / N_{L/M} A_L → A_K / N_{L/K} A_L` for the actual intermediate
field cut out by `S ≤ G(L/K)`.  No normality of `M/K` is used. -/
def intermediateNormMap (A : Rep ℤ G) (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
      L.finite
    FiniteNormQuotient A M L.field hLM →+
      FiniteNormQuotient A K L.field L.below := by
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  letI : Finite (M.toSubgroup ⧸
      extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    L.intermediateField_finite S
  exact finiteReciprocityNaturalityNormMap A K M L.field L.field
    L.below hLM hMK le_rfl

/-- Representative formula for the nonnormal-intermediate norm arrow. -/
@[simp]
theorem intermediateNormMap_finiteNormClass (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (a : ambientFixedAddSubgroup A (L.intermediateField S)) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K
        (L.intermediateField S) (L.intermediateField_le_base S)) :=
      L.intermediateField_finite S
    L.intermediateNormMap A S
        (finiteNormClass A (L.intermediateField S) L.field
          (L.field_le_intermediateField S) a) =
      finiteNormClass A K L.field L.below
        (relativeNorm A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  let : Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) :=
    L.extension_over_intermediate_finite S
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K
      (L.intermediateField S) (L.intermediateField_le_base S)) :=
    L.intermediateField_finite S
  exact finiteReciprocityNaturalityNormMap_finiteNormClass A K
    (L.intermediateField S) L.field L.field L.below
    (L.field_le_intermediateField S) (L.intermediateField_le_base S) le_rfl a

/-- Inclusion of fixed elements, descended to the two actual norm
quotients.  This is the map `i` in the Sylow argument. -/
def intermediateNormQuotientInclusion (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    FiniteNormQuotient A K L.field L.below →+
      FiniteNormQuotient A (L.intermediateField S) L.field
        (L.field_le_intermediateField S) := by
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  letI : (extensionSubgroup K L.field L.below).Normal := L.normal
  letI : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  letI : Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) :=
    L.extension_over_intermediate_finite S
  exact transferNormNaturalityNormQuotientInclusion A K (L.intermediateField S)
    L.field (L.field_le_intermediateField S)
      (L.intermediateField_le_base S)

/-- Representative formula for the inclusion used in the Sylow
reduction. -/
@[simp]
theorem intermediateNormQuotientInclusion_finiteNormClass (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    L.intermediateNormQuotientInclusion A S
        (finiteNormClass A K L.field L.below a) =
      finiteNormClass A (L.intermediateField S) L.field
        (L.field_le_intermediateField S)
        (fixedFieldInclusion A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  let : (extensionSubgroup K L.field L.below).Normal := L.normal
  let : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let : Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) :=
    L.extension_over_intermediate_finite S
  exact transferNormNaturality_normQuotientInclusion_finiteNormClass A K
    (L.intermediateField S) L.field (L.field_le_intermediateField S)
      (L.intermediateField_le_base S) a

/-- The exact identity `N_{M/K} ∘ i = [M:K]`, now for an
arbitrary (possibly nonnormal) intermediate field. -/
theorem intermediateNormMap_comp_inclusion (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    ∀ q : FiniteNormQuotient A K L.field L.below,
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K
        (L.intermediateField S) (L.intermediateField_le_base S)) :=
      L.intermediateField_finite S
    L.intermediateNormMap A S
        (L.intermediateNormQuotientInclusion A S q) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • q := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  intro q
  let : (extensionSubgroup K L.field L.below).Normal := L.normal
  let : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let : Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) :=
    L.extension_over_intermediate_finite S
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K
      (L.intermediateField S) (L.intermediateField_le_base S)) :=
    L.intermediateField_finite S
  refine FiniteNormQuotient.induction_on A K L.field L.below q ?_
  intro a
  rw [intermediateNormQuotientInclusion_finiteNormClass,
    intermediateNormMap_finiteNormClass]
  rw [show relativeNorm A K (L.intermediateField S)
      (L.intermediateField_le_base S)
        (fixedFieldInclusion A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • a by
    change relativeNorm A
        (L.intermediateFiniteAbstractExtension S).base
        (L.intermediateFiniteAbstractExtension S).field
        (L.intermediateFiniteAbstractExtension S).below
        (fixedFieldInclusion A
          (L.intermediateFiniteAbstractExtension S).base
          (L.intermediateFiniteAbstractExtension S).field
          (L.intermediateFiniteAbstractExtension S).below a) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • a
    exact relativeNorm_fixedFieldInclusion A
      (L.intermediateFiniteAbstractExtension S) a]
  exact finiteNormClass_nsmul A K L.field L.below _ a

end FiniteGaloisSubextension

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The inclusion `G(L/M) → G(L/K)` for the actual intermediate field,
obtained from `G(L/M) ≃ S` followed by the subgroup inclusion. -/
def lowerInclusionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S) →*
      L.extensionQuotient :=
  S.subtype.comp (L.lowerQuotientEquiv S).toMonoidHom

/-- Representative formula for the actual lower inclusion. -/
@[simp]
theorem lowerInclusionHom_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    L.lowerInclusionHom S (QuotientGroup.mk m) =
      (QuotientGroup.mk'
        (extensionSubgroup K L.field L.below))
          ⟨m.1, L.intermediateField_le_base S m.property⟩ := by
  exact L.lowerQuotientEquiv_mk_coe S m

/-- The lower inclusion is injective. -/
theorem lowerInclusionHom_injective (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    Function.Injective (L.lowerInclusionHom S) := by
  intro x y hxy
  apply (L.lowerQuotientEquiv S).injective
  exact Subtype.ext hxy

/-- Every lower quotient of a cyclic extension is cyclic. -/
theorem lowerQuotient_isCyclic (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [IsCyclic L.extensionQuotient] :
    IsCyclic
      ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
  (L.lowerQuotientEquiv S).isCyclic.2 inferInstance

/-- The actual restriction arrow `G(L/K) → G(M/K)` attached to a normal
subgroup `S ◁ G(L/K)`, expressed through the third-isomorphism
identification constructed in `IntermediateExtension`. -/
def upperRestrictionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.extensionQuotient →*
      K.toSubgroup ⧸ extensionSubgroup K (L.intermediateField S)
        (L.intermediateField_le_base S) :=
  (L.upperQuotientEquiv S).toMonoidHom.comp (QuotientGroup.mk' S)

/-- Representative formula for the actual upper restriction arrow. -/
@[simp]
theorem upperRestrictionHom_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] (k : K.toSubgroup) :
    L.upperRestrictionHom S
        (QuotientGroup.mk k : L.extensionQuotient) =
      QuotientGroup.mk k := by
  exact L.upperQuotientEquiv_mk_mk S k

/-- Restriction to a normal intermediate field is surjective. -/
theorem upperRestrictionHom_surjective (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    Function.Surjective (L.upperRestrictionHom S) :=
  (L.upperQuotientEquiv S).surjective.comp
    (QuotientGroup.mk'_surjective S)

/-- Every upper quotient of a cyclic extension is cyclic. -/
theorem upperQuotient_isCyclic (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    [IsCyclic L.extensionQuotient] :
    IsCyclic
      (K.toSubgroup ⧸ extensionSubgroup K (L.intermediateField S)
        (L.intermediateField_le_base S)) := by
  have hsource : IsCyclic (L.extensionQuotient ⧸ S) :=
    isCyclic_of_surjective (QuotientGroup.mk' S)
      (QuotientGroup.mk'_surjective S)
  exact (L.upperQuotientEquiv S).isCyclic.1 hsource

/-- Its kernel is exactly the subgroup defining the intermediate field. -/
theorem upperRestrictionHom_eq_one_iff (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    (q : L.extensionQuotient) :
    L.upperRestrictionHom S q = 1 ↔ q ∈ S := by
  change L.upperQuotientEquiv S
      (L.upperQuotientMk S q) = 1 ↔ q ∈ S
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff q).1
    change L.upperQuotientMk S q = 1
    apply (L.upperQuotientEquiv S).injective
    exact h.trans ((L.upperQuotientEquiv S).map_one).symm
  · intro h
    have hmk : L.upperQuotientMk S q = 1 := by
      change (QuotientGroup.mk' S) q = 1
      exact (QuotientGroup.eq_one_iff q).2 h
    exact (congrArg (L.upperQuotientEquiv S) hmk).trans
      (L.upperQuotientEquiv S).map_one

/-- Exactness of the actual upper row for an intermediate field, in
additive form for direct use with the reciprocity homomorphisms. -/
theorem intermediateGalois_exact (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    Function.Exact
      (MonoidHom.toAdditive (L.lowerInclusionHom S))
      (MonoidHom.toAdditive (L.upperRestrictionHom S)) := by
  intro q
  constructor
  · intro hq
    have hres : L.upperRestrictionHom S q.toMul = 1 := by
      exact Additive.ofMul.injective (by simpa using hq)
    have hmem : q.toMul ∈ S :=
      (L.upperRestrictionHom_eq_one_iff S q.toMul).1 hres
    let s : S := ⟨q.toMul, hmem⟩
    refine ⟨Additive.ofMul ((L.lowerQuotientEquiv S).symm s), ?_⟩
    apply Additive.toMul.injective
    change
      ↑(L.lowerQuotientEquiv S ((L.lowerQuotientEquiv S).symm s)) = q.toMul
    exact congrArg Subtype.val
      ((L.lowerQuotientEquiv S).apply_symm_apply s)
  · rintro ⟨x, rfl⟩
    apply Additive.toMul.injective
    change L.upperRestrictionHom S (L.lowerInclusionHom S x.toMul) = 1
    apply (L.upperRestrictionHom_eq_one_iff S _).2
    change (((L.lowerQuotientEquiv S) x.toMul : S) :
      L.extensionQuotient) ∈ S
    exact Subtype.property _

/-- The maximal abelian intermediate field in the first reduction is the
actual field cut out by the commutator subgroup of `G(L/K)`. -/
def abelianIntermediateField (L : FiniteGaloisSubextension K) :
    ClosedSubgroup G :=
  L.intermediateField (commutator L.extensionQuotient)

/-- Normality of the maximal abelian intermediate extension. -/
instance abelianIntermediateField_normalInstance
    (L : FiniteGaloisSubextension K) :
    (extensionSubgroup K L.abelianIntermediateField
      (L.intermediateField_le_base
        (commutator L.extensionQuotient))).Normal := by
  change (extensionSubgroup K
    (L.intermediateField (commutator L.extensionQuotient))
      (L.intermediateField_le_base
        (commutator L.extensionQuotient))).Normal
  exact L.intermediateField_normal
    (commutator L.extensionQuotient) inferInstance

/-- Restriction to the maximal abelian intermediate field. -/
def abelianRestrictionHom (L : FiniteGaloisSubextension K) :
    L.extensionQuotient →*
      K.toSubgroup ⧸ extensionSubgroup K L.abelianIntermediateField
        (L.intermediateField_le_base
          (commutator L.extensionQuotient)) :=
  L.upperRestrictionHom (commutator L.extensionQuotient)

/-- The first reduction's exact upper-row assertion: the kernel of
restriction to `L^ab` is the commutator subgroup. -/
theorem abelianRestrictionHom_eq_one_iff
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    L.abelianRestrictionHom q = 1 ↔
      q ∈ commutator L.extensionQuotient :=
  L.upperRestrictionHom_eq_one_iff (commutator L.extensionQuotient) q

/-- A jointly faithful family of quotient coordinates gives a jointly
faithful family of actual restriction maps to the corresponding
intermediate fields. -/
theorem upperRestrictionHom_jointlyFaithful
    (L : FiniteGaloisSubextension K)
    {I : Type*} {C : I → Type*} [∀ i, Group (C i)]
    (f : ∀ i, L.extensionQuotient →* C i)
    (hfaithful : (⨅ i, MonoidHom.ker (f i)) = ⊥)
    (q : L.extensionQuotient) :
    (∀ i, L.upperRestrictionHom (MonoidHom.ker (f i)) q = 1) ↔
      q = 1 := by
  constructor
  · intro hq
    have hmem : q ∈ ⨅ i, MonoidHom.ker (f i) := by
      rw [Subgroup.mem_iInf]
      intro i
      exact (L.upperRestrictionHom_eq_one_iff
        (MonoidHom.ker (f i)) q).1 (hq i)
    rw [hfaithful, Subgroup.mem_bot] at hmem
    exact hmem
  · rintro rfl
    intro i
    exact map_one _

/-- For a coordinate homomorphism, the actual restriction map has exactly
the same kernel. -/
theorem upperRestrictionHom_ker_factor
    (L : FiniteGaloisSubextension K) {C : Type*} [Group C]
    (f : L.extensionQuotient →* C) (q : L.extensionQuotient) :
    L.upperRestrictionHom (MonoidHom.ker f) q = 1 ↔ f q = 1 := by
  rw [L.upperRestrictionHom_eq_one_iff (MonoidHom.ker f) q]
  exact MonoidHom.mem_ker

/-- A finite abelian `G(L/K)` supplies the actual cyclic intermediate
extensions used in the second reduction.  The coordinate kernels have
trivial intersection, and the corresponding groups `G(Mᵢ/K)` are finite
cyclic. -/
theorem exists_cyclicIntermediateFields
    (L : FiniteGaloisSubextension K)
    [IsMulCommutative L.extensionQuotient] :
    ∃ (I : Type 0) (_ : Fintype I) (m : I → ℕ),
      (∀ i, 1 < m i) ∧
      ∃ f : ∀ i,
          L.extensionQuotient →* Multiplicative (ZMod (m i)),
        (∀ i, Function.Surjective (f i)) ∧
        (⨅ i, MonoidHom.ker (f i)) = ⊥ ∧
        (∀ i, IsCyclic
          (K.toSubgroup ⧸ extensionSubgroup K
            (L.intermediateField (MonoidHom.ker (f i)))
            (L.intermediateField_le_base (MonoidHom.ker (f i))))) ∧
        (∀ i, Finite
          (K.toSubgroup ⧸ extensionSubgroup K
            (L.intermediateField (MonoidHom.ker (f i)))
            (L.intermediateField_le_base (MonoidHom.ker (f i))))) := by
  let : CommGroup L.extensionQuotient :=
    open scoped IsMulCommutative in inferInstance
  obtain ⟨I, hI, m, hm, f, hf, hfaithful⟩ :=
    finiteCommGroup_exists_jointlyFaithful_cyclic_factors
      L.extensionQuotient
  let : Fintype I := hI
  refine ⟨I, hI, m, hm, f, hf, hfaithful, ?_, ?_⟩
  · intro i
    let e : L.extensionQuotient ⧸ MonoidHom.ker (f i) ≃*
        Multiplicative (ZMod (m i)) :=
      QuotientGroup.quotientKerEquivOfSurjective (f i) (hf i)
    have hsource : IsCyclic
        (L.extensionQuotient ⧸ MonoidHom.ker (f i)) :=
      e.isCyclic.2 inferInstance
    exact (L.upperQuotientEquiv (MonoidHom.ker (f i))).isCyclic.1 hsource
  · intro i
    exact L.intermediateField_finite (MonoidHom.ker (f i))

/-! ## The maximal unramified subextension in the third reduction -/

/-- The inertia subgroup of `G(L/K)`: the image of `I_K` in the actual
finite quotient.  Its fixed field is `L ∩ K̃` in the notation of. -/
def inertiaImage (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    Subgroup L.extensionQuotient :=
  (D.fieldInertiaWithin K).map
    (QuotientGroup.mk' (extensionSubgroup K L.field L.below))

omit [IsTopologicalGroup G] in
/-- The inertia image is normal, since it is the image of the normal
inertia subgroup under a surjective quotient map. -/
theorem inertiaImage_normal (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : (L.inertiaImage D).Normal := by
  exact (inferInstance : (D.fieldInertiaWithin K).Normal).map
    (QuotientGroup.mk' (extensionSubgroup K L.field L.below))
    (QuotientGroup.mk'_surjective
      (extensionSubgroup K L.field L.below))

/-- The inertia image in a finite Galois quotient is normal. -/
instance inertiaImage_normalInstance (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : (L.inertiaImage D).Normal :=
  L.inertiaImage_normal D

/-- The actual maximal unramified subextension `M = L ∩ K̃`. -/
def maximalUnramifiedSubextension (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : ClosedSubgroup G :=
  L.intermediateField (L.inertiaImage D)

/-- `M/K` as an actual finite Galois extension. -/
def maximalUnramifiedFiniteGalois (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : FiniteGaloisSubextension K :=
  L.intermediateFiniteGalois (L.inertiaImage D)
    (L.inertiaImage_normal D)

/-- The constructed `M/K` is unramified. -/
theorem maximalUnramifiedSubextension_isUnramified
    (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    (DegreeData.AbstractExtension.mk (L.maximalUnramifiedSubextension D) K
      (L.intermediateField_le_base (L.inertiaImage D))).IsUnramified D := by
  change (DegreeData.AbstractExtension.mk
    (L.intermediateField (L.inertiaImage D)) K
    (L.intermediateField_le_base (L.inertiaImage D))).IsUnramified D
  rw [(DegreeData.AbstractExtension.mk
    (L.intermediateField (L.inertiaImage D)) K
    (L.intermediateField_le_base (L.inertiaImage D))).isUnramified_iff_inertia_le D]
  intro x hx
  let k : K.toSubgroup := ⟨x, hx.1⟩
  have hkI : k ∈ D.fieldInertiaWithin K := by
    exact hx.2
  have hkS :
      (QuotientGroup.mk'
        (extensionSubgroup K L.field L.below)) k ∈ L.inertiaImage D :=
    ⟨k, hkI, rfl⟩
  have hkP : k ∈ L.intermediateSubgroup (L.inertiaImage D) := by
    change (QuotientGroup.mk'
      (extensionSubgroup K L.field L.below)) k ∈ L.inertiaImage D
    exact hkS
  exact ⟨k, hkP, rfl⟩

/-- The complementary extension `L/M` is totally ramified, i.e.
`f_{L/M}=1`. -/
theorem maximalUnramifiedSubextension_isTotallyRamified
    (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    (DegreeData.AbstractExtension.mk L.field
      (L.maximalUnramifiedSubextension D)
      (L.field_le_intermediateField (L.inertiaImage D))).IsTotallyRamified D := by
  let S := L.inertiaImage D
  let M := L.maximalUnramifiedSubextension D
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  change (DegreeData.AbstractExtension.mk L.field
    (L.intermediateField (L.inertiaImage D)) hLM).IsTotallyRamified D
  rw [(DegreeData.AbstractExtension.mk L.field
    (L.intermediateField (L.inertiaImage D)) hLM).isTotallyRamified_iff_image_le D]
  rintro z ⟨x, hxM, rfl⟩
  let xK : K.toSubgroup := ⟨x, hMK hxM⟩
  have hxP : xK ∈ L.intermediateSubgroup S := by
    rw [← L.extensionSubgroup_intermediateField_eq S]
    exact (mem_extensionSubgroup_iff K M hMK xK).2 hxM
  change (QuotientGroup.mk'
    (extensionSubgroup K L.field L.below)) xK ∈
      (D.fieldInertiaWithin K).map
        (QuotientGroup.mk'
          (extensionSubgroup K L.field L.below)) at hxP
  obtain ⟨i, hiI, hi⟩ := hxP
  have hiH : i⁻¹ * xK ∈ extensionSubgroup K L.field L.below :=
    QuotientGroup.eq.mp hi
  have hiL : i.1⁻¹ * x ∈ L.field.toSubgroup := by
    exact (mem_extensionSubgroup_iff K L.field L.below (i⁻¹ * xK)).1 hiH
  refine ⟨i.1⁻¹ * x, hiL, ?_⟩
  have hdegree : D.degree i.1 = 1 :=
    (D.mem_fieldInertiaWithin_iff K i).1 hiI
  simp [hdegree]

/-- Maximality: every unramified intermediate extension of `L/K` is
contained in the field cut out by the inertia image.  In subgroup order this
is the displayed inclusion. -/
theorem maximalUnramifiedSubextension_le_of_isUnramified
    (D : DegreeData G) (L : FiniteGaloisSubextension K)
    (N : ClosedSubgroup G)
    (hLN : L.field.toSubgroup ≤ N.toSubgroup)
    (hNK : N.toSubgroup ≤ K.toSubgroup)
    (hNunramified : (DegreeData.AbstractExtension.mk N K hNK).IsUnramified D) :
    (L.maximalUnramifiedSubextension D).toSubgroup ≤ N.toSubgroup := by
  change (L.intermediateField (L.inertiaImage D)).toSubgroup ≤
    N.toSubgroup
  intro x hxM
  obtain ⟨k, hkP, rfl⟩ := hxM
  change (QuotientGroup.mk'
    (extensionSubgroup K L.field L.below)) k ∈
      (D.fieldInertiaWithin K).map
        (QuotientGroup.mk'
          (extensionSubgroup K L.field L.below)) at hkP
  obtain ⟨i, hiI, hi⟩ := hkP
  have hiH : i⁻¹ * k ∈ extensionSubgroup K L.field L.below :=
    QuotientGroup.eq.mp hi
  have hikL : i.1⁻¹ * k.1 ∈ L.field.toSubgroup :=
    (mem_extensionSubgroup_iff K L.field L.below (i⁻¹ * k)).1 hiH
  have hiDegree : D.degree i.1 = 1 :=
    (D.mem_fieldInertiaWithin_iff K i).1 hiI
  have hiKN : i.1 ∈ N.toSubgroup := by
    apply ((DegreeData.AbstractExtension.mk N K hNK).isUnramified_iff_inertia_le D).1
      hNunramified
    exact ⟨i.property, hiDegree⟩
  have hikN : i.1⁻¹ * k.1 ∈ N.toSubgroup := hLN hikL
  have hmul : i.1 * (i.1⁻¹ * k.1) ∈ N.toSubgroup :=
    N.toSubgroup.mul_mem hiKN hikN
  simpa [mul_assoc] using hmul

end FiniteGaloisSubextension

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- In the cyclic case, the lower norm arrow for
`L / (L ∩ K̃) / K` is injective by the order calculation from.
This specializes the actual cardinality proof in the reciprocity reduction exact row to the
inertia-image intermediate field. -/
theorem maximalUnramified_normMap_injective
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (D : DegreeData G) (L : FiniteGaloisSubextension K)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    [IsCyclic L.extensionQuotient] :
    let S := L.inertiaImage D
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    let hMK := L.intermediateField_le_base S
    letI : Finite
        (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
      L.extension_over_intermediate_finite S
    letI : Finite
        (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      L.intermediateField_finite S
    letI : Finite
        (K.toSubgroup ⧸ extensionSubgroup K L.field (hLM.trans hMK)) := by
      simpa only using L.finite
    Function.Injective
      (abstractReciprocityNormMap A K M L.field hLM hMK) := by
  dsimp only
  let S := L.inertiaImage D
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let : (extensionSubgroup K L.field (hLM.trans hMK)).Normal := by
    simpa only using L.normal
  let : (extensionSubgroup K M hMK).Normal :=
    L.intermediateField_normal S inferInstance
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L.field (hLM.trans hMK)) := by
    simpa only using L.finite
  let : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    L.intermediateField_finite S
  let : IsCyclic
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.lowerQuotient_isCyclic S
  let : IsCyclic
      (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    L.upperQuotient_isCyclic S
  obtain ⟨gKL, hgKL⟩ := IsCyclic.exists_generator
    (α := L.extensionQuotient)
  obtain ⟨gML, hgML⟩ := IsCyclic.exists_generator
    (α := M.toSubgroup ⧸ extensionSubgroup M L.field hLM)
  obtain ⟨gKM, hgKM⟩ := IsCyclic.exists_generator
    (α := K.toSubgroup ⧸ extensionSubgroup K M hMK)
  exact abstractReciprocity_cyclicTower_normMap_injective
    A hcf K M L.field hLM hMK gKL hgKL gML hgML gKM hgKM

end FiniteGaloisSubextension

/-- The diagram chase used twice in the first reduction.  The
middle vertical arrow is surjective when the two outside vertical arrows
are surjective, the top-right arrow is surjective, and the bottom row is
exact. -/
theorem abstractReciprocity_surjective_of_exact_diagram
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexact : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Surjective r₀)
    (hr₁ : Function.Surjective r₁) :
    Function.Surjective r := by
  intro b
  obtain ⟨q₁, hq₁⟩ := hr₁ (pB b)
  obtain ⟨q, hq⟩ := hpQ q₁
  have hzero : pB (b - r q) = 0 := by
    calc
      pB (b - r q) = pB b - pB (r q) := map_sub pB b (r q)
      _ = pB b - r₁ (pQ q) := by rw [hright q]
      _ = pB b - r₁ q₁ := by rw [hq]
      _ = pB b - pB b := by rw [hq₁]
      _ = 0 := sub_self _
  obtain ⟨b₀, hb₀⟩ := (hexact (b - r q)).mp hzero
  obtain ⟨q₀, hq₀⟩ := hr₀ b₀
  refine ⟨iQ q₀ + q, ?_⟩
  calc
    r (iQ q₀ + q) = r (iQ q₀) + r q := map_add r _ _
    _ = iB (r₀ q₀) + r q := by rw [hleft q₀]
    _ = iB b₀ + r q := by rw [hq₀]
    _ = (b - r q) + r q := by rw [hb₀]
    _ = b := sub_add_cancel b (r q)

/-- The diagram chase in the third reduction.  If both outside
reciprocity arrows are bijective and the first lower arrow is injective,
then the middle reciprocity arrow is bijective. -/
theorem abstractReciprocity_bijective_of_exact_diagram
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexactQ : Function.Exact iQ pQ)
    (hexactB : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hiB : Function.Injective iB)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Bijective r₀)
    (hr₁ : Function.Bijective r₁) :
    Function.Bijective r := by
  refine ⟨?_, abstractReciprocity_surjective_of_exact_diagram
    iQ pQ iB pB r₀ r r₁ hexactB hpQ hleft hright hr₀.2 hr₁.2⟩
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hpzero : pB (r q) = 0 := by rw [hq, map_zero]
  have hr₁zero : r₁ (pQ q) = 0 := by
    rw [← hright q]
    exact hpzero
  have hpQzero : pQ q = 0 := by
    apply hr₁.1
    simpa using hr₁zero
  obtain ⟨q₀, hq₀⟩ := (hexactQ q).mp hpQzero
  have hiBzero : iB (r₀ q₀) = 0 := by
    calc
      iB (r₀ q₀) = r (iQ q₀) := (hleft q₀).symm
      _ = r q := by rw [hq₀]
      _ = 0 := hq
  have hr₀zero : r₀ q₀ = 0 := by
    apply hiB
    simpa using hiBzero
  have hq₀zero : q₀ = 0 := by
    apply hr₀.1
    simpa using hr₀zero
  rw [← hq₀, hq₀zero, map_zero]

/-- Every additive homomorphism from a group into an abelian group kills
the commutator subgroup.  This is the automatic inclusion in the kernel
statement of the first reduction. -/
theorem abstractReciprocity_commutator_mem_kernel
    {Q : Type*} {B : Type*} [Group Q] [AddCommGroup B]
    (r : Additive Q →+ B) (q : Q)
    (hq : q ∈ commutator Q) :
    r (Additive.ofMul q) = 0 := by
  let rMul : Q →* Multiplicative B :=
    { toFun := fun x => Multiplicative.ofAdd (r (Additive.ofMul x))
      map_one' := r.map_zero
      map_mul' := r.map_add }
  have hker : q ∈ rMul.ker :=
    Abelianization.commutator_subset_ker rMul hq
  change Multiplicative.ofAdd (r (Additive.ofMul q)) = 1 at hker
  exact Multiplicative.ofAdd.injective (by simpa using hker)

/-- Exact remaining kernel calculation in the first reduction.  For the
actual maximal abelian intermediate field, commutativity of the right square
and injectivity of its reciprocity arrow identify the kernel of the middle
arrow with the commutator subgroup. -/
theorem abstractReciprocity_abelianReduction_kernel
    {K : ClosedSubgroup G} {B : Type*} {C : Type*}
    [AddCommGroup B] [AddCommGroup C]
    (L : FiniteGaloisSubextension K)
    (p : B →+ C)
    (r : Additive L.extensionQuotient →+ B)
    (rAb : Additive
        (K.toSubgroup ⧸ extensionSubgroup K L.abelianIntermediateField
          (L.intermediateField_le_base
            (commutator L.extensionQuotient))) →+ C)
    (hright : ∀ q,
      p (r (Additive.ofMul q)) =
        rAb (Additive.ofMul (L.abelianRestrictionHom q)))
    (hrAb : Function.Injective rAb)
    (q : L.extensionQuotient) :
    r (Additive.ofMul q) = 0 ↔
      q ∈ commutator L.extensionQuotient := by
  constructor
  · intro hq
    have hzero :
        rAb (Additive.ofMul (L.abelianRestrictionHom q)) = 0 := by
      rw [← hright q, hq, map_zero]
    have hresAdd :
        Additive.ofMul (L.abelianRestrictionHom q) = 0 := by
      apply hrAb
      simpa using hzero
    have hres : L.abelianRestrictionHom q = 1 := by
      exact Additive.ofMul.injective (by simpa using hresAdd)
    exact (L.abelianRestrictionHom_eq_one_iff q).1 hres
  · exact abstractReciprocity_commutator_mem_kernel r q

/-- The kernel argument in the second reduction.  Injectivity of
the reciprocity arrows for a jointly faithful family of cyclic quotients
forces injectivity of the original arrow.  All horizontal maps are the
actual restrictions to the intermediate fields cut out by the coordinate
kernels. -/
theorem abstractReciprocity_cyclicFactors_injective
    {K : ClosedSubgroup G} {I : Type*} {C : I → Type*}
    [∀ i, Group (C i)]
    (L : FiniteGaloisSubextension K)
    (f : ∀ i, L.extensionQuotient →* C i)
    (hfaithful : (⨅ i, MonoidHom.ker (f i)) = ⊥)
    {B : Type*} [AddCommGroup B]
    {D : I → Type*} [∀ i, AddCommGroup (D i)]
    (p : ∀ i, B →+ D i)
    (r : Additive L.extensionQuotient →+ B)
    (rFactor : ∀ i,
      Additive
        (K.toSubgroup ⧸ extensionSubgroup K
          (L.intermediateField (MonoidHom.ker (f i)))
          (L.intermediateField_le_base (MonoidHom.ker (f i)))) →+ D i)
    (hright : ∀ i q,
      p i (r (Additive.ofMul q)) =
        rFactor i (Additive.ofMul
          (L.upperRestrictionHom (MonoidHom.ker (f i)) q)))
    (hinjective : ∀ i, Function.Injective (rFactor i)) :
    Function.Injective r := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hres (i : I) :
      L.upperRestrictionHom (MonoidHom.ker (f i)) q.toMul = 1 := by
    have hrq : r (Additive.ofMul q.toMul) = 0 := by
      simpa using hq
    have hzero : rFactor i (Additive.ofMul
        (L.upperRestrictionHom (MonoidHom.ker (f i)) q.toMul)) = 0 := by
      rw [← hright i q.toMul, hrq, map_zero]
    have hadd : Additive.ofMul
        (L.upperRestrictionHom (MonoidHom.ker (f i)) q.toMul) = 0 := by
      apply hinjective i
      simpa using hzero
    exact Additive.ofMul.injective (by simpa using hadd)
  have hqone : q.toMul = 1 :=
    (L.upperRestrictionHom_jointlyFaithful f hfaithful q.toMul).1 hres
  exact Additive.toMul.injective (by simpa using hqone)

end Representation

end
end ClassFormation
