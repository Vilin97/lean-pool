/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension
public import Mathlib.Topology.Algebra.Group.Basic

/-! # Intermediate Extension -/

@[expose] public section
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# Intermediate extensions from actual quotient subgroups

For the three reductions in the proof of the abstract reciprocity theorem, this file supplies
  the finite Galois correspondence in the
direction used by the construction.  If `L / K` is a packaged finite Galois extension
and `S ≤ G(L/K)`, its inverse image in `G_K` is realized as an actual closed
intermediate field `M`.

Closedness is proved from the explicit decomposition of the inverse image
as the finite union of right `G_L`-cosets.  The two Galois-group
identifications are then obtained from the actual restriction map and the
first and third isomorphism theorems; no correspondence certificate is
assumed.
-/

noncomputable
section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The inverse image in `G_K` of a subgroup of `G(L/K)`. -/
def intermediateSubgroup (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Subgroup K.toSubgroup := by
  exact S.comap L.extensionQuotientMk

omit [IsTopologicalGroup G] in
/-- Membership in the intermediate subgroup is characterized by membership of
the underlying ambient element. -/
@[simp]
theorem mem_intermediateSubgroup_iff
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (k : K.toSubgroup) :
    k ∈ L.intermediateSubgroup S ↔ L.extensionQuotientMk k ∈ S :=
  Iff.rfl

omit [IsTopologicalGroup G] in
/-- The original `G_L` lies in every inverse-image subgroup. -/
theorem extensionSubgroup_le_intermediateSubgroup
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    extensionSubgroup K L.field L.below ≤ L.intermediateSubgroup S := by
  intro x hx
  apply (L.mem_intermediateSubgroup_iff S x).2
  have hmk : L.extensionQuotientMk x = 1 :=
    (L.extensionQuotientMk_eq_one_iff x).2 hx
  rw [hmk]
  exact S.one_mem

/-- The `G_L`-coset classified by `q ∈ G(L/K)`, defined canonically as a
fiber of the quotient map.  In particular, its public definition does not
choose a representative of `q`. -/
def intermediateCoset (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : Set K.toSubgroup :=
  {x | L.extensionQuotientMk x = q}

/-- A representative-based description used only to prove topological facts
about the canonical quotient fiber. -/
private def representativeIntermediateCoset (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : Set K.toSubgroup :=
  (fun x : K.toSubgroup =>
      x * Quotient.out (L.extensionQuotientMulEquiv q)) ''
    (extensionSubgroup K L.field L.below : Set K.toSubgroup)

omit [IsTopologicalGroup G] in
/-- Membership in the canonical coset is equality with its quotient class. -/
theorem mem_intermediateCoset_iff (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) (x : K.toSubgroup) :
    x ∈ L.intermediateCoset q ↔
      L.extensionQuotientMk x = q :=
  Iff.rfl

omit [IsTopologicalGroup G] in
private theorem mem_representativeIntermediateCoset_iff
    (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) (x : K.toSubgroup) :
    x ∈ representativeIntermediateCoset L q ↔
      L.extensionQuotientMk x = q := by
  let : (extensionSubgroup K L.field L.below).Normal := L.normal
  constructor
  · rintro ⟨h, hh, rfl⟩
    apply L.extensionQuotientMulEquiv.injective
    rw [L.extensionQuotientMk_apply]
    rw [← Quotient.out_eq' (L.extensionQuotientMulEquiv q)]
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa [div_eq_mul_inv, mul_assoc] using hh
  · intro hx
    have hxout :
        (QuotientGroup.mk' (extensionSubgroup K L.field L.below)) x =
          (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below))
              (Quotient.out (L.extensionQuotientMulEquiv q)) := by
      calc
        (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below)) x =
              L.extensionQuotientMulEquiv (L.extensionQuotientMk x) :=
          (L.extensionQuotientMk_apply x).symm
        _ = L.extensionQuotientMulEquiv q :=
          congrArg L.extensionQuotientMulEquiv hx
        _ = (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below))
              (Quotient.out (L.extensionQuotientMulEquiv q)) :=
          (Quotient.out_eq' (L.extensionQuotientMulEquiv q)).symm
    have hdiv : x / Quotient.out (L.extensionQuotientMulEquiv q) ∈
        extensionSubgroup K L.field L.below :=
      QuotientGroup.eq_iff_div_mem.mp hxout
    refine ⟨x / Quotient.out (L.extensionQuotientMulEquiv q), hdiv, ?_⟩
    simp [div_eq_mul_inv, mul_assoc]

omit [IsTopologicalGroup G] in
private theorem intermediateCoset_eq_representativeIntermediateCoset
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    L.intermediateCoset q = representativeIntermediateCoset L q := by
  ext x
  exact (mem_representativeIntermediateCoset_iff L q x).symm

omit [IsTopologicalGroup G] in
/-- The inverse image of `S` is literally the finite union of the `G_L`
cosets indexed by the elements of `S`. -/
theorem intermediateSubgroup_eq_iUnion_cosets
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.intermediateSubgroup S : Set K.toSubgroup) =
      ⋃ q ∈ (S : Set L.extensionQuotient), L.intermediateCoset q := by
  ext x
  constructor
  · intro hx
    have hxS := (L.mem_intermediateSubgroup_iff S x).1 hx
    refine Set.mem_iUnion₂.mpr ⟨
      L.extensionQuotientMk x, hxS, ?_⟩
    exact (mem_intermediateCoset_iff L _ x).2 rfl
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨q, hqS, hxq⟩
    apply (L.mem_intermediateSubgroup_iff S x).2
    rw [(mem_intermediateCoset_iff L q x).1 hxq]
    exact hqS

private theorem representativeIntermediateCoset_isClosed
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    IsClosed (representativeIntermediateCoset L q) := by
  exact isClosedMap_mul_right
    (Quotient.out (L.extensionQuotientMulEquiv q)) _
    (extensionSubgroup_isClosed K L.field L.below)

/-- Every coset in the preceding union is closed: it is the image of the
closed subgroup `G_L ≤ G_K` under right translation. -/
theorem intermediateCoset_isClosed (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : IsClosed (L.intermediateCoset q) := by
  rw [intermediateCoset_eq_representativeIntermediateCoset]
  exact representativeIntermediateCoset_isClosed L q

/-- Closedness of the inverse image, proved by its finite coset
decomposition rather than postulated as a Galois-correspondence property. -/
theorem intermediateSubgroup_isClosed (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    IsClosed (L.intermediateSubgroup S : Set K.toSubgroup) := by
  let : Finite L.extensionQuotient := L.finite
  rw [intermediateSubgroup_eq_iUnion_cosets]
  have hfinite : (S : Set L.extensionQuotient).Finite := Set.toFinite _
  exact hfinite.isClosed_biUnion fun q _ => intermediateCoset_isClosed L q

/-- The closed intermediate field cut out by `S ≤ G(L/K)`. -/
def intermediateField (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : ClosedSubgroup G where
  toSubgroup := (L.intermediateSubgroup S).map K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      ((fun x : K.toSubgroup => (x : G)) ''
        (L.intermediateSubgroup S : Set K.toSubgroup))
    exact K.isClosed'.isClosedMap_subtype_val _
      (intermediateSubgroup_isClosed L S)

/-- The constructed intermediate field lies over `K`. -/
theorem intermediateField_le_base (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup ≤ K.toSubgroup := by
  rintro _ ⟨m, hm, rfl⟩
  exact m.property

/-- Pulling the constructed field back to `G_K` recovers exactly the
inverse-image subgroup. -/
theorem extensionSubgroup_intermediateField_eq
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    extensionSubgroup K (L.intermediateField S)
        (L.intermediateField_le_base S) =
      L.intermediateSubgroup S := by
  ext x
  simp only [extensionSubgroup, intermediateField, mem_intermediateSubgroup_iff]
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The constructed field is intermediate: `L ≤ M`. -/
theorem field_le_intermediateField (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    L.field.toSubgroup ≤ (L.intermediateField S).toSubgroup := by
  intro x hx
  let xK : K.toSubgroup := ⟨x, L.below hx⟩
  have hxH : xK ∈ extensionSubgroup K L.field L.below :=
    (mem_extensionSubgroup_iff K L.field L.below xK).2 hx
  have hxP : xK ∈ L.intermediateSubgroup S :=
    L.extensionSubgroup_le_intermediateSubgroup S hxH
  exact ⟨xK, hxP, rfl⟩

/-- The extension subgroup for `L/M` is the pullback of `G_L ◁ G_K`
along `G_M → G_K`. -/
theorem extensionSubgroup_over_intermediate_eq_comap
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S) =
      (extensionSubgroup K L.field L.below).comap
        (Subgroup.inclusion (L.intermediateField_le_base S)) := by
  ext x
  rw [mem_extensionSubgroup_iff, Subgroup.mem_comap,
    mem_extensionSubgroup_iff]
  rfl

/-- `L/M` is normal because it is obtained by restricting the normal
subgroup `G_L ◁ G_K` to `G_M`. -/
theorem extensionSubgroup_over_intermediate_normal
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal := by
  rw [extensionSubgroup_over_intermediate_eq_comap]
  infer_instance

/-- The extension subgroup over an intermediate field is normal in the intermediate subgroup. -/
instance extensionSubgroup_over_intermediate_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
  L.extensionSubgroup_over_intermediate_normal S

/-- The lower extension `L/M` is finite. -/
theorem extension_over_intermediate_finite
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  exact FiniteGaloisSubextension.finite_extension_over_intermediate
    L.below (L.intermediateField_le_base S)
      (L.field_le_intermediateField S)

/-- The intermediate extension `M/K` is finite, since its subgroup contains
the finite-index subgroup `G_L`. -/
theorem intermediateField_finite
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S)) := by
  rw [extensionSubgroup_intermediateField_eq]
  let : (extensionSubgroup K L.field L.below).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
      (extensionSubgroup K L.field L.below) L.finite
  let : (L.intermediateSubgroup S).FiniteIndex :=
    Subgroup.finiteIndex_of_le (L.extensionSubgroup_le_intermediateSubgroup S)
  exact Subgroup.finite_quotient_of_finiteIndex

/-- The generally non-Galois finite extension `L^S/K` attached to an
arbitrary subgroup `S ≤ G(L/K)`.  Normality is deliberately absent from this
bundle; clients that only need finite-extension invariants should use this
rather than forcing `S` through `intermediateFiniteGalois`. -/
def intermediateFiniteAbstractExtension
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    DegreeData.FiniteAbstractExtension G where
  field := L.intermediateField S
  base := K
  below := L.intermediateField_le_base S
  finiteQuotient := L.intermediateField_finite S

omit [IsTopologicalGroup G] in
/-- A normal subgroup `S ◁ G(L/K)` has normal inverse image in `G_K`. -/
theorem intermediateSubgroup_normal
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (hS : S.Normal) : (L.intermediateSubgroup S).Normal := by
  let : S.Normal := hS
  exact hS.comap L.extensionQuotientMk

/-- Hence `M/K` is normal whenever `S` is normal. -/
theorem intermediateField_normal
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (hS : S.Normal) :
    (extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S)).Normal := by
  rw [extensionSubgroup_intermediateField_eq]
  exact L.intermediateSubgroup_normal S hS

/-- The actual finite Galois extension `L/M`. -/
def lowerFiniteGalois (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    FiniteGaloisSubextension (L.intermediateField S) where
  field := L.field
  below := L.field_le_intermediateField S
  normal := L.extensionSubgroup_over_intermediate_normal S
  finite := L.extension_over_intermediate_finite S

/-- If `S` is normal, the actual finite Galois extension `M/K`. -/
def intermediateFiniteGalois (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) (hS : S.Normal) :
    FiniteGaloisSubextension K where
  field := L.intermediateField S
  below := L.intermediateField_le_base S
  normal := L.intermediateField_normal S hS
  finite := L.intermediateField_finite S

/-- Restriction from `G_M` to the subgroup `S ≤ G(L/K)`.  The codomain
membership proof is supplied by the defining inverse-image equation for
`M`. -/
def lowerRestrictionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup →* S :=
  (L.extensionQuotientMk.comp
      (Subgroup.inclusion (L.intermediateField_le_base S))).codRestrict S
    (by
      intro m
      apply (L.mem_intermediateSubgroup_iff S _).1
      rw [← extensionSubgroup_intermediateField_eq L S]
      exact
        (mem_extensionSubgroup_iff K (L.intermediateField S)
          (L.intermediateField_le_base S)
          (Subgroup.inclusion (L.intermediateField_le_base S) m)).2
          m.property)

/-- The lower restriction homomorphism evaluates by restricting the underlying
ambient automorphism. -/
@[simp]
theorem lowerRestrictionHom_apply_coe (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    ((L.lowerRestrictionHom S m : S) : L.extensionQuotient) =
      L.extensionQuotientMk
        (Subgroup.inclusion (L.intermediateField_le_base S) m) :=
  rfl

/-- Every element of `S` is represented by an element of `G_M`; hence the
restriction map is onto. -/
theorem lowerRestrictionHom_surjective (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    Function.Surjective (L.lowerRestrictionHom S) := by
  intro s
  rcases L.extensionQuotientMk_surjective s.1 with ⟨k, hk⟩
  have hkP : k ∈ L.intermediateSubgroup S := by
    apply (L.mem_intermediateSubgroup_iff S k).2
    rw [hk]
    exact s.property
  let m : (L.intermediateField S).toSubgroup :=
    ⟨k.1, ⟨k, hkP, rfl⟩⟩
  refine ⟨m, ?_⟩
  apply Subtype.ext
  rw [lowerRestrictionHom_apply_coe]
  change L.extensionQuotientMk k = s
  exact hk

/-- The kernel of restriction is exactly `G_L` viewed inside `G_M`. -/
theorem lowerRestrictionHom_ker (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    MonoidHom.ker (L.lowerRestrictionHom S) =
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S) := by
  ext m
  rw [MonoidHom.mem_ker, mem_extensionSubgroup_iff]
  constructor
  · intro hm
    let mK : K.toSubgroup :=
      ⟨m.1, L.intermediateField_le_base S m.property⟩
    have hq :
        ((L.lowerRestrictionHom S m : S) : L.extensionQuotient) = 1 :=
      congrArg Subtype.val hm
    rw [lowerRestrictionHom_apply_coe] at hq
    have hH : mK ∈ extensionSubgroup K L.field L.below :=
      (L.extensionQuotientMk_eq_one_iff mK).1 hq
    exact (mem_extensionSubgroup_iff K L.field L.below
      mK).1 hH
  · intro hm
    let mK : K.toSubgroup :=
      ⟨m.1, L.intermediateField_le_base S m.property⟩
    have hH : mK ∈ extensionSubgroup K L.field L.below :=
      (mem_extensionSubgroup_iff K L.field L.below mK).2 hm
    have hq : L.extensionQuotientMk mK = 1 :=
      (L.extensionQuotientMk_eq_one_iff mK).2 hH
    apply Subtype.ext
    rw [lowerRestrictionHom_apply_coe]
    exact hq

/-- The first actual Galois-group identification used:
`G(L/M) ≃ S`. -/
noncomputable def lowerQuotientEquiv (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.lowerFiniteGalois S).extensionQuotient ≃* S := by
  letI : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  exact (L.lowerFiniteGalois S).extensionQuotientMulEquiv.trans
    ((QuotientGroup.quotientMulEquivOfEq
        (L.lowerRestrictionHom_ker S).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (L.lowerRestrictionHom S) (L.lowerRestrictionHom_surjective S)))

/-- Representative formula for `G(L/M) ≃ S`. -/
@[simp]
theorem lowerQuotientEquiv_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    L.lowerQuotientEquiv S
        ((L.lowerFiniteGalois S).extensionQuotientMk m) =
      L.lowerRestrictionHom S m := by
  let : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  change
    ((QuotientGroup.quotientMulEquivOfEq
        (L.lowerRestrictionHom_ker S).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (L.lowerRestrictionHom S) (L.lowerRestrictionHom_surjective S)))
      (QuotientGroup.mk m) = L.lowerRestrictionHom S m
  rfl

/-- The same representative formula after forgetting the subtype `S`; this
is the form used when composing restriction maps in the reduction diagram. -/
theorem lowerQuotientEquiv_mk_coe (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    ((L.lowerQuotientEquiv S
        ((L.lowerFiniteGalois S).extensionQuotientMk m) : S) :
          L.extensionQuotient) =
      L.extensionQuotientMk
        ⟨m.1, L.intermediateField_le_base S m.property⟩ := by
  rw [lowerQuotientEquiv_mk, lowerRestrictionHom_apply_coe]
  apply congrArg L.extensionQuotientMk
  exact Subtype.ext (by rfl)

omit [IsTopologicalGroup G] in
/-- Mapping the inverse image of `S` back to `G(L/K)` recovers `S`
itself. -/
theorem intermediateSubgroup_map_quotient_eq
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.intermediateSubgroup S).map L.extensionQuotientMk = S := by
  exact Subgroup.map_comap_eq_self_of_surjective
    L.extensionQuotientMk_surjective S

/-- The subgroup attached to the intermediate extension is normal. -/
instance intermediateSubgroup_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    [hS : S.Normal] : (L.intermediateSubgroup S).Normal :=
  L.intermediateSubgroup_normal S hS

/-- The field represented by a normal intermediate subgroup is a normal subextension. -/
instance intermediateField_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    [hS : S.Normal] :
    (extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S)).Normal :=
  L.intermediateField_normal S hS

/-- The third-isomorphism identification used in the normal-subextension
diagram: `G(L/K)/S ≃ G(M/K)`. -/
def upperQuotient (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Type _ :=
  L.extensionQuotient ⧸ S

/-- The upper quotient over an intermediate field carries its canonical group structure. -/
instance upperQuotientGroupInstance (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    Group (L.upperQuotient S) := by
  change Group (L.extensionQuotient ⧸ S)
  infer_instance

/-- Comparison with the group-library presentation of the upper quotient. -/
def upperQuotientMulEquiv (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.upperQuotient S ≃* (L.extensionQuotient ⧸ S) :=
  MulEquiv.refl _

/-- The canonical projection to the named upper quotient. -/
def upperQuotientMk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.extensionQuotient →* L.upperQuotient S :=
  QuotientGroup.mk' S

omit [IsTopologicalGroup G] in
/-- The named upper quotient projection agrees with the underlying quotient-group projection. -/
@[simp]
theorem upperQuotientMk_apply (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    (q : L.extensionQuotient) :
    L.upperQuotientMulEquiv S (L.upperQuotientMk S q) =
      (QuotientGroup.mk q : L.extensionQuotient ⧸ S) :=
  rfl

/-- The third-isomorphism identification, with both source and target kept
behind their named finite-Galois quotient boundaries. -/
noncomputable def upperQuotientEquiv (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.upperQuotient S ≃*
      (L.intermediateFiniteGalois S inferInstance).extensionQuotient := by
  let H := extensionSubgroup K L.field L.below
  let P := L.intermediateSubgroup S
  let π : K.toSubgroup →* L.extensionQuotient := L.extensionQuotientMk
  have hHP : H ≤ P := L.extensionSubgroup_le_intermediateSubgroup S
  have hmap : P.map π = S := L.intermediateSubgroup_map_quotient_eq S
  have hupper : extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S) = P :=
    L.extensionSubgroup_intermediateField_eq S
  letI : H.Normal := L.normal
  letI : P.Normal := L.intermediateSubgroup_normal S inferInstance
  letI : (P.map π).Normal := by rw [hmap]; infer_instance
  exact (L.upperQuotientMulEquiv S).trans
    ((QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      ((QuotientGroup.quotientQuotientEquivQuotient H P hHP).trans
        ((QuotientGroup.quotientMulEquivOfEq hupper.symm).trans
          (L.intermediateFiniteGalois S inferInstance).extensionQuotientMulEquiv.symm)))

/-- Representative formula for `G(L/K)/S ≃ G(M/K)`. -/
@[simp]
theorem upperQuotientEquiv_mk_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] (k : K.toSubgroup) :
    L.upperQuotientEquiv S
        (L.upperQuotientMk S (L.extensionQuotientMk k)) =
      (L.intermediateFiniteGalois S inferInstance).extensionQuotientMk k := by
  let H := extensionSubgroup K L.field L.below
  let P := L.intermediateSubgroup S
  let π : K.toSubgroup →* L.extensionQuotient := L.extensionQuotientMk
  have hHP : H ≤ P := L.extensionSubgroup_le_intermediateSubgroup S
  have hmap : P.map π = S := L.intermediateSubgroup_map_quotient_eq S
  have hupper : extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S) = P :=
    L.extensionSubgroup_intermediateField_eq S
  let : H.Normal := L.normal
  let : P.Normal := L.intermediateSubgroup_normal S inferInstance
  let : (P.map π).Normal := by rw [hmap]; infer_instance
  change
    (L.intermediateFiniteGalois S
        inferInstance).extensionQuotientMulEquiv.symm
      ((QuotientGroup.quotientMulEquivOfEq hupper.symm)
        ((QuotientGroup.quotientQuotientEquivQuotient H P hHP)
          ((QuotientGroup.quotientMulEquivOfEq hmap.symm)
            (QuotientGroup.mk (L.extensionQuotientMk k))))) =
      (L.intermediateFiniteGalois S inferInstance).extensionQuotientMk k
  apply
    (L.intermediateFiniteGalois S inferInstance).extensionQuotientMulEquiv.injective
  refine ((L.intermediateFiniteGalois S
    inferInstance).extensionQuotientMulEquiv.apply_symm_apply _).trans ?_
  refine Eq.trans ?_
    ((L.intermediateFiniteGalois S inferInstance).extensionQuotientMk_apply k).symm
  have hmk :
      L.extensionQuotientMk k =
        (QuotientGroup.mk k : K.toSubgroup ⧸ H) := by
    change L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k : K.toSubgroup ⧸ H)
    exact L.extensionQuotientMk_apply k
  have hthird :
      (QuotientGroup.quotientQuotientEquivQuotient H P hHP)
          ((QuotientGroup.mk
            (QuotientGroup.mk k : K.toSubgroup ⧸ H)) :
              (K.toSubgroup ⧸ H) ⧸
                P.map (QuotientGroup.mk' H)) =
        (QuotientGroup.mk k : K.toSubgroup ⧸ P) := by
    exact
      QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk H P hHP k
  calc
    _ =
        (QuotientGroup.quotientMulEquivOfEq hupper.symm)
          ((QuotientGroup.quotientQuotientEquivQuotient H P hHP)
            (QuotientGroup.mk (L.extensionQuotientMk k))) :=
      congrArg
        (fun q => (QuotientGroup.quotientMulEquivOfEq hupper.symm)
          ((QuotientGroup.quotientQuotientEquivQuotient H P hHP) q))
        (QuotientGroup.quotientMulEquivOfEq_mk hmap.symm (L.extensionQuotientMk k))
    _ =
        (QuotientGroup.quotientMulEquivOfEq hupper.symm)
          ((QuotientGroup.quotientQuotientEquivQuotient H P hHP)
            (QuotientGroup.mk (QuotientGroup.mk k : K.toSubgroup ⧸ H))) :=
      congrArg
        (fun q : K.toSubgroup ⧸ H =>
          (QuotientGroup.quotientMulEquivOfEq hupper.symm)
            ((QuotientGroup.quotientQuotientEquivQuotient H P hHP)
              (QuotientGroup.mk q))) hmk
    _ =
        (QuotientGroup.quotientMulEquivOfEq hupper.symm)
          (QuotientGroup.mk k : K.toSubgroup ⧸ P) :=
      congrArg (QuotientGroup.quotientMulEquivOfEq hupper.symm) hthird
    _ = _ := QuotientGroup.quotientMulEquivOfEq_mk hupper.symm k

end FiniteGaloisSubextension

end
end ClassFormation
