/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6

/-!
# Hopf problem: toric · diagonal quotient 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def
    DiagonalQuotient.fibreHomeomorphOfLocalTrivializations {E B F J : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace F] (f : E → B) (U : J → TopologicalSpace.Opens B)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F)) (hbase : ∀ i x, ((h i x).1 : B) = f x.val)
    (i : J) (b : B) (hb : b ∈ U i) : (f ⁻¹' { b }) ≃ₜ F := by
  let lift : (f ⁻¹' { b }) → (f ⁻¹' (U i : Set B)) := fun x =>
    ⟨x.val, by
      change f x.val ∈ U i
      rw [show f x.val = b from x.property]
      exact hb⟩
  let inv : F → (f ⁻¹' { b }) := fun t =>
    ⟨((h i).symm (⟨b, hb⟩, t)).val,
      by
      change f ((h i).symm (⟨b, hb⟩, t)).val = b
      rw [← hbase i]
      simp⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have hpair (x : (f ⁻¹' { b })) : ((⟨b, hb⟩ : U i), (h i (lift x)).2) = h i (lift x) := by
    apply Prod.ext
    · apply Subtype.ext
      exact ((hbase i (lift x)).trans x.property).symm
    · rfl
  refine
    { toFun := fun x => (h i (lift x)).2
      invFun := inv
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := continuous_snd.comp ((h i).continuous.comp hlift)
      continuous_invFun := ?_ }
  · intro x
    apply Subtype.ext
    change ((h i).symm ((⟨b, hb⟩ : U i), (h i (lift x)).2)).val = x.val
    rw [hpair x, (h i).symm_apply_apply]
  · intro t
    change (h i (lift (inv t))).2 = t
    have hinv : lift (inv t) = (h i).symm (⟨b, hb⟩, t) := by
      apply Subtype.ext
      rfl
    rw [hinv, (h i).apply_symm_apply]
  · exact
      (continuous_subtype_val.comp
            ((h i).symm.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk
        _

private theorem DiagonalQuotient.restrictPreimage_eq_fst_comp {E B F J : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace F] (f : E → B) (U : J → TopologicalSpace.Opens B)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F)) (hbase : ∀ i x, ((h i x).1 : B) = f x.val)
    (i : J) : (U i : Set B).restrictPreimage f = Prod.fst ∘ h i := by
  funext x
  apply Subtype.ext
  exact (hbase i x).symm

private theorem DiagonalQuotient.restrictPreimage_proper_of_localTrivializations {E B F J : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F] [CompactSpace F] (f : E → B)
    (U : J → TopologicalSpace.Opens B) (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F))
    (hbase : ∀ i x, ((h i x).1 : B) = f x.val) (i : J) :
    IsProperMap ((U i : Set B).restrictPreimage f) := by
  rw [restrictPreimage_eq_fst_comp f U h hbase i]
  exact isProperMap_fst_of_compactSpace.comp (h i).isProperMap

private theorem
    DiagonalQuotient.proper_of_localTrivializations {E B F J : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace F] [CompactSpace F] (f : E → B) (hf : Continuous f)
    (U : J → TopologicalSpace.Opens B) (hU : TopologicalSpace.IsOpenCover U)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F)) (hbase : ∀ i x, ((h i x).1 : B) = f x.val) :
    IsProperMap f := by
  have hp := restrictPreimage_proper_of_localTrivializations f U h hbase
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hf, hU.isClosedMap_iff_restrictPreimage.mpr (fun i => (hp i).isClosedMap), ?_⟩
  intro b
  obtain ⟨i, hi⟩ := hU.exists_mem b
  have hc :=
    ((hp i).isCompact_preimage (isCompact_singleton (x := (⟨b, hi⟩ : U i)))).image
      continuous_subtype_val
  simpa only [Set.image_val_preimage_restrictPreimage, Set.image_singleton] using hc

private theorem
    DiagonalQuotient.t2Space_of_localTrivializations {E B F J : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace F] [T2Space B] [T2Space F] (f : E → B)
    (hf : Continuous f) (U : J → TopologicalSpace.Opens B) (hU : TopologicalSpace.IsOpenCover U)
    (h : ∀ i, (f ⁻¹' (U i : Set B)) ≃ₜ ((U i) × F)) :
    T2Space E := by
  constructor
  intro x y hxy
  by_cases hb : f x = f y
  · obtain ⟨i, hi⟩ := hU.exists_mem (f x)
    have hx : x ∈ f ⁻¹' (U i : Set B) := hi
    have hy : y ∈ f ⁻¹' (U i : Set B) := by
      change f y ∈ U i
      rw [← hb]
      exact hi
    let a : f ⁻¹' (U i : Set B) := ⟨x, hx⟩
    let b : f ⁻¹' (U i : Set B) := ⟨y, hy⟩
    have hab : a ≠ b := fun he => hxy (congrArg Subtype.val he)
    let : T2Space (f ⁻¹' (U i : Set B)) := (h i).symm.t2Space
    obtain ⟨V, W, hV, hW, ha, hb', hVW⟩ := t2_separation hab
    have hopen : IsOpen (f ⁻¹' (U i : Set B)) := (U i).isOpen.preimage hf
    refine
      ⟨Subtype.val '' V, Subtype.val '' W, hopen.isOpenMap_subtype_val _ hV,
        hopen.isOpenMap_subtype_val _ hW, ⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, ?_⟩
    apply Set.disjoint_left.mpr
    rintro z ⟨a', ha', hza⟩ ⟨b', hb'', hzb⟩
    have hab' : a' = b' := Subtype.ext (hza.trans hzb.symm)
    exact (Set.disjoint_left.mp hVW) ha' (hab'.symm ▸ hb'')
  · obtain ⟨V, W, hV, hW, hx, hy, hVW⟩ := t2_separation hb
    exact ⟨f ⁻¹' V, f ⁻¹' W, hV.preimage hf, hW.preimage hf, hx, hy, hVW.preimage f⟩

/-- The orbit-space quotient of a group action on the base. -/
public
abbrev DiagonalQuotient.BaseSpace (G B : Type*) [Group G] [MulAction G B] :=
  MulAction.orbitRel.Quotient G B

private abbrev DiagonalQuotient.Space (G B F : Type*) [Group G] [MulAction G B] [MulAction G F] :=
  MulAction.orbitRel.Quotient G (B × F)

/-- The quotient map from a base to its orbit space. -/
public
def DiagonalQuotient.baseQuotient (G B : Type*) [Group G] [MulAction G B] : B → BaseSpace G B :=
  Quotient.mk (MulAction.orbitRel G B)

private def DiagonalQuotient.quotient (G B F : Type*) [Group G] [MulAction G B] [MulAction G F] :
    B × F → Space G B F :=
  Quotient.mk (MulAction.orbitRel G (B × F))

private theorem DiagonalQuotient.quotient_surjective (G B F : Type*) [Group G] [MulAction G B]
    [MulAction G F] : Function.Surjective (quotient G B F) :=
  Quotient.mk_surjective

private theorem
    DiagonalQuotient.quotient_eq_iff (G B F : Type*) [Group G] [MulAction G B] [MulAction G F]
    (x y : B × F) : quotient G B F x = quotient G B F y ↔ ∃ g : G, g • y = x :=
  Quotient.eq''

@[simp]
private theorem
    DiagonalQuotient.quotient_smul (G B F : Type*) [Group G] [MulAction G B] [MulAction G F]
    (g : G) (x : B × F) : quotient G B F (g • x) = quotient G B F x :=
  (quotient_eq_iff G B F _ _).mpr ⟨g, rfl⟩

private def DiagonalQuotient.projection (G B F : Type*) [Group G] [MulAction G B] [MulAction G F] :
    Space G B F → BaseSpace G B :=
  Quotient.lift (fun x : B × F => baseQuotient G B x.1)
    (by
      rintro x y ⟨g, hg⟩
      exact Quotient.sound ⟨g, congrArg Prod.fst hg⟩)

private def
    DiagonalQuotient.fibreInclusion (G B F : Type*) [Group G] [MulAction G B] [MulAction G F]
    (b : B) (f : F) : Space G B F :=
  quotient G B F (b, f)

private theorem DiagonalQuotient.baseQuotient_continuous (G B : Type*) [Group G] [MulAction G B]
    [TopologicalSpace B] : Continuous (baseQuotient G B) :=
  continuous_quot_mk

private theorem DiagonalQuotient.quotient_continuous (G B F : Type*) [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] : Continuous (quotient G B F) :=
  continuous_quot_mk

private theorem DiagonalQuotient.quotient_isQuotientMap (G B F : Type*) [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] :
    Topology.IsQuotientMap (quotient G B F) :=
  isQuotientMap_quotient_mk'

private theorem DiagonalQuotient.projection_continuous (G B F : Type*) [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] : Continuous (projection G B F) :=
  (quotient_isQuotientMap G B F).continuous_iff.mpr
    ((baseQuotient_continuous G B).comp continuous_fst)

private theorem DiagonalQuotient.fibreInclusion_continuous (G B F : Type*) [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] (b : B) :
    Continuous (fibreInclusion G B F b) :=
  (quotient_continuous G B F).comp (continuous_const.prodMk continuous_id)

private def DiagonalQuotient.baseLocalInverse {G : Type*} {B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    OpenPartialHomeomorph (BaseSpace G B) B :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt b

private theorem DiagonalQuotient.baseQuotient_localInverse {G : Type*} {B : Type*} [Group G]
    [MulAction G B] [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B)
    {x : BaseSpace G B} (hx : x ∈ (baseLocalInverse hq b).source) :
    baseQuotient G B (baseLocalInverse hq b x) = x :=
  hq.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hx

private def
    DiagonalQuotient.patch {G : Type*} {B : Type*} [Group G] [MulAction G B] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    TopologicalSpace.Opens (BaseSpace G B) :=
  ⟨(baseLocalInverse hq b).source, (baseLocalInverse hq b).open_source⟩

private theorem
    DiagonalQuotient.baseQuotient_mem_patch {G : Type*} {B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    baseQuotient G B b ∈ patch hq b :=
  hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source

private theorem DiagonalQuotient.patch_cover {G : Type*} {B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) :
    TopologicalSpace.IsOpenCover (patch hq) := by
  apply TopologicalSpace.IsOpenCover.of_sets (fun b => (baseLocalInverse hq b).open_source)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨b, rfl⟩ := hq.surjective x
  exact Set.mem_iUnion.mpr ⟨b, baseQuotient_mem_patch hq b⟩

private theorem
    DiagonalQuotient.fibreInclusion_injective {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    Function.Injective (fibreInclusion G B F b) := by
  let := hq.isCancelSMul
  intro x y hxy
  obtain ⟨g, hg⟩ := (quotient_eq_iff G B F _ _).mp hxy
  have hb : g • b = b := congrArg Prod.fst hg
  have hg1 : g = 1 := IsCancelSMul.right_cancel _ _ b (hb.trans (one_smul G b).symm)
  simpa only [hg1, one_smul] using (congrArg Prod.snd hg).symm

private theorem DiagonalQuotient.quotientCoveringMap {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] :
    IsQuotientCoveringMap (quotient G B F) G
    where
  toIsQuotientMap := quotient_isQuotientMap G B F
  continuous_const_smul
    g := (hq.continuous_const_smul g).prodMap (ContinuousConstSMul.continuous_const_smul g)
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint
    x := by
    obtain ⟨U, hU, hd⟩ := hq.disjoint x.1
    refine ⟨Prod.fst ⁻¹' U, continuous_fst.continuousAt hU, ?_⟩
    rintro g ⟨z, ⟨w, hw, rfl⟩, hz⟩
    exact hd g ⟨g • w.1, ⟨w.1, hw, rfl⟩, hz⟩

private theorem
    DiagonalQuotient.quotient_isCoveringMap {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] :
    IsCoveringMap (quotient G B F) :=
  (quotientCoveringMap (F := F) hq).isCoveringMap

private theorem
    DiagonalQuotient.quotient_isOpenQuotientMap {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] :
    IsOpenQuotientMap (quotient G B F) := by
  let := hq.toContinuousConstSMul
  exact MulAction.isOpenQuotientMap_quotientMk

private def DiagonalQuotient.patchMap {G : Type*} {B : Type*} {F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B)
    (x : patch hq b × F) : Space G B F :=
  quotient G B F (baseLocalInverse hq b x.1, x.2)

@[simp]
private theorem DiagonalQuotient.projection_patchMap {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) (x : patch hq b × F) :
    projection G B F (patchMap hq b x) = (x.1 : BaseSpace G B) :=
  baseQuotient_localInverse hq b x.1.property

private theorem DiagonalQuotient.patchMap_injective {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    Function.Injective (patchMap (F := F) hq b) := by
  let := hq.isCancelSMul
  intro x y hxy
  have hbase : x.1 = y.1 :=
    Subtype.ext (by simpa only [projection_patchMap] using congrArg (projection G B F) hxy)
  obtain ⟨g, hg⟩ := (quotient_eq_iff G B F _ _).mp hxy
  have hgbase : g • baseLocalInverse hq b y.1 = baseLocalInverse hq b y.1 := by
    have he := congrArg Prod.fst hg
    change g • baseLocalInverse hq b y.1 = baseLocalInverse hq b x.1 at he
    simpa only [hbase] using he
  have hg1 : g = 1 :=
    IsCancelSMul.right_cancel _ _ (baseLocalInverse hq b y.1)
      (hgbase.trans (one_smul G (baseLocalInverse hq b y.1)).symm)
  apply Prod.ext hbase
  simpa only [hg1, one_smul] using (congrArg Prod.snd hg).symm

private theorem DiagonalQuotient.patchMap_continuous {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    Continuous (patchMap (F := F) hq b) :=
  (quotient_continuous G B F).comp
    ((baseLocalInverse hq b).isOpenEmbedding_restrict.continuous.prodMap continuous_id)

private theorem
    DiagonalQuotient.patchMap_openEmbedding {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] (b : B) :
    Topology.IsOpenEmbedding (patchMap (F := F) hq b) :=
  .of_continuous_injective_isOpenMap (patchMap_continuous hq b) (patchMap_injective hq b)
    ((quotient_isOpenQuotientMap (F := F) hq).isOpenMap.comp
      ((baseLocalInverse hq b).isOpenEmbedding_restrict.isOpenMap.prodMap IsOpenMap.id))

private theorem DiagonalQuotient.patchMap_range {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (b : B) :
    Set.range (patchMap (F := F) hq b) = projection G B F ⁻¹' (patch hq b : Set _) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_preimage, projection_patchMap]
    exact x.1.property
  · intro hy
    obtain ⟨⟨z, f⟩, rfl⟩ := quotient_surjective G B F y
    change baseQuotient G B z ∈ patch hq b at hy
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp (baseQuotient_localInverse hq b hy)
    refine ⟨(⟨baseQuotient G B z, hy⟩, g • f), ?_⟩
    apply (quotient_eq_iff G B F _ _).mpr
    exact ⟨g, Prod.ext hg rfl⟩

private def
    DiagonalQuotient.patchHomeomorph {G : Type*} {B : Type*} {F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] (b : B) :
    (projection G B F ⁻¹' (patch hq b : Set _)) ≃ₜ (patch hq b × F) :=
  ((patchMap_openEmbedding (F := F) hq b).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (patchMap_range hq b))).symm

private theorem
    DiagonalQuotient.patchHomeomorph_projection {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] (b : B)
    (x : projection G B F ⁻¹' (patch hq b : Set _)) :
    ((patchHomeomorph hq b x).1 : BaseSpace G B) = projection G B F x.val := by
  have hp := projection_patchMap hq b (patchHomeomorph hq b x)
  have he : patchMap hq b (patchHomeomorph hq b x) = x.val :=
    congrArg Subtype.val ((patchHomeomorph hq b).symm_apply_apply x)
  rw [he] at hp
  exact hp.symm

private def DiagonalQuotient.fibreHomeomorphOver {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] (b : B) :
    (projection G B F ⁻¹' {baseQuotient G B b}) ≃ₜ F :=
  fibreHomeomorphOfLocalTrivializations (projection G B F) (patch hq) (patchHomeomorph hq)
    (patchHomeomorph_projection hq) b (baseQuotient G B b) (baseQuotient_mem_patch hq b)

private theorem DiagonalQuotient.projection_proper {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F] [CompactSpace F] :
    IsProperMap (projection G B F) :=
  proper_of_localTrivializations (projection G B F) (projection_continuous G B F) (patch hq)
    (patch_cover hq) (patchHomeomorph hq) (patchHomeomorph_projection hq)

private theorem DiagonalQuotient.spaceT2Space {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F]
    [T2Space (BaseSpace G B)] [T2Space F] : T2Space (Space G B F) :=
  t2Space_of_localTrivializations (projection G B F) (projection_continuous G B F) (patch hq)
    (patch_cover hq) (patchHomeomorph hq)

private theorem DiagonalQuotient.baseT2Space {G : Type*} {B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G) [T2Space B]
    [LocallyCompactSpace B] [ProperlyDiscontinuousSMul G B] : T2Space (BaseSpace G B) := by
  let := hq.toContinuousConstSMul
  infer_instance

private theorem DiagonalQuotient.spaceSecondCountable {G : Type*} {B : Type*} {F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) [ContinuousConstSMul G F]
    [SecondCountableTopology B] [SecondCountableTopology F] :
    SecondCountableTopology (Space G B F) :=
  (quotient_isQuotientMap G B F).secondCountableTopology
    (quotient_isOpenQuotientMap (F := F) hq).isOpenMap

end Mathoverflow1973

end
