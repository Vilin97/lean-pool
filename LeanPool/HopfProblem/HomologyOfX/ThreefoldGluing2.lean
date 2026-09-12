/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7

/-!
# Hopf problem: homology of x · threefold gluing 2

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

private theorem ThreefoldGluing.Data.restrictedProjection_eq {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) :
    (D.patch i : Set B).restrictPreimage D.projection =
      D.localProjection i ∘ (D.patchHomeomorph i).symm := by
  funext x
  simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using
    D.patchHomeomorph_projection i ((D.patchHomeomorph i).symm x)

private theorem ThreefoldGluing.Data.restrictedProjection_proper {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) (hi : IsProperMap (D.localProjection i)) :
    IsProperMap ((D.patch i : Set B).restrictPreimage D.projection) := by
  rw [D.restrictedProjection_eq]
  exact hi.comp (D.patchHomeomorph i).symm.isProperMap

private theorem
    ThreefoldGluing.Data.projection_fibre_eq_localImage {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) (b : D.patch i) :
    D.projection ⁻¹' {(b : B)} = D.inclusion i '' (D.localProjection i ⁻¹' { b }) := by
  ext x
  constructor
  · intro hx
    change D.projection x = (b : B) at hx
    have hi : x ∈ Set.range (D.inclusion i) := by
      rw [D.inclusion_range]
      change D.projection x ∈ D.patch i
      rw [hx]
      exact b.property
    obtain ⟨z, rfl⟩ := hi
    refine ⟨z, ?_, rfl⟩
    change D.localProjection i z = b
    apply Subtype.ext
    exact (D.projection_inclusion i z).symm.trans hx
  · rintro ⟨z, hz, rfl⟩
    change D.localProjection i z = b at hz
    change D.projection (D.inclusion i z) = (b : B)
    exact (D.projection_inclusion i z).trans (congrArg Subtype.val hz)

private theorem ThreefoldGluing.Data.projection_fibre_compact {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (hproper : ∀ i : D.J, IsProperMap (D.localProjection i))
    (b : B) : IsCompact (D.projection ⁻¹' { b }) := by
  obtain ⟨i, hi⟩ := D.cover.exists_mem b
  rw [D.projection_fibre_eq_localImage i ⟨b, hi⟩]
  exact
    ((hproper i).isCompact_preimage isCompact_singleton).image
      (D.inclusion_openEmbedding i).continuous

private theorem ThreefoldGluing.Data.projection_proper {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (hproper : ∀ i : D.J, IsProperMap (D.localProjection i)) :
    IsProperMap D.projection := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨D.projection_continuous, ?_, D.projection_fibre_compact hproper⟩
  apply D.cover.isClosedMap_iff_restrictPreimage.mpr
  intro i
  exact (D.restrictedProjection_proper i (hproper i)).isClosedMap

private theorem ThreefoldGluing.Data.compactSpace {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [CompactSpace B]
    (hproper : ∀ i : D.J, IsProperMap (D.localProjection i)) : CompactSpace D.Space := by
  constructor
  simpa only [Set.preimage_univ] using
    (D.projection_proper hproper).isCompact_preimage
      (isCompact_univ : IsCompact (Set.univ : Set B))

public
theorem ThreefoldGluing.Data.secondCountableSpace_of_compactBase {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [CompactSpace B] [∀ i, SecondCountableTopology (D.piece i)] :
    SecondCountableTopology D.Space := by
  classical
  obtain ⟨s, hs⟩ := D.cover.exists_finite_of_compactSpace
  let : ∀ i : s, SecondCountableTopology (Set.range (D.inclusion i.val)) := fun i =>
    (D.inclusion_openEmbedding i.val).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply
    TopologicalSpace.secondCountableTopology_of_countable_cover (U := fun i : s =>
      Set.range (D.inclusion i.val)) (fun i => (D.inclusion_openEmbedding i.val).isOpen_range)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := hs.exists_mem (D.projection x)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [D.inclusion_range]
  exact hi

private def
    ThreefoldGluing.Data.Compatible {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    {Y : Type*} (f : ∀ i, D.piece i → Y) : Prop :=
  ∀ i j x, x ∈ (D.transition i j).source → f j (D.transition i j x) = f i x

private def
    ThreefoldGluing.Data.descend {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    {Y : Type*} (f : ∀ i, D.piece i → Y) (_hf : D.Compatible f) (x : D.Space) : Y :=
  f (D.representative x).1 (D.representative x).2

@[simp]
private theorem ThreefoldGluing.Data.descend_inclusion {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) {Y : Type*} (f : ∀ i, D.piece i → Y) (hf : D.Compatible f)
    (i : D.J) (x : D.piece i) : D.descend f hf (D.inclusion i x) = f i x := by
  let r := D.representative (D.inclusion i x)
  have h := (D.inclusion_eq_iff r.1 i r.2 x).mp (D.inclusion_representative _)
  change f r.1 r.2 = f i x
  rw [← h.2]
  exact (hf r.1 i r.2 h.1).symm

private def ThreefoldGluing.Data.liftedPatch {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) : TopologicalSpace.Opens D.Space :=
  ⟨D.projection ⁻¹' (D.patch i : Set B), (D.patch i).isOpen.preimage D.projection_continuous⟩

private theorem ThreefoldGluing.Data.patchHomeomorph_symm_eq_parametrization {B : Type u}
    [TopologicalSpace B] (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] (i : D.J)
    (x : D.liftedPatch i) : (D.patchHomeomorph i).symm x = (D.parametrization i).symm x.val := by
  have hx : D.inclusion i ((D.patchHomeomorph i).symm x) = x.val :=
    congrArg Subtype.val ((D.patchHomeomorph i).apply_symm_apply x)
  rw [← hx, D.parametrization_symm_inclusion]

private def ThreefoldGluing.Data.patchBiholomorph {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [∀ i, ChartedSpace E (D.piece i)]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]
    (hhol :
      ∀ i j,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
          (D.transition i j).source)
    (i : D.J) :
    letI := D.chartedSpace (E := E)
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) (D.piece i)
      (D.liftedPatch i) ω := by
  letI := D.chartedSpace (E := E)
  let e : D.piece i ≃ₜ D.liftedPatch i := D.patchHomeomorph i
  refine
    { toEquiv := e.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · intro x
    have he :
      ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
          (fun z : D.piece i => ((e z).val : D.Space)) x ↔
        ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω e x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact he.mp ((D.inclusion_holomorphic hhol i) x)
  · intro x
    have hx : x.val ∈ (D.parametrization i).target := by
      rw [D.parametrization_target, D.inclusion_range]
      exact x.property
    have h :=
      ((D.parametrization_symm_holomorphic hhol i).contMDiffAt
            ((D.parametrization i).open_target.mem_nhds hx)).comp
        x contMDiff_subtype_val.contMDiffAt
    convert h using 1
    funext y
    exact D.patchHomeomorph_symm_eq_parametrization i y

private theorem ThreefoldGluing.Data.projection_fibre_isConnected {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B)
    (hlocal : ∀ i (b : D.patch i), IsConnected (D.localProjection i ⁻¹' { b })) (b : B) :
    IsConnected (D.projection ⁻¹' { b }) := by
  obtain ⟨i, hi⟩ := D.cover.exists_mem b
  rw [D.projection_fibre_eq_localImage i ⟨b, hi⟩]
  exact
    (hlocal i ⟨b, hi⟩).image (D.inclusion i) (D.inclusion_openEmbedding i).continuous.continuousOn

private theorem ThreefoldGluing.Data.projection_surjective_of_connected_fibres {B : Type u}
    [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    (hlocal : ∀ i (b : D.patch i), IsConnected (D.localProjection i ⁻¹' { b })) :
    Function.Surjective D.projection := by
  intro b
  obtain ⟨x, hx⟩ := (D.projection_fibre_isConnected hlocal b).nonempty
  exact ⟨x, hx⟩

private theorem ThreefoldGluing.Data.connectedSpace {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [ConnectedSpace B]
    (hproper : ∀ i : D.J, IsProperMap (D.localProjection i))
    (hlocal : ∀ i (b : D.patch i), IsConnected (D.localProjection i ⁻¹' { b })) :
    ConnectedSpace D.Space := by
  have hq : Topology.IsQuotientMap D.projection :=
    (D.projection_proper hproper).isClosedMap.isQuotientMap D.projection_continuous
      (D.projection_surjective_of_connected_fibres hlocal)
  apply connectedSpace_iff_univ.mpr
  simpa only [Set.preimage_univ] using
    hq.isCoinducing.isConnected_preimage_of_isClosed (D.projection_fibre_isConnected hlocal)
      isClosed_univ (isConnected_univ : IsConnected (Set.univ : Set B))

end Mathoverflow1973

end
