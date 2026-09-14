/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Smale8
import all LeanPool.HopfProblem.Toric.DiagonalQuotient1
import all LeanPool.HopfProblem.Recognition.Smale8

/-!
# Hopf problem: toric · diagonal quotient 3

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

private def DiagonalQuotient.sectionMap {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B)) (x : U × F) :
    Space G B F :=
  quotient G B F (s x.1, x.2)

private theorem DiagonalQuotient.sectionMap_continuous {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B)) :
    Continuous (sectionMap (F := F) U s) :=
  (quotient_continuous G B F).comp (s.continuous.prodMap continuous_id)

public
theorem DiagonalQuotient.baseSection_openEmbedding {G B : Type*} [Group G] [MulAction G B]
    [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) : Topology.IsOpenEmbedding s := by
  apply hq.isCoveringMap.isLocalHomeomorph.isOpenEmbedding_of_comp _ s.continuous
  have hcomp : baseQuotient G B ∘ s = (Subtype.val : U → BaseSpace G B) := funext hs
  rw [hcomp]
  exact U.isOpenEmbedding'

@[simp]
private theorem DiagonalQuotient.projection_sectionMap {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] (U : TopologicalSpace.Opens (BaseSpace G B))
    (s : C(U, B)) (hs : ∀ x : U, baseQuotient G B (s x) = x) (x : U × F) :
    projection G B F (sectionMap U s x) = (x.1 : BaseSpace G B) :=
  hs x.1

private theorem DiagonalQuotient.sectionMap_injective {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) : Function.Injective (sectionMap (F := F) U s) := by
  intro x y hxy
  have hbase : x.1 = y.1 :=
    Subtype.ext
      (by simpa only [projection_sectionMap U s hs] using congrArg (projection G B F) hxy)
  apply Prod.ext hbase
  apply fibreInclusion_injective hq (s y.1)
  simpa only [sectionMap, fibreInclusion, hbase] using hxy

private theorem DiagonalQuotient.sectionMap_range {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    Set.range (sectionMap (F := F) U s) = projection G B F ⁻¹' (U : Set _) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_preimage, projection_sectionMap U s hs]
    exact x.1.property
  · intro hy
    obtain ⟨⟨z, f⟩, rfl⟩ := quotient_surjective G B F y
    change baseQuotient G B z ∈ U at hy
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp (hs ⟨baseQuotient G B z, hy⟩)
    refine ⟨(⟨baseQuotient G B z, hy⟩, g • f), ?_⟩
    exact (quotient_eq_iff G B F _ _).mpr ⟨g, Prod.ext hg rfl⟩

private theorem DiagonalQuotient.sectionMap_openEmbedding {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (U : TopologicalSpace.Opens (BaseSpace G B))
    (s : C(U, B)) (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    Topology.IsOpenEmbedding (sectionMap (F := F) U s) :=
  .of_continuous_injective_isOpenMap (sectionMap_continuous U s) (sectionMap_injective hq U s hs)
    ((quotient_isOpenQuotientMap (F := F) hq).isOpenMap.comp
      ((baseSection_openEmbedding hq U s hs).isOpenMap.prodMap IsOpenMap.id))

private def
    DiagonalQuotient.sectionHomeomorph {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (U : TopologicalSpace.Opens (BaseSpace G B))
    (s : C(U, B)) (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    (projection G B F ⁻¹' (U : Set _)) ≃ₜ (U × F) :=
  ((sectionMap_openEmbedding (F := F) hq U s hs).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (sectionMap_range hq U s hs))).symm

private theorem
    DiagonalQuotient.sectionHomeomorph_projection {G B F : Type*} [Group G] [MulAction G B]
    [MulAction G F] [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G) (U : TopologicalSpace.Opens (BaseSpace G B))
    (s : C(U, B)) (hs : ∀ x : U, baseQuotient G B (s x) = x)
    (x : projection G B F ⁻¹' (U : Set _)) :
    ((sectionHomeomorph hq U s hs x).1 : BaseSpace G B) = projection G B F x.val := by
  have hp := projection_sectionMap U s hs (sectionHomeomorph hq U s hs x)
  have he : sectionMap U s (sectionHomeomorph hq U s hs x) = x.val :=
    congrArg Subtype.val ((sectionHomeomorph hq U s hs).symm_apply_apply x)
  rw [he] at hp
  exact hp.symm

@[simp]
private theorem DiagonalQuotient.sectionHomeomorph_apply_quotient {G B F : Type*} [Group G]
    [MulAction G B] [MulAction G F] [TopologicalSpace B] [TopologicalSpace F]
    [ContinuousConstSMul G F] (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : TopologicalSpace.Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) (x : U) (f : F) :
    sectionHomeomorph hq U s hs
        ⟨quotient G B F (s x, f), by
          change baseQuotient G B (s x) ∈ U
          rw [hs x]
          exact x.property⟩ =
      (x, f) :=
  (sectionHomeomorph hq U s hs).apply_symm_apply (x, f)

end Mathoverflow1973

end
