/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Smale8
public import LeanPool.HopfProblem.Foundations.Core5
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Foundations.LineBundleTransport
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology2
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Recognition.Smale5
import all LeanPool.HopfProblem.Recognition.Degree1
import all LeanPool.HopfProblem.Recognition.Degree2
import all LeanPool.HopfProblem.Recognition.Smale6
import all LeanPool.HopfProblem.Recognition.Smale8
import all LeanPool.HopfProblem.Foundations.Core5

/-!
# Hopf problem: recognition · smale 9

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
    Smale.HandleCoreAttachment.core {N P X : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    [TopologicalSpace X] (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) :
    C(Smale.MorseHandle.UnitDisk N, X) :=
  ⟨fun x => h (x, ⟨0, by simp⟩), h.continuous.comp (continuous_id.prodMk continuous_const)⟩

private def Smale.HandleCoreAttachment.coreSpace {N P R X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) : Set X :=
  Set.range r ∪ Set.range (core h)

private theorem Smale.HandleCoreAttachment.collapse_lands {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1)
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :
    h (Smale.HandleCoreDeformation.collapse z) ∈ coreSpace r h := by
  rcases Smale.HandleCoreDeformation.collapse_mem z with hz | hz
  · exact Or.inl ((hface (Smale.HandleCoreDeformation.collapse z)).mpr hz)
  · right
    refine ⟨(Smale.HandleCoreDeformation.collapse z).1, ?_⟩
    apply congrArg h
    exact Prod.ext rfl (Subtype.ext hz.symm)

private def Smale.HandleCoreAttachment.oldToCore {N P R X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) : C(R, coreSpace r h) :=
  ⟨fun a => ⟨r a, Or.inl (Set.mem_range_self a)⟩, hr.continuous.subtype_mk _⟩

private def Smale.HandleCoreAttachment.handleToCore {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) :
    C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, coreSpace r h) :=
  ⟨fun z => ⟨h (Smale.HandleCoreDeformation.collapse z), collapse_lands r h hface z⟩,
    (h.continuous.comp Smale.HandleCoreDeformation.collapse.continuous).subtype_mk _⟩

private theorem Smale.HandleCoreAttachment.coreMaps_agree {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) (a : R)
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) (haz : r a = h z) :
    oldToCore r h hr a = handleToCore r h hface z := by
  have hz : ‖(z.1 : N)‖ = 1 := (hface z).mp ⟨a, haz⟩
  apply Subtype.ext
  change r a = h (Smale.HandleCoreDeformation.collapse z)
  rw [Smale.HandleCoreDeformation.collapse_face z hz]
  exact haz

private def Smale.HandleCoreAttachment.retraction {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) : C(X, coreSpace r h) :=
  Smale.ClosedCover.mapOfClosedPieces r h hr hh hcover (oldToCore r h hr) (handleToCore r h hface)
    (coreMaps_agree r h hr hface)

private theorem Smale.HandleCoreAttachment.retraction_old {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) (a : R) :
    (retraction r h hr hh hcover hface (r a) : X) = r a :=
  congrArg Subtype.val
    (Smale.ClosedCover.mapOfClosedPieces_left r h hr hh hcover (oldToCore r h hr)
      (handleToCore r h hface) (coreMaps_agree r h hr hface) a)

private theorem
    Smale.HandleCoreAttachment.retraction_handle {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1)
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :
    (retraction r h hr hh hcover hface (h z) : X) = h (Smale.HandleCoreDeformation.collapse z) :=
  congrArg Subtype.val
    (Smale.ClosedCover.mapOfClosedPieces_right r h hr hh hcover (oldToCore r h hr)
      (handleToCore r h hface) (coreMaps_agree r h hr hface) z)

private theorem Smale.HandleCoreAttachment.retraction_fixed {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) (x : X) (hx : x ∈ coreSpace r h) :
    (retraction r h hr hh hcover hface x : X) = x := by
  rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · exact retraction_old r h hr hh hcover hface a
  · change (retraction r h hr hh hcover hface (h (z, ⟨0, by simp⟩)) : X) = h (z, ⟨0, by simp⟩)
    rw [retraction_handle, Smale.HandleCoreDeformation.collapse_core _ rfl]

private theorem Smale.HandleCoreAttachment.time_cover {N P R X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hcover : Set.range r ∪ Set.range h = Set.univ) :
    Set.range (Prod.map (id : (unitInterval) → (unitInterval)) r) ∪
        Set.range (Prod.map (id : (unitInterval) → (unitInterval)) h) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨t, x⟩
  have hx : x ∈ Set.range r ∪ Set.range h := by rw [hcover]; trivial
  rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inl ⟨(t, a), rfl⟩
  · exact Or.inr ⟨(t, z), rfl⟩

private def
    Smale.HandleCoreAttachment.oldMotion {R X : Type*} [TopologicalSpace R] [TopologicalSpace X]
    (r : R → X) (hr : Topology.IsClosedEmbedding r) : C((unitInterval) × R, X) :=
  ⟨fun q => r q.2, hr.continuous.comp continuous_snd⟩

private def Smale.HandleCoreAttachment.handleMotion {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace X]
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) :
    C((unitInterval) × (Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P), X) :=
  h.comp Smale.HandleCoreDeformation.deformation.toHomotopy.toContinuousMap

private theorem Smale.HandleCoreAttachment.motions_agree {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1)
    (a : (unitInterval) × R)
    (z : (unitInterval) × (Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P))
    (haz : Prod.map id r a = Prod.map id h z) : oldMotion r hr a = handleMotion h z := by
  have ha : r a.2 = h z.2 := congrArg Prod.snd haz
  have hz : z.2 ∈ Smale.HandleCoreDeformation.faceCore := Or.inl ((hface z.2).mp ⟨a.2, ha⟩)
  change r a.2 = h (Smale.HandleCoreDeformation.deformation (z.1, z.2))
  rw [Smale.HandleCoreDeformation.deformation.eq_fst z.1 hz]
  exact ha

private def
    Smale.HandleCoreAttachment.motion {N P R X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R] [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) : C((unitInterval) × X, X) :=
  Smale.ClosedCover.mapOfClosedPieces (Prod.map id r) (Prod.map id h)
    (Topology.IsClosedEmbedding.id.prodMap hr) (Topology.IsClosedEmbedding.id.prodMap hh)
    (time_cover r h hcover) (oldMotion r hr) (handleMotion h) (motions_agree r h hr hface)

private theorem Smale.HandleCoreAttachment.motion_old {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) (t : (unitInterval)) (a : R) :
    motion r h hr hh hcover hface (t, r a) = r a :=
  Smale.ClosedCover.mapOfClosedPieces_left (Prod.map id r) (Prod.map id h)
    (Topology.IsClosedEmbedding.id.prodMap hr) (Topology.IsClosedEmbedding.id.prodMap hh)
    (time_cover r h hcover) (oldMotion r hr) (handleMotion h) (motions_agree r h hr hface) (t, a)

private theorem Smale.HandleCoreAttachment.motion_handle {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) (t : (unitInterval))
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :
    motion r h hr hh hcover hface (t, h z) = h (Smale.HandleCoreDeformation.deformation (t, z)) :=
  Smale.ClosedCover.mapOfClosedPieces_right (Prod.map id r) (Prod.map id h)
    (Topology.IsClosedEmbedding.id.prodMap hr) (Topology.IsClosedEmbedding.id.prodMap hh)
    (time_cover r h hcover) (oldMotion r hr) (handleMotion h) (motions_agree r h hr hface) (t, z)

private def Smale.HandleCoreAttachment.coreInclusion {N P R X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) :
    C(coreSpace r h, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def Smale.HandleCoreAttachment.deformation {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) :
    (ContinuousMap.id X).HomotopyRel
      ((coreInclusion r h).comp (retraction r h hr hh hcover hface)) (coreSpace r h)
    where
  toFun := motion r h hr hh hcover hface
  continuous_toFun := (motion r h hr hh hcover hface).continuous
  map_zero_left
    x := by
    have hx : x ∈ Set.range r ∪ Set.range h := by rw [hcover]; trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · exact motion_old r h hr hh hcover hface 0 a
    · rw [motion_handle]
      exact congrArg h (Smale.HandleCoreDeformation.deformation.toHomotopy.map_zero_left z)
  map_one_left
    x := by
    change motion r h hr hh hcover hface (1, x) = (retraction r h hr hh hcover hface x : X)
    have hx : x ∈ Set.range r ∪ Set.range h := by rw [hcover]; trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · rw [motion_old, retraction_old]
    · rw [motion_handle, retraction_handle]
      exact congrArg h (Smale.HandleCoreDeformation.deformation.toHomotopy.map_one_left z)
  prop' t x
    hx := by
    change motion r h hr hh hcover hface (t, x) = x
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · exact motion_old r h hr hh hcover hface t a
    · change motion r h hr hh hcover hface (t, h (z, ⟨0, by simp⟩)) = h (z, ⟨0, by simp⟩)
      rw [motion_handle]
      exact congrArg h (Smale.HandleCoreDeformation.deformation.eq_fst t (Or.inr rfl))

private def Smale.HandleCoreAttachment.homotopyEquiv {N P R X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R]
    [TopologicalSpace X] (r : R → X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hr : Topology.IsClosedEmbedding r) (hh : Topology.IsClosedEmbedding h)
    (hcover : Set.range r ∪ Set.range h = Set.univ)
    (hface : ∀ z, h z ∈ Set.range r ↔ ‖(z.1 : N)‖ = 1) : coreSpace r h ≃ₕ X
    where
  toFun := coreInclusion r h
  invFun := retraction r h hr hh hcover hface
  left_inv := by
    have heq :
      (retraction r h hr hh hcover hface).comp (coreInclusion r h) =
        ContinuousMap.id (coreSpace r h) := by
      apply ContinuousMap.ext
      intro x
      exact Subtype.ext (retraction_fixed r h hr hh hcover hface x.val x.property)
    rw [heq]
  right_inv := ⟨(deformation r h hr hh hcover hface).toHomotopy.symm⟩

private def Smale.ClosedHandleCore.oldInclusion {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) :
    C(A, ↥(A ∪ Set.range h)) :=
  ⟨Set.inclusion (fun _ hx => Or.inl hx), continuous_inclusion _⟩

private def Smale.ClosedHandleCore.handleInclusion {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) :
    C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, ↥(A ∪ Set.range h)) :=
  ⟨fun z => ⟨h z, Or.inr (Set.mem_range_self z)⟩, h.continuous.subtype_mk _⟩

private theorem Smale.ClosedHandleCore.old_closed {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) (hA : IsClosed A) :
    Topology.IsClosedEmbedding (oldInclusion A h) :=
  Smale.ClosedCover.isClosedEmbedding_codRestrict hA.isClosedEmbedding_subtypeVal
    (fun x => Or.inl x.property)

private theorem Smale.ClosedHandleCore.handle_closed {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hh : Topology.IsClosedEmbedding h) : Topology.IsClosedEmbedding (handleInclusion A h) :=
  Smale.ClosedCover.isClosedEmbedding_codRestrict hh (fun z => Or.inr (Set.mem_range_self z))

private theorem Smale.ClosedHandleCore.pieces_cover {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) :
    Set.range (oldInclusion A h) ∪ Set.range (handleInclusion A h) = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨x, hx | ⟨z, rfl⟩⟩
  · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inr ⟨z, rfl⟩

private theorem Smale.ClosedHandleCore.handle_mem_old_iff {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :
    handleInclusion A h z ∈ Set.range (oldInclusion A h) ↔ h z ∈ A := by
  constructor
  · rintro ⟨a, ha⟩
    have heq : (a : X) = h z := congrArg Subtype.val ha
    exact heq ▸ a.property
  · intro hz
    exact ⟨⟨h z, hz⟩, rfl⟩

private theorem Smale.ClosedHandleCore.core_subset {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) :
    A ∪ Set.range (Smale.HandleCoreAttachment.core h) ⊆ A ∪ Set.range h := by
  rintro x (hx | ⟨z, rfl⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨(z, ⟨0, by simp⟩), rfl⟩

private theorem Smale.ClosedHandleCore.coreSpace_iff {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (x : ↥(A ∪ Set.range h)) :
    x ∈ Smale.HandleCoreAttachment.coreSpace (oldInclusion A h) (handleInclusion A h) ↔
      x.val ∈ A ∪ Set.range (Smale.HandleCoreAttachment.core h) := by
  constructor
  · rintro (⟨a, ha⟩ | ⟨z, hz⟩)
    · left
      have heq : (a : X) = x.val := congrArg Subtype.val ha
      exact heq ▸ a.property
    · right
      exact ⟨z, congrArg Subtype.val hz⟩
  · rintro (hx | ⟨z, hz⟩)
    · exact Or.inl ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · exact Or.inr ⟨z, Subtype.ext hz⟩

private def Smale.ClosedHandleCore.coreUnionHomeomorph {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) :
    ↥(A ∪ Set.range (Smale.HandleCoreAttachment.core h)) ≃ₜ
      Smale.HandleCoreAttachment.coreSpace (oldInclusion A h) (handleInclusion A h)
    where
  toFun x := ⟨⟨x.val, core_subset A h x.property⟩, (coreSpace_iff A h _).mpr x.property⟩
  invFun x := ⟨x.val.val, (coreSpace_iff A h x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private def Smale.ClosedHandleCore.unionHomotopyEquiv {N P X : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) [NormedSpace ℝ N]
    [NormedSpace ℝ P] (hA : IsClosed A) (hh : Topology.IsClosedEmbedding h)
    (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) :
    ↥(A ∪ Set.range (Smale.HandleCoreAttachment.core h)) ≃ₕ ↥(A ∪ Set.range h) :=
  (coreUnionHomeomorph A h).toHomotopyEquiv.trans
    (Smale.HandleCoreAttachment.homotopyEquiv (oldInclusion A h) (handleInclusion A h)
      (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
      (fun z => (handle_mem_old_iff A h z).trans (hface z)))

attribute [local instance 100] Classical.propDecidable in
private abbrev
    Smale.ManifoldMorse.MorseSurgeryData.HandleDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :=
  Smale.MorseHandle.UnitDisk d.chart.NegativeCoordinates ×
    Smale.MorseHandle.UnitDisk d.chart.PositiveCoordinates

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.handleMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) : C(d.HandleDomain, M) :=
  d.chart.attachingHandleMap d.radius d.radius_pos d.block

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.handleFacePoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (u : Smale.PuncturedHandle.UnitSphere d.chart.NegativeCoordinates)
    (v : Smale.MorseHandle.UnitDisk d.chart.PositiveCoordinates) : d.HandleDomain :=
  (⟨u, Metric.sphere_subset_closedBall u.property⟩, v)

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.handleMap_core {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (u : Smale.PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    d.handleMap (d.handleFacePoint u ⟨0, by simp⟩) = (d.surgery.attachingSphere u : M) := by
  rw [d.attaching_eq]
  rfl

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.coreMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C(Smale.MorseHandle.UnitDisk d.chart.NegativeCoordinates, M) :=
  Smale.HandleCoreAttachment.core d.handleMap

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.coreMap_boundary {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (u : Smale.PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    d.coreMap ⟨u, Metric.sphere_subset_closedBall u.property⟩ =
      (d.surgery.attachingSphere u : M) :=
  d.handleMap_core u

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.coreMap_lower_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (u : Smale.MorseHandle.UnitDisk d.chart.NegativeCoordinates) :
    f (d.coreMap u) ≤ f p - d.radius ^ 2 ↔ ‖(u : d.chart.NegativeCoordinates)‖ = 1 :=
  d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block (u, ⟨0, by simp⟩)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.coreMap_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] :
    Topology.IsClosedEmbedding d.coreMap := by
  apply d.coreMap.continuous.isClosedEmbedding
  intro x y hxy
  have heq :=
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block).injective hxy
  exact congrArg Prod.fst heq

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.coreUnionHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f) :
    ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) ≃ₕ
      { y : M // f y ≤ f p + d.radius ^ 2 } :=
  (Smale.ClosedHandleCore.unionHomotopyEquiv {y : M | f y ≤ f p - d.radius ^ 2} d.handleMap
        (isClosed_le hf continuous_const)
        (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
        (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)).trans
    d.attachmentHomeomorph.toHomotopyEquiv

private structure Smale.EmbeddedCellAttachment (N X : Type*) [NormedAddCommGroup N]
    [TopologicalSpace X] where
  old : Set X
  old_closed : IsClosed old
  cell : C(MorseHandle.UnitDisk N, X)
  cell_closed : Topology.IsClosedEmbedding cell
  cover : old ∪ Set.range cell = Set.univ
  boundary : ∀ z, cell z ∈ old ↔ ‖(z : N)‖ = 1

private def
    Smale.EmbeddedCellAttachment.ofUnion {N X : Type*} [NormedAddCommGroup N] [TopologicalSpace X]
    (A : Set X) (e : C(Smale.MorseHandle.UnitDisk N, X)) (hA : IsClosed A)
    (he : Topology.IsClosedEmbedding e) (hface : ∀ z, e z ∈ A ↔ ‖(z : N)‖ = 1) :
    Smale.EmbeddedCellAttachment N ↥(A ∪ Set.range e)
    where
  old := {x | x.val ∈ A}
  old_closed := hA.preimage continuous_subtype_val
  cell := ⟨fun z => ⟨e z, Or.inr (Set.mem_range_self z)⟩, e.continuous.subtype_mk _⟩
  cell_closed :=
    Smale.ClosedCover.isClosedEmbedding_codRestrict he (fun z => Or.inr (Set.mem_range_self z))
  cover := by
    apply Set.eq_univ_of_forall
    rintro ⟨x, hx | ⟨z, rfl⟩⟩
    · exact Or.inl hx
    · exact Or.inr ⟨z, rfl⟩
  boundary := hface

private def Smale.EmbeddedCellAttachment.oldNeighborhood {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) : Set X :=
  (D.cell '' {z : Smale.MorseHandle.UnitDisk N | ‖(z : N)‖ ≤ 1 / 2})ᶜ

private def Smale.EmbeddedCellAttachment.diskPatch {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) : Set X :=
  D.oldᶜ

private theorem
    Smale.EmbeddedCellAttachment.isOpen_oldNeighborhood {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) : IsOpen D.oldNeighborhood :=
  (D.cell_closed.isClosedMap _
      (isClosed_le continuous_subtype_val.norm continuous_const)).isOpen_compl

private theorem Smale.EmbeddedCellAttachment.isOpen_diskPatch {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) : IsOpen D.diskPatch :=
  D.old_closed.isOpen_compl

private theorem Smale.EmbeddedCellAttachment.cell_mem_oldNeighborhood_iff {N X : Type*}
    [NormedAddCommGroup N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (z : Smale.MorseHandle.UnitDisk N) : D.cell z ∈ D.oldNeighborhood ↔ 1 / 2 < ‖(z : N)‖ := by
  constructor
  · intro hz
    by_contra! hnorm
    exact hz ⟨z, hnorm, rfl⟩
  · rintro hnorm ⟨w, hw, heq⟩
    have hwz : w = z := D.cell_closed.injective heq
    subst w
    exact (not_le_of_gt hnorm) hw

private theorem
    Smale.EmbeddedCellAttachment.cell_mem_diskPatch_iff {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (z : Smale.MorseHandle.UnitDisk N) : D.cell z ∈ D.diskPatch ↔ ‖(z : N)‖ < 1 := by
  change D.cell z ∉ D.old ↔ ‖(z : N)‖ < 1
  rw [D.boundary]
  have hz : ‖(z : N)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
  constructor
  · intro h
    exact lt_of_le_of_ne hz h
  · exact ne_of_lt

private theorem
    Smale.EmbeddedCellAttachment.old_subset_neighborhood {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) : D.old ⊆ D.oldNeighborhood := by
  rintro x hx ⟨z, hz, rfl⟩
  have heq := (D.boundary z).mp hx
  change ‖(z : N)‖ ≤ 1 / 2 at hz
  linarith

private theorem Smale.EmbeddedCellAttachment.open_cover {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    D.oldNeighborhood ∪ D.diskPatch = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ D.old
  · exact Or.inl (D.old_subset_neighborhood hx)
  · exact Or.inr hx

private theorem
    Smale.EmbeddedCellAttachment.diskPatch_subset_range {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    D.diskPatch ⊆ Set.range D.cell := by
  intro x hx
  have hcover : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  exact hcover.resolve_left hx

private theorem
    Smale.EmbeddedCellAttachment.overlap_subset_range {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    D.oldNeighborhood ∩ D.diskPatch ⊆ Set.range D.cell :=
  Set.inter_subset_right.trans D.diskPatch_subset_range

private def Smale.EmbeddedCellAttachment.diskHomeomorph {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    { z : Smale.MorseHandle.UnitDisk N // ‖(z : N)‖ < 1 } ≃ₜ D.diskPatch :=
  (Homeomorph.setCongr
        (by
          ext z
          exact (D.cell_mem_diskPatch_iff z).symm)).trans
    (D.cell_closed.isEmbedding.homeomorphOfSubsetRange D.diskPatch_subset_range)

private def Smale.EmbeddedCellAttachment.overlapHomeomorph {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    { z : Smale.MorseHandle.UnitDisk N // 1 / 2 < ‖(z : N)‖ ∧ ‖(z : N)‖ < 1 } ≃ₜ
      ↥(D.oldNeighborhood ∩ D.diskPatch) :=
  (Homeomorph.setCongr
        (by
          ext z
          exact
            (and_congr (D.cell_mem_oldNeighborhood_iff z)
                (D.cell_mem_diskPatch_iff z)).symm)).trans
    (D.cell_closed.isEmbedding.homeomorphOfSubsetRange D.overlap_subset_range)

private abbrev Smale.OuterDisk.Space (E : Type*) [NormedAddCommGroup E] :=
  { z : Smale.MorseHandle.UnitDisk E // 1 / 2 < ‖(z : E)‖ }

private theorem Smale.OuterDisk.norm_pos {E : Type*} [NormedAddCommGroup E] (z : Space E) :
    0 < ‖(z.val : E)‖ := by linarith [z.property]

private def Smale.OuterDisk.sphereDisk {E : Type*} [NormedAddCommGroup E] :
    C(Metric.sphere (0 : E) 1, Smale.MorseHandle.UnitDisk E) :=
  ⟨Set.inclusion Metric.sphere_subset_closedBall, continuous_inclusion _⟩

private theorem Smale.OuterDisk.sphereDisk_mem {E : Type*} [NormedAddCommGroup E]
    (u : Metric.sphere (0 : E) 1) : 1 / 2 < ‖(sphereDisk u : E)‖ := by
  change 1 / 2 < ‖(u : E)‖
  rw [mem_sphere_zero_iff_norm.mp u.property]
  norm_num

private def Smale.OuterDisk.fromSphere {E : Type*} [NormedAddCommGroup E] :
    C(Metric.sphere (0 : E) 1, Space E) :=
  ⟨fun u => ⟨sphereDisk u, sphereDisk_mem u⟩, sphereDisk.continuous.subtype_mk _⟩

private def Smale.OuterDisk.toSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(Space E, Metric.sphere (0 : E) 1) :=
  ⟨fun z => Smale.RadialExtension.direction (z.val : E) (norm_ne_zero_iff.mp (norm_pos z).ne'),
    (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
              (fun z => (norm_pos z).ne')).smul
          (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
      _⟩

private theorem Smale.OuterDisk.fromSphere_toSphere_boundary {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (z : Space E) (hz : ‖(z.val : E)‖ = 1) : fromSphere (toSphere z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  change ‖(z.val : E)‖⁻¹ • (z.val : E) = (z.val : E)
  rw [hz, inv_one, one_smul]

private def Smale.OuterDisk.blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : (unitInterval) × Space E) : E :=
  ((1 - (q.1 : ℝ)) + (q.1 : ℝ) / ‖(q.2.val : E)‖) • (q.2.val : E)

private theorem Smale.OuterDisk.continuous_blendVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Continuous (blendVector (E := E)) := by
  have ht : Continuous (fun q : (unitInterval) × Space E => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous (fun q : (unitInterval) × Space E => (q.2.val : E)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_const.sub ht).add (ht.div hz.norm (fun q => (norm_pos q.2).ne'))).smul hz

private theorem
    Smale.OuterDisk.norm_blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : (unitInterval)) (z : Space E) :
    ‖blendVector (t, z)‖ = (1 - (t : ℝ)) * ‖(z.val : E)‖ + (t : ℝ) := by
  have hscale : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) / ‖(z.val : E)‖ :=
    add_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg t.property.1 (norm_pos z).le)
  rw [blendVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale, add_mul,
    div_mul_cancel₀ _ (norm_pos z).ne']

private theorem
    Smale.OuterDisk.norm_blendVector_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : (unitInterval)) (z : Space E) :
    1 / 2 < ‖blendVector (t, z)‖ ∧ ‖blendVector (t, z)‖ ≤ 1 := by
  rw [norm_blendVector]
  have hz : ‖(z.val : E)‖ ∈ Set.Ioc (1 / 2 : ℝ) 1 :=
    ⟨z.property, mem_closedBall_zero_iff.mp z.val.property⟩
  have h :=
    (convex_Ioc (𝕜 := ℝ) (1 / 2 : ℝ) 1) hz (by norm_num : (1 : ℝ) ∈ Ioc (1 / 2) 1)
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
  simpa only [Set.mem_Ioc, smul_eq_mul, mul_one] using h

private def Smale.OuterDisk.blend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : (unitInterval) × Space E) : Space E :=
  ⟨⟨blendVector q, mem_closedBall_zero_iff.mpr (norm_blendVector_mem q.1 q.2).2⟩,
    (norm_blendVector_mem q.1 q.2).1⟩

private theorem
    Smale.OuterDisk.continuous_blend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (blend (E := E)) :=
  (continuous_blendVector.subtype_mk _).subtype_mk _

private def Smale.OuterDisk.deformation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (ContinuousMap.id (Space E)).HomotopyRel (fromSphere.comp toSphere) {z | ‖(z.val : E)‖ = 1}
    where
  toFun := blend
  continuous_toFun := continuous_blend
  map_zero_left
    z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector]
  map_one_left
    z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector, fromSphere, sphereDisk, toSphere, Smale.RadialExtension.direction]
  prop' t z
    hz := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (t : ℝ)) + (t : ℝ) / ‖(z.val : E)‖) • (z.val : E) = (z.val : E)
    rw [hz, div_one, sub_add_cancel, one_smul]

private def Smale.EmbeddedCellAttachment.oldInclusion {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) : C(D.old, D.oldNeighborhood) :=
  ⟨Set.inclusion D.old_subset_neighborhood, continuous_inclusion _⟩

private def
    Smale.EmbeddedCellAttachment.outerParameterHomeomorph {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    Smale.OuterDisk.Space N ≃ₜ (D.cell ⁻¹' D.oldNeighborhood) :=
  Homeomorph.setCongr (by ext z; exact (D.cell_mem_oldNeighborhood_iff z).symm)

private def Smale.EmbeddedCellAttachment.outerInclusion {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    C(Smale.OuterDisk.Space N, D.oldNeighborhood) :=
  ⟨fun z => ⟨D.cell z.val, (D.cell_mem_oldNeighborhood_iff z.val).mpr z.property⟩,
    (D.cell.continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem
    Smale.EmbeddedCellAttachment.oldInclusion_closed {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    Topology.IsClosedEmbedding D.oldInclusion :=
  Smale.ClosedCover.isClosedEmbedding_codRestrict D.old_closed.isClosedEmbedding_subtypeVal
    (fun x => D.old_subset_neighborhood x.property)

private theorem
    Smale.EmbeddedCellAttachment.outerInclusion_closed {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    Topology.IsClosedEmbedding D.outerInclusion :=
  (D.oldNeighborhood.restrictPreimage_isClosedEmbedding D.cell_closed).comp
    D.outerParameterHomeomorph.isClosedEmbedding

private theorem
    Smale.EmbeddedCellAttachment.oldNeighborhood_cover {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    Set.range D.oldInclusion ∪ Set.range D.outerInclusion = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨x, hx⟩
  have hcover : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  rcases hcover with hA | ⟨z, rfl⟩
  · exact Or.inl ⟨⟨x, hA⟩, rfl⟩
  · exact Or.inr ⟨⟨z, (D.cell_mem_oldNeighborhood_iff z).mp hx⟩, rfl⟩

private theorem Smale.EmbeddedCellAttachment.sphere_attaches {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (u : Metric.sphere (0 : N) 1) :
    D.cell (Smale.OuterDisk.sphereDisk u) ∈ D.old :=
  (D.boundary _).mpr (mem_sphere_zero_iff_norm.mp u.property)

private def Smale.EmbeddedCellAttachment.attachingSphere {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    C(Metric.sphere (0 : N) 1, D.old) :=
  ⟨fun u => ⟨D.cell (Smale.OuterDisk.sphereDisk u), D.sphere_attaches u⟩,
    (D.cell.continuous.comp Smale.OuterDisk.sphereDisk.continuous).subtype_mk _⟩

private theorem
    Smale.EmbeddedCellAttachment.retractionMaps_agree {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) [NormedSpace ℝ N] (a : D.old)
    (z : Smale.OuterDisk.Space N) (haz : D.oldInclusion a = D.outerInclusion z) :
    a = D.attachingSphere (Smale.OuterDisk.toSphere z) := by
  have heq : (a : X) = D.cell z.val := congrArg Subtype.val haz
  have hnorm : ‖(z.val : N)‖ = 1 := (D.boundary z.val).mp (heq ▸ a.property)
  have hs : Smale.OuterDisk.sphereDisk (Smale.OuterDisk.toSphere z) = z.val :=
    congrArg Subtype.val (Smale.OuterDisk.fromSphere_toSphere_boundary z hnorm)
  apply Subtype.ext
  change (a : X) = D.cell (Smale.OuterDisk.sphereDisk (Smale.OuterDisk.toSphere z))
  rw [hs]
  exact heq

private def Smale.EmbeddedCellAttachment.oldRetraction {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) [NormedSpace ℝ N] :
    C(D.oldNeighborhood, D.old) :=
  Smale.ClosedCover.mapOfClosedPieces D.oldInclusion D.outerInclusion D.oldInclusion_closed
    D.outerInclusion_closed D.oldNeighborhood_cover (ContinuousMap.id D.old)
    (D.attachingSphere.comp Smale.OuterDisk.toSphere) D.retractionMaps_agree

private theorem Smale.EmbeddedCellAttachment.oldRetraction_old {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) [NormedSpace ℝ N] (a : D.old) :
    D.oldRetraction (D.oldInclusion a) = a :=
  Smale.ClosedCover.mapOfClosedPieces_left D.oldInclusion D.outerInclusion D.oldInclusion_closed
    D.outerInclusion_closed D.oldNeighborhood_cover (ContinuousMap.id D.old)
    (D.attachingSphere.comp Smale.OuterDisk.toSphere) D.retractionMaps_agree a

private theorem
    Smale.EmbeddedCellAttachment.oldRetraction_outer {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) [NormedSpace ℝ N]
    (z : Smale.OuterDisk.Space N) :
    D.oldRetraction (D.outerInclusion z) = D.attachingSphere (Smale.OuterDisk.toSphere z) :=
  Smale.ClosedCover.mapOfClosedPieces_right D.oldInclusion D.outerInclusion D.oldInclusion_closed
    D.outerInclusion_closed D.oldNeighborhood_cover (ContinuousMap.id D.old)
    (D.attachingSphere.comp Smale.OuterDisk.toSphere) D.retractionMaps_agree z

private theorem
    Smale.EmbeddedCellAttachment.neighborhood_time_cover {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    Set.range (Prod.map (id : (unitInterval) → (unitInterval)) D.oldInclusion) ∪
        Set.range (Prod.map (id : (unitInterval) → (unitInterval)) D.outerInclusion) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨t, x⟩
  have hx : x ∈ Set.range D.oldInclusion ∪ Set.range D.outerInclusion := by
    rw [D.oldNeighborhood_cover]
    trivial
  rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inl ⟨(t, a), rfl⟩
  · exact Or.inr ⟨(t, z), rfl⟩

private def Smale.EmbeddedCellAttachment.stationaryOld {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    C((unitInterval) × D.old, D.oldNeighborhood) :=
  D.oldInclusion.comp ContinuousMap.snd

private def Smale.EmbeddedCellAttachment.movingOuter {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    C((unitInterval) × Smale.OuterDisk.Space N, D.oldNeighborhood) :=
  D.outerInclusion.comp Smale.OuterDisk.deformation.toHomotopy.toContinuousMap

private theorem Smale.EmbeddedCellAttachment.neighborhoodMotions_agree {N X : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (a : (unitInterval) × D.old)
    (z : (unitInterval) × Smale.OuterDisk.Space N)
    (haz : Prod.map id D.oldInclusion a = Prod.map id D.outerInclusion z) :
    D.stationaryOld a = D.movingOuter z := by
  have ha : D.oldInclusion a.2 = D.outerInclusion z.2 := congrArg Prod.snd haz
  have heq : (a.2 : X) = D.cell z.2.val := congrArg Subtype.val ha
  have hn : ‖(z.2.val : N)‖ = 1 := (D.boundary z.2.val).mp (heq ▸ a.2.property)
  change D.oldInclusion a.2 = D.outerInclusion (Smale.OuterDisk.deformation (z.1, z.2))
  rw [Smale.OuterDisk.deformation.eq_fst z.1 hn]
  exact ha

private def Smale.EmbeddedCellAttachment.neighborhoodMotion {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    C((unitInterval) × D.oldNeighborhood, D.oldNeighborhood) :=
  Smale.ClosedCover.mapOfClosedPieces (Prod.map id D.oldInclusion) (Prod.map id D.outerInclusion)
    (Topology.IsClosedEmbedding.id.prodMap D.oldInclusion_closed)
    (Topology.IsClosedEmbedding.id.prodMap D.outerInclusion_closed) D.neighborhood_time_cover
    D.stationaryOld D.movingOuter D.neighborhoodMotions_agree

private theorem
    Smale.EmbeddedCellAttachment.neighborhoodMotion_old {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (t : (unitInterval)) (a : D.old) :
    D.neighborhoodMotion (t, D.oldInclusion a) = D.oldInclusion a :=
  Smale.ClosedCover.mapOfClosedPieces_left (Prod.map id D.oldInclusion)
    (Prod.map id D.outerInclusion) (Topology.IsClosedEmbedding.id.prodMap D.oldInclusion_closed)
    (Topology.IsClosedEmbedding.id.prodMap D.outerInclusion_closed) D.neighborhood_time_cover
    D.stationaryOld D.movingOuter D.neighborhoodMotions_agree (t, a)

private theorem
    Smale.EmbeddedCellAttachment.neighborhoodMotion_outer {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (t : (unitInterval)) (z : Smale.OuterDisk.Space N) :
    D.neighborhoodMotion (t, D.outerInclusion z) =
      D.outerInclusion (Smale.OuterDisk.deformation (t, z)) :=
  Smale.ClosedCover.mapOfClosedPieces_right (Prod.map id D.oldInclusion)
    (Prod.map id D.outerInclusion) (Topology.IsClosedEmbedding.id.prodMap D.oldInclusion_closed)
    (Topology.IsClosedEmbedding.id.prodMap D.outerInclusion_closed) D.neighborhood_time_cover
    D.stationaryOld D.movingOuter D.neighborhoodMotions_agree (t, z)

private def Smale.EmbeddedCellAttachment.oldDeformation {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    (ContinuousMap.id D.oldNeighborhood).HomotopyRel (D.oldInclusion.comp D.oldRetraction)
      (Set.range D.oldInclusion)
    where
  toFun := D.neighborhoodMotion
  continuous_toFun := D.neighborhoodMotion.continuous
  map_zero_left
    x := by
    have hx : x ∈ Set.range D.oldInclusion ∪ Set.range D.outerInclusion := by
      rw [D.oldNeighborhood_cover]
      trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · exact D.neighborhoodMotion_old 0 a
    · rw [D.neighborhoodMotion_outer]
      exact congrArg D.outerInclusion (Smale.OuterDisk.deformation.toHomotopy.map_zero_left z)
  map_one_left
    x := by
    change D.neighborhoodMotion (1, x) = D.oldInclusion (D.oldRetraction x)
    have hx : x ∈ Set.range D.oldInclusion ∪ Set.range D.outerInclusion := by
      rw [D.oldNeighborhood_cover]
      trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · rw [D.neighborhoodMotion_old, D.oldRetraction_old]
    · rw [D.neighborhoodMotion_outer, D.oldRetraction_outer]
      exact congrArg D.outerInclusion (Smale.OuterDisk.deformation.toHomotopy.map_one_left z)
  prop' t x
    hx := by
    obtain ⟨a, rfl⟩ := hx
    exact D.neighborhoodMotion_old t a

private def Smale.EmbeddedCellAttachment.oldHomotopyEquiv {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    D.old ≃ₕ D.oldNeighborhood where
  toFun := D.oldInclusion
  invFun := D.oldRetraction
  left_inv := by
    have heq : D.oldRetraction.comp D.oldInclusion = ContinuousMap.id D.old :=
      ContinuousMap.ext D.oldRetraction_old
    rw [heq]
  right_inv := ⟨D.oldDeformation.toHomotopy.symm⟩

private abbrev Smale.DiskAnnulus.OpenDisk (E : Type*) [NormedAddCommGroup E] :=
  { z : Smale.MorseHandle.UnitDisk E // ‖(z : E)‖ < 1 }

private abbrev Smale.DiskAnnulus.Annulus (E : Type*) [NormedAddCommGroup E] :=
  { z : Smale.MorseHandle.UnitDisk E // 1 / 2 < ‖(z : E)‖ ∧ ‖(z : E)‖ < 1 }

private theorem Smale.DiskAnnulus.norm_pos {E : Type*} [NormedAddCommGroup E] (z : Annulus E) :
    0 < ‖(z.val : E)‖ := by linarith [z.property.1]

private def Smale.DiskAnnulus.openDiskHomeomorph {E : Type*} [NormedAddCommGroup E] :
    OpenDisk E ≃ₜ Metric.ball (0 : E) 1
    where
  toFun z := ⟨z.val.val, mem_ball_zero_iff.mpr z.property⟩
  invFun
    z :=
    ⟨⟨z.val, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp z.property).le⟩,
      mem_ball_zero_iff.mp z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem Smale.DiskAnnulus.openDisk_contractible {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : ContractibleSpace (OpenDisk E) := by
  let : ContractibleSpace (Metric.ball (0 : E) 1) :=
    (convex_ball (0 : E) 1).contractibleSpace ⟨0, by simp⟩
  exact openDiskHomeomorph.contractibleSpace

private def Smale.DiskAnnulus.toSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(Annulus E, Metric.sphere (0 : E) 1) :=
  ⟨fun z => Smale.RadialExtension.direction (z.val : E) (norm_ne_zero_iff.mp (norm_pos z).ne'),
    (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
              (fun z => (norm_pos z).ne')).smul
          (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
      _⟩

private theorem Smale.DiskAnnulus.norm_middle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Metric.sphere (0 : E) 1) : ‖(3 / 4 : ℝ) • (u : E)‖ = 3 / 4 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

private def Smale.DiskAnnulus.middleDisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Metric.sphere (0 : E) 1) : Smale.MorseHandle.UnitDisk E :=
  ⟨(3 / 4 : ℝ) • (u : E), by
    rw [mem_closedBall_zero_iff, norm_middle]
    norm_num⟩

private theorem
    Smale.DiskAnnulus.middleDisk_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Metric.sphere (0 : E) 1) : 1 / 2 < ‖(middleDisk u : E)‖ ∧ ‖(middleDisk u : E)‖ < 1 := by
  change 1 / 2 < ‖(3 / 4 : ℝ) • (u : E)‖ ∧ ‖(3 / 4 : ℝ) • (u : E)‖ < 1
  rw [norm_middle]
  norm_num

private def Smale.DiskAnnulus.fromSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(Metric.sphere (0 : E) 1, Annulus E) :=
  ⟨fun u => ⟨middleDisk u, middleDisk_mem u⟩,
    ((continuous_const.smul continuous_subtype_val).subtype_mk _).subtype_mk _⟩

private theorem
    Smale.DiskAnnulus.toSphere_fromSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Metric.sphere (0 : E) 1) : toSphere (fromSphere u) = u := by
  apply Subtype.ext
  change ‖(3 / 4 : ℝ) • (u : E)‖⁻¹ • ((3 / 4 : ℝ) • (u : E)) = (u : E)
  rw [norm_middle, inv_smul_smul₀ (by norm_num : (3 / 4 : ℝ) ≠ 0)]

private def Smale.DiskAnnulus.blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : (unitInterval) × Annulus E) : E :=
  ((1 - (q.1 : ℝ)) + (q.1 : ℝ) * ((3 / 4 : ℝ) / ‖(q.2.val : E)‖)) • (q.2.val : E)

private theorem Smale.DiskAnnulus.continuous_blendVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Continuous (blendVector (E := E)) := by
  have ht : Continuous (fun q : (unitInterval) × Annulus E => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous (fun q : (unitInterval) × Annulus E => (q.2.val : E)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact
    ((continuous_const.sub ht).add
          (ht.mul (continuous_const.div hz.norm (fun q => (norm_pos q.2).ne')))).smul
      hz

private theorem
    Smale.DiskAnnulus.norm_blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : (unitInterval)) (z : Annulus E) :
    ‖blendVector (t, z)‖ = (1 - (t : ℝ)) * ‖(z.val : E)‖ + (t : ℝ) * (3 / 4) := by
  have hscale : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * ((3 / 4 : ℝ) / ‖(z.val : E)‖) :=
    add_nonneg (sub_nonneg.mpr t.property.2)
      (mul_nonneg t.property.1 (div_nonneg (by norm_num) (norm_pos z).le))
  rw [blendVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale, add_mul, mul_assoc,
    div_mul_cancel₀ _ (norm_pos z).ne']

private theorem Smale.DiskAnnulus.norm_blendVector_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (t : (unitInterval)) (z : Annulus E) :
    1 / 2 < ‖blendVector (t, z)‖ ∧ ‖blendVector (t, z)‖ < 1 := by
  rw [norm_blendVector]
  have h :=
    (convex_Ioo (𝕜 := ℝ) (1 / 2 : ℝ) 1) z.property (by norm_num : (3 / 4 : ℝ) ∈ Ioo (1 / 2) 1)
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
  exact h

private def Smale.DiskAnnulus.blend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : (unitInterval) × Annulus E) : Annulus E :=
  ⟨⟨blendVector q, mem_closedBall_zero_iff.mpr (norm_blendVector_mem q.1 q.2).2.le⟩,
    norm_blendVector_mem q.1 q.2⟩

private theorem
    Smale.DiskAnnulus.continuous_blend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (blend (E := E)) :=
  (continuous_blendVector.subtype_mk _).subtype_mk _

private def Smale.DiskAnnulus.deformation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (ContinuousMap.id (Annulus E)).Homotopy (fromSphere.comp toSphere)
    where
  toFun := blend
  continuous_toFun := continuous_blend
  map_zero_left
    z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector]
  map_one_left
    z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector, fromSphere, middleDisk, toSphere, Smale.RadialExtension.direction,
      div_eq_mul_inv, smul_smul]

private def
    Smale.DiskAnnulus.sphereHomotopyEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Metric.sphere (0 : E) 1 ≃ₕ Annulus E
    where
  toFun := fromSphere
  invFun := toSphere
  left_inv := by
    have heq : toSphere.comp fromSphere = ContinuousMap.id (Metric.sphere (0 : E) 1) :=
      ContinuousMap.ext toSphere_fromSphere
    rw [heq]
  right_inv := ⟨deformation.symm⟩

private theorem
    Smale.EmbeddedCellAttachment.diskPatch_contractible {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    ContractibleSpace D.diskPatch := by
  let : ContractibleSpace (Smale.DiskAnnulus.OpenDisk N) :=
    Smale.DiskAnnulus.openDisk_contractible
  exact D.diskHomeomorph.symm.contractibleSpace

private def Smale.EmbeddedCellAttachment.overlapSphereEquiv {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    Metric.sphere (0 : N) 1 ≃ₕ ↥(D.oldNeighborhood ∩ D.diskPatch) :=
  Smale.DiskAnnulus.sphereHomotopyEquiv.trans D.overlapHomeomorph.toHomotopyEquiv

private def Smale.EmbeddedCellAttachment.overlapOldMap {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    C(↥(D.oldNeighborhood ∩ D.diskPatch), D.old) :=
  D.oldRetraction.comp (ContinuousMap.inclusion Set.inter_subset_left)

private theorem
    Smale.EmbeddedCellAttachment.overlapOldMap_sphere {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (u : Metric.sphere (0 : N) 1) :
    D.overlapOldMap (D.overlapSphereEquiv u) = D.attachingSphere u := by
  let z : Smale.OuterDisk.Space N :=
    ⟨(Smale.DiskAnnulus.fromSphere u).val, (Smale.DiskAnnulus.fromSphere u).property.1⟩
  change D.oldRetraction (D.outerInclusion z) = D.attachingSphere u
  rw [D.oldRetraction_outer]
  apply congrArg D.attachingSphere
  exact Smale.DiskAnnulus.toSphere_fromSphere u

private theorem Smale.EmbeddedCellAttachment.overlapOldMap_comp_sphere {N X : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) :
    D.overlapOldMap.comp D.overlapSphereEquiv.toFun = D.attachingSphere :=
  ContinuousMap.ext D.overlapOldMap_sphere

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.coreCellPresentation {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    Smale.EmbeddedCellAttachment d.chart.NegativeCoordinates
      ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
  Smale.EmbeddedCellAttachment.ofUnion _ d.coreMap (isClosed_le hf continuous_const)
    d.coreMap_isClosedEmbedding d.coreMap_lower_iff

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.cellOldHomeomorph {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    { y : M // f y ≤ f p - d.radius ^ 2 } ≃ₜ (d.coreCellPresentation hf).old
    where
  toFun x := ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.coreBoundaryMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.NegativeCoordinates) 1, { y : M // f y ≤ f p - d.radius ^ 2 }) :=
  (⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩ :
        C(d.LowerLevel, { y : M // f y ≤ f p - d.radius ^ 2 })).comp
    d.surgery.attachingSphere

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.coreCell_attaching_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    (d.coreCellPresentation hf).attachingSphere =
      (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun.comp d.coreBoundaryMap := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  exact d.coreMap_boundary u

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.realizedLowerInclusion {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C({ y : M // f y ≤ f p - d.radius ^ 2 }, { y : M // f y ≤ f p + d.radius ^ 2 }) :=
  ⟨fun x => d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩,
    d.attachmentHomeomorph.continuous.comp (continuous_inclusion (fun _ hx => Or.inl hx))⟩

private theorem
    AdaptedWindows.forward_limit_below_regular_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ x, f x = a → x ∉ Smale.ManifoldMorse.criticalPoints E f) (x : { y : M // f y = a })
    {p : M} (hlim : Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p)) : f p < a := by
  obtain ⟨r, hr, q, hq, -, hqLim, hheight⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct (x : M)
  have hqp : q = p := tendsto_nhds_unique hqLim hlim
  have hh := (hheight (hreg x x.property)).1
  simpa only [hqp, x.property] using hh

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.place_one_handle_in_distinct_minimum_basins {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hone : MorseCancel.nativeMorseIndex E f q = 1)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v)) :
    letI := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ d :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        (S.data q).LowerLevel (S.data q).LowerLevel ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧
        ∃ p r : Smale.ManifoldMorse.criticalPoints E f,
          MorseCancel.nativeMorseIndex E f p = 0 ∧
            MorseCancel.nativeMorseIndex E f r = 0 ∧
              p ≠ r ∧
                f p < S.toSurgeryWindows.lower q ∧
                  f r < S.toSurgeryWindows.lower q ∧
                    Filter.Tendsto
                        (fun t => S.flow t (d ((S.data q).surgery.attachingSphere u)).val)
                        Filter.atTop (𝓝 p.val) ∧
                      Filter.Tendsto
                          (fun t => S.flow t (d ((S.data q).surgery.attachingSphere v)).val)
                          Filter.atTop (𝓝 r.val) ∧
                        ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
                          Filter.Tendsto
                              (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
                              Filter.atTop (𝓝 p.val) ∨
                            Filter.Tendsto
                              (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
                              Filter.atTop (𝓝 r.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data q).lower_regular
  let ι : C((S.data q).LowerLevel, { z : M // f z ≤ S.toSurgeryWindows.lower q }) :=
    ⟨fun x => ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩
  let α := (S.data q).surgery.attachingSphere
  have hxy : α u ≠ α v := by
    intro h
    have hh : (S.data q).coreBoundaryMap u = (S.data q).coreBoundaryMap v := congrArg ι h
    exact hnot (hh ▸ Joined.refl _)
  obtain ⟨d, hd, ⟨p, hp, hpu⟩, ⟨r, hr, hrv⟩⟩ :=
    MorseCancel.exists_isotopic_two_points_in_dense (J := 𝓘(ℝ, Smale.RegularLevel.Model E))
      (S.dense_regular_level_minimum_basins hf (S.data q).lower_regular) hxy
  have hpq := S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α u)) hpu
  have hrq := S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α v)) hrv
  have hpr : p ≠ r := by
    intro h
    subst r
    let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
    have hnew : Joined (ι (d (α u))) (ι (d (α v))) :=
      MorseCancel.joined_sublevel_of_common_forward_limit S.flow hf.continuous
        (Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent)
        (ι (d (α u))) (ι (d (α v))) hpq hpu hrv
    exact
      hnot
        (((MorseCancel.isotopicToIdentity_joined hd (α u)).map ι.continuous).trans
          (hnew.trans ((MorseCancel.isotopicToIdentity_joined hd (α v)).map ι.continuous).symm))
  refine ⟨d, hd, p, r, hp, hr, hpr, hpq, hrq, hpu, hrv, ?_⟩
  intro w
  have hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  have huv : u ≠ v := fun h => hxy (congrArg α h)
  rcases MorseCancel.unitSphere_eq_two_points_of_finrank_one hindex u v huv w with h | h
  · subst w
    exact Or.inl hpu
  · subst w
    exact Or.inr hrv

private theorem MorseCancel.fderiv_beltPassage_upper_fst {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s w : ℝ) (u : N) (v : P) :
    (fderiv ℝ (fun t => Degree.BeltPassage.upper ρ t u v) s w).1 = (ρ * w) • u := by
  have hfirst : HasDerivAt (fun t : ℝ => (Degree.BeltPassage.upper ρ t u v).1) (ρ • u) s := by
    simpa only [Degree.BeltPassage.upper, id_eq, mul_one] using
      ((hasDerivAt_id s).const_mul ρ).smul_const u
  have hchain :
    fderiv ℝ (fun t => (Degree.BeltPassage.upper ρ t u v).1) s =
      (ContinuousLinearMap.fst ℝ N P).comp
        (fderiv ℝ (fun t => Degree.BeltPassage.upper ρ t u v) s) := by
    have hh :=
      fderiv_comp s (ContinuousLinearMap.fst ℝ N P).differentiableAt
        ((Degree.BeltPassage.contDiff_upper ρ u v).differentiable (by simp) s)
    rw [(ContinuousLinearMap.fst ℝ N P).fderiv] at hh
    exact hh
  have hh := congrArg (fun L : ℝ →L[ℝ] N => L w) hchain
  rw [hfirst.hasFDerivAt.fderiv] at hh
  change w • (ρ • u) = (fderiv ℝ (fun t => Degree.BeltPassage.upper ρ t u v) s w).1 at hh
  rw [smul_smul, mul_comm w ρ] at hh
  exact hh.symm

private theorem MorseCancel.injective_fderiv_beltPassage_upper {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : ρ ≠ 0) (s : ℝ)
    {u : N} (hu : u ≠ 0) (v : P) :
    Function.Injective (fderiv ℝ (fun t => Degree.BeltPassage.upper ρ t u v) s) := by
  intro a b hab
  have hh := congrArg Prod.fst hab
  rw [fderiv_beltPassage_upper_fst, fderiv_beltPassage_upper_fst] at hh
  exact mul_left_cancel₀ hρ (smul_left_injective ℝ hu hh)

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.nativeBeltArc_derivative_injective {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (nativeBeltArc S q u v) s) := by
  have ht := nativeBeltArc_coordinates_mem_target S q u v hs
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  change
    Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        ((S.data q).chart.splitChart.symm ∘
          (fun t => Degree.BeltPassage.upper (S.data q).radius t u.val v.val))
        s)
  rw [mfderiv_comp s ((S.data q).chart.splitChart.symm.mdifferentiableAt (by simp) ht)
      ((Degree.BeltPassage.contDiff_upper (S.data q).radius u.val
            v.val).contMDiff.mdifferentiableAt
        (by simp)),
    mfderiv_eq_fderiv]
  exact
    (Smale.PartialChart.bijective_mfderiv (S.data q).chart.splitChart.symm ht).injective.comp
      (injective_fderiv_beltPassage_upper (S.data q).radius_pos.ne' s hu v.val)

private theorem
    Smale.RegularLevel.contMDiffWithinAt_iff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) (S : Set X) (x : X) :
    letI := chartedSpace hf hreg
    ContMDiffWithinAt I 𝓘(ℝ, Model E) ∞ g S x ↔
      ContMDiffWithinAt I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) S x := by
  let _ := chartedSpace hf hreg
  constructor
  · intro hg
    exact (Smale.RegularLevel.contMDiff_inclusion hf hreg).contMDiffAt.comp_contMDiffWithinAt x hg
  · intro hg
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr hg.continuousWithinAt, ?_⟩
    let Φ := heightChart hf hreg (g x)
    have hΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) ∞ Φ (g x) :=
      Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (heightChart_mem_source hf hreg (g x)))
    have hcomp := hΦ.comp_contMDiffWithinAt x hg
    change ContMDiffWithinAt I 𝓘(ℝ, Model E) ∞ (fun y => (Φ (g y)).2) S x
    exact contDiff_snd.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hcomp

private theorem Smale.RegularLevel.contMDiffOn_iff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) (S : Set X) :
    letI := chartedSpace hf hreg
    ContMDiffOn I 𝓘(ℝ, Model E) ∞ g S ↔ ContMDiffOn I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) S := by
  let _ := chartedSpace hf hreg
  exact
    forall_congr'
      (fun x => forall_congr' (fun _ => contMDiffWithinAt_iff_inclusion hf hreg I g S x))

attribute [local instance 100] Classical.propDecidable in
private def MorseCancel.nativeBeltLevelArc {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : ℝ) :
    (S.data q).UpperLevel :=
  if hs : |s| ≤ 1 then ⟨nativeBeltArc S q u v s, nativeBeltArc_height S q u v hs⟩
  else (S.data q).surgery.beltSphere v

private theorem
    MorseCancel.nativeBeltLevelArc_coe {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    (nativeBeltLevelArc S q u v s).val = nativeBeltArc S q u v s := by
  simp only [nativeBeltLevelArc, dite_eq_left hs]

private theorem MorseCancel.nativeBeltLevelArc_coe_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    (Subtype.val ∘ nativeBeltLevelArc S q u v) =ᶠ[𝓝 s] nativeBeltArc S q u v := by
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  exact nativeBeltLevelArc_coe S q u v (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)

private theorem MorseCancel.nativeBeltLevelArc_contMDiffOn {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} [FiniteDimensional ℝ E] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (nativeBeltLevelArc S q u v)
      (Set.Ioo (-1 : ℝ) 1) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  apply
    (Smale.RegularLevel.contMDiffOn_iff_inclusion hf (S.data q).upper_regular 𝓘(ℝ, ℝ)
        (nativeBeltLevelArc S q u v) (Set.Ioo (-1 : ℝ) 1)).mpr
  apply (nativeBeltArc_contMDiffOn S q u v).congr
  intro s hs
  exact nativeBeltLevelArc_coe S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

private theorem
    MorseCancel.nativeBeltLevelArc_derivative_injective {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} [FiniteDimensional ℝ E] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Smale.RegularLevel.Model E) (nativeBeltLevelArc S q u v) s) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  have hg := nativeBeltLevelArc_coe_germ S q u v hs
  apply
    Smale.RegularLevel.injective_mfderiv_of_inclusion hf (S.data q).upper_regular 𝓘(ℝ, ℝ)
      (nativeBeltLevelArc S q u v) s
  · exact
      ((nativeBeltArc_contMDiffOn S q u v).contMDiffAt
            (Ioo_mem_nhds hs.1 hs.2)).congr_of_eventuallyEq
        hg
  · rw [hg.mfderiv_eq]
    exact nativeBeltArc_derivative_injective S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.nativeBeltLevelArc_normal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    (S.data q).beltNormal (nativeBeltLevelArc S q u v s) = ((S.data q).radius * s) • u.val := by
  change ((S.data q).chart.splitChart (nativeBeltLevelArc S q u v s).val).1 = _
  rw [nativeBeltLevelArc_coe S q u v hs]
  exact
    congrArg Prod.fst
      ((S.data q).chart.splitChart.right_inv' (nativeBeltArc_coordinates_mem_target S q u v hs))

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.nativeBeltLevelArc_transverse {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (hq : nativeMorseIndex E f q = 1) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    Function.Surjective
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Smale.RegularLevel.Model E) (nativeBeltLevelArc S q u v) 0 :
            ℝ →L[ℝ] Smale.RegularLevel.Model E).coprod
        (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) (S.data q).surgery.beltSphere v)) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let d := S.data q
  let γ := nativeBeltLevelArc S q u v
  let L : ℝ →L[ℝ] d.chart.NegativeCoordinates :=
    ContinuousLinearMap.toSpanSingleton ℝ (d.radius • u.val)
  have hpoint : γ 0 = d.surgery.beltSphere v :=
    Subtype.ext
      ((nativeBeltLevelArc_coe S q u v (s := 0) (by simp)).trans (nativeBeltArc_zero S q u v))
  have hgerm : d.beltNormal ∘ γ =ᶠ[𝓝 (0 : ℝ)] L := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < 1 by norm_num)] with
      s hs
    change d.beltNormal (nativeBeltLevelArc S q u v s) = s • (d.radius • u.val)
    rw [nativeBeltLevelArc_normal S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩), smul_smul,
      mul_comm s d.radius]
  have hnormalDerivative :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ γ) 0 = L := by
    rw [hgerm.mfderiv_eq, mfderiv_eq_fderiv, L.fderiv]
  have hγ :=
    (nativeBeltLevelArc_contMDiffOn S hf q u v).contMDiffAt
      (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))
  have hnormal :=
    (d.contMDiffOn_beltNormal hf).contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  let A : ℝ →L[ℝ] Smale.RegularLevel.Model E :=
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Smale.RegularLevel.Model E) γ 0
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] Smale.RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) d.surgery.beltSphere v
  let Q : Smale.RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
      (d.surgery.beltSphere v)
  have hnγ :
    MDifferentiableAt 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
      d.beltNormal (γ 0) := by
    rw [hpoint]
    exact hnormal.mdifferentiableAt (by simp)
  have hQA : Q.comp A = L := by
    have hh := mfderiv_comp 0 hnγ (hγ.mdifferentiableAt (by simp))
    rw [hpoint] at hh
    exact hh.symm.trans hnormalDerivative
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hLi : Function.Injective L := smul_left_injective ℝ (smul_ne_zero d.radius_pos.ne' hu)
  have hdim : Module.finrank ℝ ℝ = Module.finrank ℝ d.chart.NegativeCoordinates := by
    rw [Module.finrank_self]
    exact ((nativeMorseIndex_eq_chart d.chart).symm.trans hq).symm
  have hLs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) hdim).mp hLi
  have hQAs : Function.Surjective (Q.comp A) := hQA.symm ▸ hLs
  have hker : B.range = Q.ker := d.range_belt_derivative_eq_normal_kernel hf n v
  change Function.Surjective (A.coprod B)
  intro z
  obtain ⟨s, hs⟩ := hQAs (Q z)
  have hmem : z - A s ∈ Q.ker := by
    change Q (z - A s) = 0
    change Q (A s) = Q z at hs
    rw [map_sub, hs, sub_self]
  rw [← hker] at hmem
  obtain ⟨w, hw⟩ := hmem
  change B w = z - A s at hw
  refine ⟨(s, w), ?_⟩
  change A s + B w = z
  rw [hw]
  abel

private theorem MorseCancel.transverse_circle_of_arc_germ {D G H N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] {α : ℝ → N}
    {γ : Circle → N} {ψ : ℝ → Circle} (hγ : ContMDiff (𝓡 1) J ∞ γ)
    (hψ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ψ) (hgerm : γ ∘ ψ =ᶠ[𝓝 (0 : ℝ)] α) (B : D →L[ℝ] G)
    (htrans : Function.Surjective ((mfderiv 𝓘(ℝ, ℝ) J α 0 : ℝ →L[ℝ] G).coprod B)) :
    Function.Surjective ((mfderiv (𝓡 1) J γ (ψ 0) : EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod B) :=
  by
  let A : EuclideanSpace ℝ (Fin 1) →L[ℝ] G := mfderiv (𝓡 1) J γ (ψ 0)
  let P : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) ψ 0
  let A₀ : ℝ →L[ℝ] G := mfderiv 𝓘(ℝ, ℝ) J α 0
  have hc := mfderiv_comp 0 (hγ.mdifferentiableAt (by simp)) (hψ.mdifferentiableAt (by simp))
  have heq : A.comp P = A₀ := hc.symm.trans hgerm.mfderiv_eq
  intro y
  obtain ⟨⟨a, b⟩, hab⟩ := htrans y
  refine ⟨(P a, b), ?_⟩
  have ha := congrArg (fun L : ℝ →L[ℝ] G => L a) heq
  change A (P a) + B b = y
  change A (P a) = A₀ a at ha
  rw [ha]
  exact hab

private theorem MorseCancel.surjective_coprod_comp_left {A A' B G : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup A'] [NormedSpace ℝ A'] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : A →L[ℝ] G) (R : B →L[ℝ] G)
    (P : A' →L[ℝ] A) (hP : Function.Surjective P) (htrans : Function.Surjective (L.coprod R)) :
    Function.Surjective ((L.comp P).coprod R) := by
  intro y
  obtain ⟨⟨a, b⟩, hab⟩ := htrans y
  obtain ⟨a', ha⟩ := hP a
  refine ⟨(a', b), ?_⟩
  change L (P a') + R b = y
  rw [ha]
  exact hab

private def MorseCancel.euclideanTail (n : ℕ) :
    Smale.Hemisphere.Ambient (n + 1) →L[ℝ] Smale.Hemisphere.Ambient n :=
  ({    toFun := fun x => WithLp.toLp 2 (fun i : Fin n => x i.succ)
        map_add' := by intro x y; ext i; rfl
        map_smul' := by intro a x; ext i; rfl } :
      Smale.Hemisphere.Ambient (n + 1) →ₗ[ℝ] Smale.Hemisphere.Ambient n).toContinuousLinearMap

private theorem
    MorseCancel.euclideanTail_hemisphere {n : ℕ} (b : Bool) (x : Smale.Hemisphere.Ball n) :
    euclideanTail n (Smale.Hemisphere.point b x).val = x.val := by
  ext i
  rfl

private theorem MorseCancel.exists_belt_point_avoiding_smooth_image {E M D H Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace Y]
    [ChartedSpace H Y] [IsManifold I ∞ Y] [LindelofSpace Y] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] (g : Y → M)
    (hg : ContMDiff I 𝓘(ℝ, E) ∞ g) (hdim : Module.finrank ℝ D < n) :
    ∃ v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1,
      (d.surgery.beltSphere v).val ∉ Set.range g := by
  let b :=
    (stdOrthonormalBasis ℝ d.chart.PositiveCoordinates).reindex
      (finCongr (Fact.out : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1))
  let L : d.chart.PositiveCoordinates ≃ₗᵢ[ℝ] Smale.Hemisphere.Ambient (n + 1) := b.repr
  let P : M → Smale.Hemisphere.Ambient n := fun x =>
    euclideanTail n (d.radius⁻¹ • L (d.chart.splitChart x).2)
  let U : Set Y := g ⁻¹' d.chart.splitChart.source
  have hU : IsOpen U := d.chart.splitChart.open_source.preimage hg.continuous
  have hPg : ContMDiffOn I 𝓘(ℝ, Smale.Hemisphere.Ambient n) ∞ (P ∘ g) U := by
    have hc :
      ContMDiffOn I 𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
        (d.chart.splitChart ∘ g) U :=
      d.chart.splitChart.contMDiffOn_toFun.comp hg.contMDiffOn (fun _ hy => hy)
    let A :
      d.chart.NegativeCoordinates × d.chart.PositiveCoordinates →L[ℝ]
        Smale.Hemisphere.Ambient n :=
      (euclideanTail n).comp
        ((d.radius⁻¹ • L.toContinuousLinearEquiv.toContinuousLinearMap).comp
          (ContinuousLinearMap.snd ℝ d.chart.NegativeCoordinates d.chart.PositiveCoordinates))
    have hQ :
      ContDiff ℝ ∞
        (fun z : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates =>
          euclideanTail n (d.radius⁻¹ • L z.2)) :=
      A.contDiff
    exact hQ.contMDiff.comp_contMDiffOn hc
  have hdense :=
    Smale.GeneralPosition.dense_compl_manifold_image hU hPg
      (show Module.finrank ℝ D < Module.finrank ℝ (Smale.Hemisphere.Ambient n) by
        simpa only [Smale.Hemisphere.Ambient, finrank_euclideanSpace_fin] using hdim)
  obtain ⟨x, hxavoid, hxnorm⟩ := hdense.exists_dist_lt 0 (show (0 : ℝ) < 1 by norm_num)
  have hx : ‖x‖ < 1 := by simpa only [dist_zero_left] using hxnorm
  let xB : Smale.Hemisphere.Ball n := ⟨x, mem_closedBall_zero_iff.mpr hx.le⟩
  let w := Smale.Hemisphere.point Bool.true xB
  let v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1 :=
    ⟨L.symm w.val, by
      rw [mem_sphere_zero_iff_norm, L.symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp w.property⟩
  have hcoord : d.chart.splitChart (d.surgery.beltSphere v).val = (0, d.radius • v.val) := by
    rw [d.belt_eq, d.chart.beltCoreMap_coe]
    exact d.chart.splitChart.right_inv' (d.belt_model_mem_target v)
  have hproject : P (d.surgery.beltSphere v).val = x := by
    change
      euclideanTail n (d.radius⁻¹ • L (d.chart.splitChart (d.surgery.beltSphere v).val).2) = x
    rw [hcoord]
    change euclideanTail n (d.radius⁻¹ • L (d.radius • (L.symm w.val))) = x
    rw [L.map_smul, L.apply_symm_apply, smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul]
    exact euclideanTail_hemisphere Bool.true xB
  refine ⟨v, ?_⟩
  rintro ⟨y, hy⟩
  apply hxavoid
  refine ⟨y, ?_, ?_⟩
  · change g y ∈ d.chart.splitChart.source
    rw [hy]
    exact d.belt_mem_normalDomain v
  · change P (g y) = x
    rw [hy]
    exact hproject

private theorem AdaptedWindows.exists_belt_point_reaching_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : Smale.ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)] {a : ℝ} (hqa : f q < a)
    {d : ℕ}
    (hlow :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancel.nativeMorseIndex E f p ≤ d)
    (hdim : d < n) :
    ∃ v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
      ((S.data q).surgery.beltSphere v).val ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let K := MorseCancel.LowBackwardBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := MorseCancel.lowBackwardBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_low_backward_obstruction_images hf a hlow
  let G : K × V → M := fun z => g z.1 z.2
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ G :=
    MorseCancel.contMDiff_discrete_family g hg
  have hrange : Set.range G = MorseCancel.backwardLowBasins S a := by
    rw [hcover]
    exact MorseCancel.range_discrete_family g
  obtain ⟨v, hv⟩ :=
    MorseCancel.exists_belt_point_avoiding_smooth_image (S.data q) n G hG
      (show Module.finrank ℝ (Z × V) < n by
        simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim)
  have hforward := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere v)).mpr ⟨v, rfl⟩
  obtain ⟨p, hp, _, _, hback, _, _⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct ((S.data q).surgery.beltSphere v).val
  have hap : a < f p :=
    lt_of_not_ge
      (fun h =>
        hv
          (hrange.symm ▸
            (show ((S.data q).surgery.beltSphere v).val ∈ MorseCancel.backwardLowBasins S a from
              ⟨⟨p, hp⟩, h, hback⟩)))
  exact
    ⟨v,
      Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
        hforward hap hqa⟩

private theorem AdaptedWindows.joinedIn_level_minimum_basin_reaching_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancel.nativeMorseIndex E f p = 0)
    {a b : ℝ} (hpb : f p < b) (hba : b ≤ a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hlow :
      ∀ q : Smale.ManifoldMorse.criticalPoints E f,
        f q ≤ a → MorseCancel.nativeMorseIndex E f q ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) {x y : M} (hxb : f x = b) (hyb : f y = b)
    (hx : Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val))
    (hy : Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p.val))
    (hxa : x ∈ Degree.FlowCancellation.levelBasin S.flow f a)
    (hya : y ∈ Degree.FlowCancellation.levelBasin S.flow f a) :
    JoinedIn
      {z : M |
        f z = b ∧
          Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val) ∧
            z ∈ Degree.FlowCancellation.levelBasin S.flow f a}
      x y := by
  let _ := S.finite.fintype
  let K := MorseCancel.LowBackwardBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := MorseCancel.lowBackwardBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_low_backward_obstruction_images hf a hlow
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun z : K × V => g z.1 z.2) :=
    MorseCancel.contMDiff_discrete_family g hg
  let G : C(K × V, M) := ⟨fun z => g z.1 z.2, hG.continuous⟩
  have hrange : Set.range G = MorseCancel.backwardLowBasins S a := by
    rw [hcover]
    exact MorseCancel.range_discrete_family g
  have hclosed : IsClosed (Set.range G) := by
    rw [hrange]
    exact MorseCancel.isClosed_backwardLowBasins S hf a
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : M) (hz : z ∈ Degree.FlowCancellation.levelBasin S.flow f a) : z ∉ Set.range G := by
    rw [hrange]
    intro hlowz
    have hc : z ∈ (Degree.FlowCancellation.levelBasin S.flow f a)ᶜ := by
      rw [MorseCancel.levelBasin_compl_eq_endpoint_obstruction S hf ha]
      exact Or.inr hlowz
    exact hc hz
  let U : TopologicalSpace.Opens M :=
    ⟨{z | Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val)},
      S.isOpen_minimum_forward_basin hf p hp⟩
  let xU : U := ⟨x, hx⟩
  let yU : U := ⟨y, hy⟩
  have hjoined : Joined xU yU := (S.joinedIn_minimum_basin hf p hp hx hy).joined_subtype
  obtain ⟨η, -, havoid⟩ :=
    MorseCancel.exists_smooth_path_avoiding_closed_image_in_open U hjoined.somePath G hG hclosed
      hdim' (hnot x hxa) (hnot y hya)
  have hcross (c : ℝ) (hbc : b ≤ c) (hca : c ≤ a) (u : unitInterval) :
    (η u).val ∈ Degree.FlowCancellation.levelBasin S.flow f c := by
    obtain ⟨q, hq, _, _, hback, _, _⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct (η u).val
    have hqa : a < f q :=
      lt_of_not_ge
        (fun h =>
          havoid u
            (hrange.symm ▸
              (show (η u).val ∈ MorseCancel.backwardLowBasins S a from ⟨⟨q, hq⟩, h, hback⟩)))
    exact
      Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
        (η u).property (hca.trans_lt hqa) (hpb.trans_le hbc)
  let _ := Smale.RegularLevel.chartedSpace hf hb
  let xL : { z : M // f z = b } := ⟨x, hxb⟩
  let yL : { z : M // f z = b } := ⟨y, hyb⟩
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ :=
    Degree.FlowCancellation.exists_native_level_flow_cylinder hf hb S.smooth S.flow S.integral
      (fun z hz => S.descent z (hb z hz)) xL
  have hcont : Continuous (fun u : unitInterval => Φ.symm (η u).val) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous (continuous_subtype_val.comp η.continuous)
      (fun u => htarget.symm ▸ hcross b le_rfl hba u)
  have hlevelInverse (z : { w : M // f w = b }) : Φ.symm z.val = (z, 0) := by
    have hs : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hs
    rwa [he] at hi
  let γ : Path x y :=
    { toFun := fun u => (Φ.symm (η u).val).1.val
      continuous_toFun := continuous_subtype_val.comp (continuous_fst.comp hcont)
      source' := by
        rw [η.source]
        exact congrArg (fun z : { w : M // f w = b } × ℝ => z.1.val) (hlevelInverse xL)
      target' := by
        rw [η.target]
        exact congrArg (fun z : { w : M // f w = b } × ℝ => z.1.val) (hlevelInverse yL) }
  refine ⟨γ, fun u => ⟨(Φ.symm (η u).val).1.property, ?_, ?_⟩⟩
  · let z := Φ.symm (η u).val
    have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross b le_rfl hba u)
    have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
    have hlim : Filter.Tendsto (fun t => S.flow t (S.flow z.2 z.1.val)) Filter.atTop (𝓝 p.val) :=
      hflow.symm ▸ (η u).property
    exact (MorseCancel.flow_time_atTop_limit_iff S.flow z.2 z.1.val p.val).mp hlim
  · let z := Φ.symm (η u).val
    have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross b le_rfl hba u)
    have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
    exact
      (Degree.FlowCancellation.levelBasin_flow_iff S.flow f a z.2 z.1.val).mp
        (hflow.symm ▸ hcross a hba le_rfl u)

private theorem AdaptedWindows.exists_belt_arc_closing_path_reaching_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancel.nativeMorseIndex E f p = 0)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val))
    {a : ℝ} (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hv : ((S.data q).surgery.beltSphere v).val ∈ Degree.FlowCancellation.levelBasin S.flow f a)
    {d : ℕ}
    (hlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        f z ≤ a → MorseCancel.nativeMorseIndex E f z ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) :
    ∃ r : ℝ,
      0 < r ∧
        r < 1 ∧
          (∀ s : ℝ,
              |s| ≤ r →
                MorseCancel.nativeBeltArc S q u v s ∈
                  Degree.FlowCancellation.levelBasin S.flow f a) ∧
            (∀ s : ℝ,
                0 < |s| →
                  |s| ≤ r →
                    Filter.Tendsto (fun t => S.flow t (MorseCancel.nativeBeltArc S q u v s))
                      Filter.atTop (𝓝 p.val)) ∧
              JoinedIn
                {z : M |
                  f z = S.toSurgeryWindows.upper q ∧
                    Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val) ∧
                      z ∈ Degree.FlowCancellation.levelBasin S.flow f a}
                (MorseCancel.nativeBeltArc S q u v r) (MorseCancel.nativeBeltArc S q u v (-r)) := by
  obtain ⟨ε, hε, hε1, hmin⟩ :=
    S.exists_two_sided_belt_branch_in_minimum_basin hf p q hp u v hbranches
  have hB : IsOpen (Degree.FlowCancellation.levelBasin S.flow f a) :=
    (Degree.FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (ha z hz))).1
  have hα0 :
    MorseCancel.nativeBeltArc S q u v 0 ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
    rw [MorseCancel.nativeBeltArc_zero]
    exact hv
  have hc : ContinuousAt (MorseCancel.nativeBeltArc S q u v) 0 :=
    ((MorseCancel.nativeBeltArc_contMDiffOn S q u v).contMDiffAt
        (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
          (show (0 : ℝ) < 1 by norm_num))).continuousAt
  have hnear :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      MorseCancel.nativeBeltArc S q u v s ∈ Degree.FlowCancellation.levelBasin S.flow f a :=
    hc.preimage_mem_nhds (hB.mem_nhds hα0)
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hnear
  let r := Min.min (ε / 2) (δ / 2)
  have hr : 0 < r := lt_min (half_pos hε) (half_pos hδ)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrδ : r < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hr1 : r < 1 := hrε.trans_le hε1
  have hreach (s : ℝ) (hs : |s| ≤ r) :
    MorseCancel.nativeBeltArc S q u v s ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hs.trans_lt hrδ
  have hall (s : ℝ) (hs : 0 < |s|) (hsr : |s| ≤ r) :
    Filter.Tendsto (fun t => S.flow t (MorseCancel.nativeBeltArc S q u v s)) Filter.atTop
      (𝓝 p.val) :=
    hmin s hs (hsr.trans_lt hrε)
  have hpb : f p < S.toSurgeryWindows.upper q :=
    (S.forward_limit_below_regular_level hf (S.data q).lower_regular
          ((S.data q).surgery.attachingSphere u) (hbranches u)).trans
      ((S.toSurgeryWindows.lower_lt_value q).trans (S.toSurgeryWindows.value_lt_upper q))
  have hpr : |r| = r := abs_of_pos hr
  have hmr : |-r| = r := by rw [abs_neg, hpr]
  refine ⟨r, hr, hr1, hreach, hall, ?_⟩
  exact
    S.joinedIn_level_minimum_basin_reaching_level hf p hp hpb hba ha (S.data q).upper_regular hlow
      hdim (MorseCancel.nativeBeltArc_height S q u v (by rw [hpr]; exact hr1.le))
      (MorseCancel.nativeBeltArc_height S q u v (by rw [hmr]; exact hr1.le))
      (hall r (hpr.symm ▸ hr) hpr.le) (hall (-r) (hmr.symm ▸ hr) hmr.le) (hreach r hpr.le)
      (hreach (-r) hmr.le)

private theorem MorseCancel.single_belt_intersection_of_arc_and_minimum_range {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {X : Type*}
    {γ : X → (S.data q).UpperLevel} (hγi : Function.Injective γ) {z₀ : X}
    (hzero : γ z₀ = (S.data q).surgery.beltSphere v) {r : ℝ} (hr1 : r ≤ 1)
    (himage :
      ∀ z,
        γ z ∈ nativeBeltLevelArc S q u v '' Set.Icc (-r) r ∨
          Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val)) :
    ∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w := by
  intro z w
  constructor
  · intro hzw
    rcases himage z with hshort | hmin
    · obtain ⟨s, hs, hsz⟩ := hshort
      have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hsw : nativeBeltArc S q u v s = ((S.data q).surgery.beltSphere w).val := by
        rw [← nativeBeltLevelArc_coe S q u v hs1]
        exact congrArg Subtype.val (hsz.trans hzw)
      obtain ⟨-, hvw⟩ := (nativeBeltArc_belt_eq_iff S q u v w hs1).mp hsw
      refine ⟨hγi ?_, hvw⟩
      exact hzw.trans ((congrArg (S.data q).surgery.beltSphere hvw).symm.trans hzero.symm)
    · have hqz := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩
      rw [hzw] at hmin
      exact False.elim (hpq (Subtype.ext (tendsto_nhds_unique hmin hqz)))
  · rintro ⟨rfl, rfl⟩
    exact hzero

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.exists_single_belt_circle_in_open_with_image {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancel.nativeMorseIndex E f p = 0)
    (hpq : p ≠ q) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (O : TopologicalSpace.Opens M) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hshortO : ∀ s ∈ Set.Icc (-r) r, MorseCancel.nativeBeltArc S q u v s ∈ O)
    (hpath :
      JoinedIn
        {z : M |
          f z = S.toSurgeryWindows.upper q ∧
            Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val) ∧ z ∈ O}
        (MorseCancel.nativeBeltArc S q u v r) (MorseCancel.nativeBeltArc S q u v (-r)))
    (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ γ : C(Circle, (S.data q).UpperLevel),
      ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ ∧
        Function.Injective γ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) ∧
            (∀ z, (γ z).val ∈ O) ∧
              (∀ s ∈ Set.Icc (-r) r,
                  γ (Circle.exp (2 * Real.pi / (2 * r + 1) * (s + r))) =
                    MorseCancel.nativeBeltLevelArc S q u v s) ∧
                (∀ z w,
                    γ z = (S.data q).surgery.beltSphere w ↔
                      z = Circle.exp (2 * Real.pi / (2 * r + 1) * r) ∧ v = w) ∧
                  ∀ z,
                    γ z ∈ MorseCancel.nativeBeltLevelArc S q u v '' Set.Icc (-r) r ∨
                      Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data q).upper_regular
  let α := MorseCancel.nativeBeltLevelArc S q u v
  let U : TopologicalSpace.Opens (S.data q).UpperLevel :=
    ⟨{z | Filter.Tendsto (fun t => S.flow t z.val) Filter.atTop (𝓝 p.val) ∧ z.val ∈ O},
      ((S.isOpen_minimum_forward_basin hf p hp).inter O.isOpen).preimage continuous_subtype_val⟩
  have hpr : |r| ≤ 1 := by rw [abs_of_pos hr]; exact hr1.le
  have hmr : |-r| ≤ 1 := by rw [abs_neg]; exact hpr
  have hplus : α r ∈ U := by
    change Filter.Tendsto (fun t => S.flow t (α r).val) Filter.atTop (𝓝 p.val) ∧ (α r).val ∈ O
    rw [MorseCancel.nativeBeltLevelArc_coe S q u v hpr]
    exact hpath.source_mem.2
  have hminus : α (-r) ∈ U := by
    change
      Filter.Tendsto (fun t => S.flow t (α (-r)).val) Filter.atTop (𝓝 p.val) ∧ (α (-r)).val ∈ O
    rw [MorseCancel.nativeBeltLevelArc_coe S q u v hmr]
    exact hpath.target_mem.2
  let η : Path (⟨α r, hplus⟩ : U) (⟨α (-r), hminus⟩ : U) :=
    { toFun := fun t => ⟨⟨hpath.somePath t, (hpath.somePath_mem t).1⟩, (hpath.somePath_mem t).2⟩
      continuous_toFun := (hpath.somePath.continuous.subtype_mk _).subtype_mk _
      source' :=
        Subtype.ext
          (Subtype.ext
            (hpath.somePath.source.trans (MorseCancel.nativeBeltLevelArc_coe S q u v hpr).symm))
      target' :=
        Subtype.ext
          (Subtype.ext
            (hpath.somePath.target.trans (MorseCancel.nativeBeltLevelArc_coe S q u v hmr).symm)) }
  have hαi : Set.InjOn α (Set.Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    apply MorseCancel.nativeBeltArc_injOn S q u v hx hy
    have hh := congrArg Subtype.val hxy
    rw [MorseCancel.nativeBeltLevelArc_coe S q u v (abs_le.mpr hx),
      MorseCancel.nativeBeltLevelArc_coe S q u v (abs_le.mpr hy)] at hh
    exact hh
  have hdimL : 3 ≤ Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Smale.RegularLevel.Model, finrank_euclideanSpace_fin]
    omega
  obtain ⟨γ, hγ, hγi, hγd, hshort, himage⟩ :=
    MorseCancel.exists_embedded_circle_through_arc U hr hr1
      (MorseCancel.nativeBeltLevelArc_contMDiffOn S hf q u v) hαi
      (fun _ hs => MorseCancel.nativeBeltLevelArc_derivative_injective S hf q u v hs) hplus hminus
      η hdimL
  let z₀ := Circle.exp (2 * Real.pi / (2 * r + 1) * r)
  have hzero : γ z₀ = (S.data q).surgery.beltSphere v := by
    have hh := hshort 0 ⟨by linarith, hr.le⟩
    rw [zero_add] at hh
    apply Subtype.ext
    exact
      (congrArg Subtype.val hh).trans
        ((MorseCancel.nativeBeltLevelArc_coe S q u v (s := 0) (by simp)).trans
          (MorseCancel.nativeBeltArc_zero S q u v))
  have himage' (z : Circle) :
    γ z ∈ MorseCancel.nativeBeltLevelArc S q u v '' Set.Icc (-r) r ∨
      Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) := by
    rcases himage (Set.mem_range_self z) with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz.1
  refine ⟨γ, hγ, hγi, hγd, ?_, hshort, ?_, himage'⟩
  · intro z
    rcases himage (Set.mem_range_self z) with hz | hz
    · obtain ⟨s, hs, hsz⟩ := hz
      rw [← hsz,
        MorseCancel.nativeBeltLevelArc_coe S q u v
          (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)]
      exact hshortO s hs
    · exact hz.2
  · apply
      MorseCancel.single_belt_intersection_of_arc_and_minimum_range S hf p q hpq u v hγi hzero
        hr1.le
    exact himage'

attribute [local instance 100] Classical.propDecidable in
private theorem
    AdaptedWindows.exists_transverse_belt_circle_reaching_level_with_endpoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancel.nativeMorseIndex E f p = 0)
    (hq : MorseCancel.nativeMorseIndex E f q = 1) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val))
    {a : ℝ} (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        f z ≤ a → MorseCancel.nativeMorseIndex E f z ≤ d)
    (hdn : d < n) (hcut : 1 + d < Module.finrank ℝ E) (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
      ∃ γ : C(Circle, (S.data q).UpperLevel),
        ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ ∧
          Function.Injective γ ∧
            (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) ∧
              (∀ z, (γ z).val ∈ Degree.FlowCancellation.levelBasin S.flow f a) ∧
                ∃ z₀ : Circle,
                  (∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w) ∧
                    (Function.Surjective
                        ((mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z₀ :
                              EuclideanSpace ℝ (Fin 1) →L[ℝ] Smale.RegularLevel.Model E).coprod
                          (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E)
                            (S.data q).surgery.beltSphere v))) ∧
                      ∀ z,
                        Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) ∨
                          Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 q.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data q).upper_regular
  have hqa : f q < a := (S.toSurgeryWindows.value_lt_upper q).trans_le hba
  obtain ⟨v, hv⟩ := S.exists_belt_point_reaching_level hf q n hqa hlow hdn
  obtain ⟨r, hr, hr1, hreach, hmin, hpath⟩ :=
    S.exists_belt_arc_closing_path_reaching_level hf p q hp u v hbranches hba ha hv hlow hcut
  let O : TopologicalSpace.Opens M :=
    ⟨Degree.FlowCancellation.levelBasin S.flow f a,
      (Degree.FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
          (fun z hz => S.descent z (ha z hz))).1⟩
  have hpq : p ≠ q := by
    intro heq
    have hh := hp
    rw [heq, hq] at hh
    exact Nat.one_ne_zero hh
  obtain ⟨γ, hγ, hγi, hγd, hγreach, hshort, hsingle, himage⟩ :=
    S.exists_single_belt_circle_in_open_with_image hf p q hp hpq u v O hr hr1
      (fun s hs => hreach s (abs_le.mpr hs)) hpath hdim
  let ψ : ℝ → Circle := fun t => Circle.exp (2 * Real.pi / (2 * r + 1) * (t + r))
  have hψ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ψ :=
    contMDiff_circleExp.comp (contDiff_const.mul (contDiff_id.add contDiff_const)).contMDiff
  have heq : γ ∘ ψ =ᶠ[𝓝 (0 : ℝ)] MorseCancel.nativeBeltLevelArc S q u v := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hr) hr] with t ht
    exact hshort t ⟨ht.1.le, ht.2.le⟩
  have hendpoints (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 p.val) ∨
      Filter.Tendsto (fun t => S.flow t (γ z).val) Filter.atTop (𝓝 q.val) := by
    rcases himage z with hshortz | hzmin
    · obtain ⟨s, hs, hsz⟩ := hshortz
      have hsr : |s| ≤ r := abs_le.mpr hs
      have hs1 : |s| ≤ 1 := hsr.trans hr1.le
      by_cases hs0 : s = 0
      · right
        have hz : (γ z).val = ((S.data q).surgery.beltSphere v).val := by
          rw [← hsz, MorseCancel.nativeBeltLevelArc_coe S q u v hs1, hs0,
            MorseCancel.nativeBeltArc_zero]
        rw [hz]
        exact (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere v)).mpr ⟨v, rfl⟩
      · left
        rw [← hsz, MorseCancel.nativeBeltLevelArc_coe S q u v hs1]
        exact hmin s (abs_pos.mpr hs0) hsr
    · exact Or.inl hzmin
  refine
    ⟨v, γ, hγ, hγi, hγd, hγreach, Circle.exp (2 * Real.pi / (2 * r + 1) * r), hsingle, ?_,
      hendpoints⟩
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] Smale.RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) (S.data q).surgery.beltSphere v
  have hαtrans :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Smale.RegularLevel.Model E) (MorseCancel.nativeBeltLevelArc S q u v)
              0 :
            ℝ →L[ℝ] Smale.RegularLevel.Model E).coprod
        B) :=
    MorseCancel.nativeBeltLevelArc_transverse S hf q hq n u v
  have ht :
    Function.Surjective
      ((mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ (ψ 0) :
            EuclideanSpace ℝ (Fin 1) →L[ℝ] Smale.RegularLevel.Model E).coprod
        B) :=
    MorseCancel.transverse_circle_of_arc_germ (D := EuclideanSpace ℝ (Fin n)) (J :=
      𝓘(ℝ, Smale.RegularLevel.Model E)) (α := MorseCancel.nativeBeltLevelArc S q u v) (γ := γ)
      (ψ := ψ) hγ hψ heq B hαtrans
  have hp0 : ψ 0 = Circle.exp (2 * Real.pi / (2 * r + 1) * r) := by
    dsimp [ψ]
    rw [zero_add]
  rw [hp0] at ht
  exact ht

private theorem
    AdaptedWindows.exists_native_level_basin_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) (za : { x : M // f x = a })
    (zb : { x : M // f x = b }) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    let _ := Smale.RegularLevel.chartedSpace hf hb
    ∃ D :
      PartialDiffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { x : M // f x = a } { x : M // f x = b } ∞,
      D.source = {x | x.val ∈ Degree.FlowCancellation.levelBasin S.flow f b} ∧
        D.target = {y | y.val ∈ Degree.FlowCancellation.levelBasin S.flow f a} ∧
          ∀ x ∈ D.source, ∃ t : ℝ, S.flow t x.val = (D x).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  let _ := Smale.RegularLevel.isManifold hf ha
  let _ := Smale.RegularLevel.isManifold hf hb
  let A := { x : M // f x = a }
  let B := { x : M // f x = b }
  obtain ⟨Φa, hsa, hta, hfa, -⟩ :=
    Degree.FlowCancellation.exists_native_level_flow_cylinder hf ha S.smooth S.flow S.integral
      (fun x hx => S.descent x (ha x hx)) za
  obtain ⟨Φb, hsb, htb, hfb, -⟩ :=
    Degree.FlowCancellation.exists_native_level_flow_cylinder hf hb S.smooth S.flow S.integral
      (fun x hx => S.descent x (hb x hx)) zb
  let U : Set A := {x | x.val ∈ Degree.FlowCancellation.levelBasin S.flow f b}
  let V : Set B := {x | x.val ∈ Degree.FlowCancellation.levelBasin S.flow f a}
  let P : A → B := fun x => (Φb.symm x.val).1
  let Q : B → A := fun y => (Φa.symm y.val).1
  have hU : IsOpen U := by
    have hh : IsOpen (Degree.FlowCancellation.levelBasin S.flow f b) := htb ▸ Φb.open_target
    exact hh.preimage continuous_subtype_val
  have hV : IsOpen V := by
    have hh : IsOpen (Degree.FlowCancellation.levelBasin S.flow f a) := hta ▸ Φa.open_target
    exact hh.preimage continuous_subtype_val
  have hPa (x : A) (t : ℝ) : Φa.symm (S.flow t x.val) = (x, t) := by
    have hs : (x, t) ∈ Φa.source := by rw [hsa]; trivial
    have hh : Φa.symm (Φa (x, t)) = (x, t) := Φa.left_inv' hs
    rwa [hfa] at hh
  have hPb (y : B) (t : ℝ) : Φb.symm (S.flow t y.val) = (y, t) := by
    have hs : (y, t) ∈ Φb.source := by rw [hsb]; trivial
    have hh : Φb.symm (Φb (y, t)) = (y, t) := Φb.left_inv' hs
    rwa [hfb] at hh
  have horbP (x : A) (hx : x ∈ U) : S.flow (-(Φb.symm x.val).2) x.val = (P x).val := by
    have hh : S.flow (Φb.symm x.val).2 (P x).val = x.val :=
      (hfb (Φb.symm x.val)).symm.trans (Φb.right_inv' (htb.symm ▸ hx))
    have hi := congrArg (S.flow (-(Φb.symm x.val).2)) hh
    rw [← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply] at hi
    exact hi.symm
  have horbQ (y : B) (hy : y ∈ V) : S.flow (-(Φa.symm y.val).2) y.val = (Q y).val := by
    have hh : S.flow (Φa.symm y.val).2 (Q y).val = y.val :=
      (hfa (Φa.symm y.val)).symm.trans (Φa.right_inv' (hta.symm ▸ hy))
    have hi := congrArg (S.flow (-(Φa.symm y.val).2)) hh
    rw [← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply] at hi
    exact hi.symm
  have hPU : Set.MapsTo P U V := by
    intro x hx
    have hxa : x.val ∈ Degree.FlowCancellation.levelBasin S.flow f a :=
      ⟨0, by simpa only [S.flow.map_zero_apply] using x.property⟩
    change (P x).val ∈ Degree.FlowCancellation.levelBasin S.flow f a
    exact
      horbP x hx ▸
        (Degree.FlowCancellation.levelBasin_flow_iff S.flow f a (-(Φb.symm x.val).2) x.val).mpr
          hxa
  have hQV : Set.MapsTo Q V U := by
    intro y hy
    have hyb : y.val ∈ Degree.FlowCancellation.levelBasin S.flow f b :=
      ⟨0, by simpa only [S.flow.map_zero_apply] using y.property⟩
    change (Q y).val ∈ Degree.FlowCancellation.levelBasin S.flow f b
    exact
      horbQ y hy ▸
        (Degree.FlowCancellation.levelBasin_flow_iff S.flow f b (-(Φa.symm y.val).2) y.val).mpr
          hyb
  have hQP (x : A) (hx : x ∈ U) : Q (P x) = x := by
    have hh := hPa x (-(Φb.symm x.val).2)
    rw [horbP x hx] at hh
    exact congrArg Prod.fst hh
  have hPQ (y : B) (hy : y ∈ V) : P (Q y) = y := by
    have hh := hPb y (-(Φa.symm y.val).2)
    rw [horbQ y hy] at hh
    exact congrArg Prod.fst hh
  have hPs :
    ContMDiffOn 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ P U := by
    have hh :=
      Φb.contMDiffOn_invFun.comp (Smale.RegularLevel.contMDiff_inclusion hf ha).contMDiffOn
        (show Set.MapsTo (Subtype.val : A → M) U Φb.target from fun _ hx => htb.symm ▸ hx)
    exact contMDiff_fst.comp_contMDiffOn hh
  have hQs :
    ContMDiffOn 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ Q V := by
    have hh :=
      Φa.contMDiffOn_invFun.comp (Smale.RegularLevel.contMDiff_inclusion hf hb).contMDiffOn
        (show Set.MapsTo (Subtype.val : B → M) V Φa.target from fun _ hy => hta.symm ▸ hy)
    exact contMDiff_fst.comp_contMDiffOn hh
  let D :
    PartialDiffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) A B ∞ :=
    { toFun := P
      invFun := Q
      source := U
      target := V
      map_source' := hPU
      map_target' := hQV
      left_inv' := hQP
      right_inv' := hPQ
      open_source := hU
      open_target := hV
      contMDiffOn_toFun := hPs
      contMDiffOn_invFun := hQs }
  exact ⟨D, rfl, rfl, fun x hx => ⟨-(Φb.symm x.val).2, horbP x hx⟩⟩

private theorem
    AdaptedWindows.belt_complement_reaches_lower_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (y : (S.data p).UpperLevel) (hy : y ∉ Set.range (S.data p).surgery.beltSphere) :
    y.val ∈ Degree.FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p) := by
  obtain ⟨a, ha, b, hb, hback, hforward, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct y.val
  have hyreg : y.val ∉ Smale.ManifoldMorse.criticalPoints E f :=
    (S.data p).upper_regular y.val y.property
  have hbelow : f b < S.toSurgeryWindows.lower p := by
    rcases lt_trichotomy (f b) (f p) with h | h | h
    · exact (S.toSurgeryWindows.value_lt_upper ⟨b, hb⟩).trans (S.separated ⟨b, hb⟩ p h)
    · have heq : b = p.val := S.distinct hb p.property h
      subst b
      exact (hy ((S.belt_basin_iff hf p y).mp hforward)).elim
    · have hup : f y.val < f b := by
        rw [y.property]
        exact (S.separated p ⟨b, hb⟩ h).trans (S.toSurgeryWindows.lower_lt_value ⟨b, hb⟩)
      exact (not_lt_of_ge hup.le (hheights hyreg).1).elim
  have hlow : S.toSurgeryWindows.lower p < f y.val := by
    rw [y.property]
    exact (S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward (hlow.trans (hheights hyreg).2) hbelow

private theorem
    AdaptedWindows.exists_belt_complement_lower_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        ∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  obtain ⟨P, hsource, -, horbit⟩ :=
    S.exists_native_level_basin_transport hf (S.data p).upper_regular (S.data p).lower_regular
      ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u)
  have hsrc (x : ((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel)) :
    x.val ∈ P.source := hsource.symm ▸ S.belt_complement_reaches_lower_level hf p x.val x.property
  let D :
    C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
      (S.data p).LowerLevel) :=
    ⟨fun x => P x.val,
      P.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val hsrc⟩
  refine ⟨D, fun x => horbit x.val (hsrc x), ?_⟩
  intro x y t hty
  obtain ⟨s, hs⟩ := horbit x.val (hsrc x)
  have hshared : S.flow 0 (D x).val = S.flow (s - t) y.val := by
    rw [S.flow.map_zero_apply]
    change (P x.val).val = S.flow (s - t) y.val
    rw [← hs, ← hty, ← S.flow.map_add, sub_add_cancel]
  apply Subtype.ext
  exact
    MorseCancel.native_same_level_orbit_points hf S.smooth S.flow S.integral
      (fun z hz => S.descent z ((S.data p).lower_regular z hz)) (D x).property y.property hshared

private def MorseCancel.nativeUpperMeridianInComplement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) :
    C(Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1,
      ((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel))
    where
  toFun u := ⟨nativeUpperMeridian S p v s u, nativeUpperMeridian_avoids_belt S p v s hs u⟩
  continuous_toFun := (nativeUpperMeridian S p v s).continuous.subtype_mk _

private theorem MorseCancel.lower_transport_upperMeridian_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (p : Smale.ManifoldMorse.criticalPoints E f)
    (D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel))
    (hD : ∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) :
    D.comp (nativeUpperMeridianInComplement S p v s hs) = nativeLowerMeridian S p v s := by
  apply ContinuousMap.ext
  intro u
  exact
    hD (nativeUpperMeridianInComplement S p v s hs u) (nativeLowerMeridian S p v s u)
      (Degree.BeltPassage.time s) (nativeUpperMeridian_flow S p v s hs u)

private theorem
    AdaptedWindows.exists_lower_transport_with_meridians {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
          ∀ (w : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
            (hs : 0 < (s : ℝ)),
            (D.comp (MorseCancel.nativeUpperMeridianInComplement S p w s hs)).Homotopic
              (S.data p).surgery.attachingSphere := by
  obtain ⟨D, horbit, hunique⟩ := S.exists_belt_complement_lower_transport hf p u v
  refine ⟨D, horbit, hunique, ?_⟩
  intro w s hs
  rw [MorseCancel.lower_transport_upperMeridian_eq S p D hunique w s hs]
  exact MorseCancel.nativeLowerMeridian_homotopic_attaching S p w s

private theorem
    AdaptedWindows.exists_lower_passage_homology_relation {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (H : C(ℝ × Smale.Hemisphere.Sphere 2, (S.data p).UpperLevel)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (x₀ : Smale.Hemisphere.Sphere 2)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : Smale.Hemisphere.Sphere 2,
          H (t, x) ∈ Set.range (S.data p).surgery.beltSphere ↔ t = τ ∧ x = x₀) :
    ∃ D :
      C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
        (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
          (∀ (w : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1) (s : unitInterval)
              (hs : 0 < (s : ℝ)),
              (D.comp (MorseCancel.nativeUpperMeridianInComplement S p w s hs)).Homotopic
                (S.data p).surgery.attachingSphere) ∧
            let G :=
              D.comp
                (Degree.PassageHomology.puncturedPassageTrace H
                  (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross)
            (∀ z : ({(τ, x₀)}ᶜ : Set (ℝ × Smale.Hemisphere.Sphere 2)),
                z.val.1 ∈ Set.Icc (0 : ℝ) 1 → ∃ t : ℝ, S.flow t (H z.val).val = (G z).val) ∧
              ∀ (ε : ℝ) (hε : 0 < ε) (hεx : ε < Real.exp τ),
                SingularMayerVietoris.singularHomologyMap
                    (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
                  SingularMayerVietoris.singularHomologyMap
                      (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
                    SingularMayerVietoris.singularHomologyMap
                      (G.comp (Degree.PassageHomology.cylinderLink τ x₀ ε hε hεx)) 2 := by
  obtain ⟨D, horbit, hunique, hmeridian⟩ := S.exists_lower_transport_with_meridians hf p u v
  refine ⟨D, horbit, hunique, hmeridian, ?_, ?_⟩
  · intro z hz
    have hh :=
      horbit
        (Degree.PassageHomology.puncturedPassageTrace H (Set.range (S.data p).surgery.beltSphere)
          hτ x₀ hcross z)
    rw [Degree.PassageHomology.puncturedPassageTrace_on_interval H
        (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross z hz] at hh
    exact hh
  · intro ε hε hεx
    exact
      Degree.PassageHomology.punctured_cylinder_trace_relation hτ x₀ hε hεx
        (D.comp
          (Degree.PassageHomology.puncturedPassageTrace H
            (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross))
        2 (by decide)

private def
    Smale.PartialChart.openInclusion {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    (U : TopologicalSpace.Opens X) [Nonempty U] : PartialDiffeomorph I I U X ∞ := by
  let h : OpenPartialHomeomorph U X := U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  refine
    { toPartialEquiv := h.toPartialEquiv
      open_source := h.open_source
      open_target := h.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := ?_ }
  change ContMDiffOn I I ∞ h.symm h.target
  intro x hx
  apply (ContMDiffWithinAt.subtypeVal_comp_iff U h.symm h.target x).mp
  apply contMDiffWithinAt_id.congr_of_mem (fun y hy => ?_) hx
  exact h.right_inv hy

private theorem Smale.PartialChart.openInclusion_target {E H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X]
    [ChartedSpace H X] (U : TopologicalSpace.Opens X) [Nonempty U] :
    (openInclusion (I := I) U).target = U := by
  change U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.target = U
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact Subtype.range_coe

private theorem Smale.PartialChart.openInclusion_symm_coe {E H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X]
    [ChartedSpace H X] (U : TopologicalSpace.Opens X) [Nonempty U] {x : X} (hx : x ∈ U) :
    ((openInclusion (I := I) U).symm x).val = x := by
  have h :=
    (openInclusion (I := I) U).right_inv
      (show x ∈ (openInclusion (I := I) U).target by rw [openInclusion_target]; exact hx)
  exact h

private def Degree.PassageHomology.puncturedVectorSpace (E : Type) [NormedAddCommGroup E] :
    TopologicalSpace.Opens E :=
  ⟨({0}ᶜ : Set E), isOpen_compl_singleton⟩

private theorem
    Degree.PassageHomology.radialCylinderHomeomorph_symm_fst (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ({0}ᶜ : Set E)) :
    ((radialCylinderHomeomorph E).symm x).1 = Real.log ‖x.val‖ := by
  have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property
  change Real.expOrderIso.symm ((homeomorphUnitSphereProd E) x).2 = _
  rw [Real.log_of_pos hn]
  congr 1
  apply Subtype.ext
  exact homeomorphUnitSphereProd_apply_snd_coe E x

private theorem Degree.PassageHomology.radialCylinderHomeomorph_symm_snd_coe (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : ({0}ᶜ : Set E)) :
    (((radialCylinderHomeomorph E).symm x).2 : E) = ‖x.val‖⁻¹ • x.val := by
  change (((homeomorphUnitSphereProd E) x).1 : E) = _
  exact homeomorphUnitSphereProd_apply_fst_coe E x

private def Degree.PassageHomology.radialCylinderDiffeomorph (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)] :
    Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (ℝ × Metric.sphere (0 : E) 1)
      (puncturedVectorSpace E) ∞
    where
  toEquiv := (radialCylinderHomeomorph E).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (puncturedVectorSpace E) _).mp
    change
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) ∞
        (fun p : ℝ × Metric.sphere (0 : E) 1 => Real.exp p.1 • p.2.val)
    exact
      (Real.contDiff_exp.contMDiff.comp contMDiff_fst).smul
        ((contMDiff_coe_sphere (n := n)).comp contMDiff_snd)
  contMDiff_invFun := by
    have hn : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : puncturedVectorSpace E => ‖x.val‖) := by
      intro x
      exact (contDiffAt_norm ℝ x.property).contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt
    have hl : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : puncturedVectorSpace E => Real.log ‖x.val‖) := by
      intro x
      exact
        (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr x.property)).contMDiffAt.comp x
          hn.contMDiffAt
    have hraw :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : puncturedVectorSpace E => ‖x.val‖⁻¹ • x.val) :=
      (hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul contMDiff_subtype_val
    have hfst :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        (fun x : puncturedVectorSpace E => ((radialCylinderHomeomorph E).symm x).1) := by
      have heq :
        (fun x : puncturedVectorSpace E => ((radialCylinderHomeomorph E).symm x).1) =
          (fun x => Real.log ‖x.val‖) :=
        funext (fun x => radialCylinderHomeomorph_symm_fst E x)
      rw [heq]
      exact hl
    have hval :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun x : puncturedVectorSpace E => (((radialCylinderHomeomorph E).symm x).2 : E)) := by
      have heq :
        (fun x : puncturedVectorSpace E => (((radialCylinderHomeomorph E).symm x).2 : E)) =
          (fun x => ‖x.val‖⁻¹ • x.val) :=
        funext (fun x => radialCylinderHomeomorph_symm_snd_coe E x)
      rw [heq]
      exact hraw
    have hsnd :
      ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞
        (fun x : puncturedVectorSpace E => ((radialCylinderHomeomorph E).symm x).2) :=
      hval.codRestrict_sphere (fun x => ((radialCylinderHomeomorph E).symm x).2.property)
    exact hfst.prodMk hsnd

private def Degree.PassageHomology.radialCylinderChart (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : Metric.sphere (0 : E) 1) :
    PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (ℝ × Metric.sphere (0 : E) 1) E ∞ := by
  let _ : Nonempty (puncturedVectorSpace E) :=
    ⟨⟨u.val, Metric.ne_of_mem_sphere u.property one_ne_zero⟩⟩
  exact
    (radialCylinderDiffeomorph E n).toPartialDiffeomorph.trans
      (Smale.PartialChart.openInclusion (I := 𝓘(ℝ, E)) (puncturedVectorSpace E))

private theorem
    Degree.PassageHomology.radialCylinderChart_mem_source (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : Metric.sphere (0 : E) 1) (p : ℝ × Metric.sphere (0 : E) 1) :
    p ∈ (radialCylinderChart E n u).source :=
  ⟨Set.mem_univ _, Set.mem_univ _⟩

private theorem
    Degree.PassageHomology.radialCylinderChart_mem_target (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : Metric.sphere (0 : E) 1) (z : E) : z ∈ (radialCylinderChart E n u).target ↔ z ≠ 0 := by
  let _ : Nonempty (puncturedVectorSpace E) :=
    ⟨⟨u.val, Metric.ne_of_mem_sphere u.property one_ne_zero⟩⟩
  change
    (z ∈ (Smale.PartialChart.openInclusion (I := 𝓘(ℝ, E)) (puncturedVectorSpace E)).target ∧
        (Smale.PartialChart.openInclusion (I := 𝓘(ℝ, E)) (puncturedVectorSpace E)).symm z ∈
          Set.univ) ↔
      z ≠ 0
  rw [Smale.PartialChart.openInclusion_target]
  exact ⟨fun h => h.1, fun h => ⟨h, Set.mem_univ _⟩⟩

private theorem Degree.PassageHomology.radialCylinderChart_symm_eq (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (u : Metric.sphere (0 : E) 1) (z : E) (hz : z ≠ 0) :
    (radialCylinderChart E n u).symm z = (radialCylinderHomeomorph E).symm ⟨z, hz⟩ := by
  let _ : Nonempty (puncturedVectorSpace E) :=
    ⟨⟨u.val, Metric.ne_of_mem_sphere u.property one_ne_zero⟩⟩
  change
    (radialCylinderDiffeomorph E n).symm
        ((Smale.PartialChart.openInclusion (I := 𝓘(ℝ, E)) (puncturedVectorSpace E)).symm z) =
      _
  have heq :
    (Smale.PartialChart.openInclusion (I := 𝓘(ℝ, E)) (puncturedVectorSpace E)).symm z =
      (⟨z, hz⟩ : puncturedVectorSpace E) :=
    Subtype.ext
      (Smale.PartialChart.openInclusion_symm_coe (I := 𝓘(ℝ, E)) (puncturedVectorSpace E) hz)
  rw [heq]
  rfl

private abbrev Smale.PuncturedRadial.Space (N : Type*) [Zero N] :=
  { u : N // u ≠ 0 }

private def Smale.PuncturedRadial.toSphere {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] :
    C(Space N, Metric.sphere (0 : N) 1) :=
  ⟨fun u => Smale.RadialExtension.direction u.val u.property,
    ((continuous_subtype_val.norm.inv₀ (fun u => norm_ne_zero_iff.mpr u.property)).smul
          continuous_subtype_val).subtype_mk
      _⟩

private def
    Smale.PuncturedRadial.fromSphere {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (r : ℝ)
    (hr : 0 < r) : C(Metric.sphere (0 : N) 1, Space N) :=
  ⟨fun u => ⟨r • (u : N), smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u)⟩,
    (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

private theorem Smale.PuncturedRadial.toSphere_fromSphere {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) (hr : 0 < r) (u : Metric.sphere (0 : N) 1) :
    toSphere (fromSphere r hr u) = u := by
  apply Subtype.ext
  change ‖r • (u : N)‖⁻¹ • (r • (u : N)) = (u : N)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one,
    inv_smul_smul₀ hr.ne']

private def
    Smale.PuncturedRadial.blendVector {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (r : ℝ)
    (q : (unitInterval) × Space N) : N :=
  ((1 - (q.1 : ℝ)) + (q.1 : ℝ) * (r / ‖q.2.val‖)) • q.2.val

private theorem Smale.PuncturedRadial.continuous_blendVector {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) : Continuous (blendVector (N := N) r) := by
  have ht : Continuous (fun q : (unitInterval) × Space N => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun q : (unitInterval) × Space N => q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact
    ((continuous_const.sub ht).add
          (ht.mul
            (continuous_const.div hu.norm (fun q => norm_ne_zero_iff.mpr q.2.property)))).smul
      hu

private theorem Smale.PuncturedRadial.blendVector_ne_zero {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) (hr : 0 < r) (q : (unitInterval) × Space N) : blendVector r q ≠ 0 :=
  by
  have hu : 0 < ‖q.2.val‖ := norm_pos_iff.mpr q.2.property
  have hpos : 0 < (1 - (q.1 : ℝ)) + (q.1 : ℝ) * (r / ‖q.2.val‖) := by
    have h :=
      (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) (by norm_num : (1 : ℝ) ∈ Ioi 0) (div_pos hr hu)
        (sub_nonneg.mpr q.1.property.2) q.1.property.1 (sub_add_cancel 1 (q.1 : ℝ))
    simpa only [smul_eq_mul, mul_one, Set.mem_Ioi] using h
  exact smul_ne_zero hpos.ne' q.2.property

private def
    Smale.PuncturedRadial.deformation {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (r : ℝ)
    (hr : 0 < r) : (ContinuousMap.id (Space N)).Homotopy ((fromSphere r hr).comp toSphere)
    where
  toFun q := ⟨blendVector r q, blendVector_ne_zero r hr q⟩
  continuous_toFun := (continuous_blendVector r).subtype_mk _
  map_zero_left
    u := by
    apply Subtype.ext
    simp [blendVector]
  map_one_left
    u := by
    apply Subtype.ext
    simp [blendVector, fromSphere, toSphere, Smale.RadialExtension.direction, div_eq_mul_inv,
      smul_smul]

private def
    Smale.PuncturedRadial.sphereHomotopyEquiv {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) : Metric.sphere (0 : N) 1 ≃ₕ Space N
    where
  toFun := fromSphere r hr
  invFun := toSphere
  left_inv := by
    have heq : toSphere.comp (fromSphere r hr) = ContinuousMap.id (Metric.sphere (0 : N) 1) :=
      ContinuousMap.ext (toSphere_fromSphere r hr)
    rw [heq]
  right_inv := ⟨(deformation r hr).symm⟩

private theorem Smale.LocalDegree.exists_pos_remainder_bound {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F)
    (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.ball (0 : E) ε, ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖ := by
  have herr : (fun x : E => f x - L x) =o[𝓝 (0 : E)] (fun x : E => x) := by
    convert hf.isLittleO using 1
    · rfl
    · rfl
    · simp only [hzero, sub_zero]
      rfl
    · simp only [sub_zero]
  have hbig : (fun x : E => x) =O[𝓝 (0 : E)] (fun x : E => L x) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨‖L.symm.toContinuousLinearMap‖, Filter.Eventually.of_forall ?_⟩
    intro x
    have h := L.symm.toContinuousLinearMap.le_opNorm (L x)
    simpa only [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] using h
  exact
    Metric.eventually_nhds_iff_ball.mp
      ((herr.trans_isBigO hbig).bound (by norm_num : (0 : ℝ) < 1 / 2))

private def Smale.LocalDegree.blend {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F) (t : (unitInterval))
    (x : E) : F :=
  L x + (t : ℝ) • (f x - L x)

private theorem
    Smale.LocalDegree.blend_ne_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F) (t : (unitInterval))
    {x : E} (hx : x ≠ 0) (hbound : ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) : blend f L t x ≠ 0 := by
  have hL : L x ≠ 0 := fun h => hx (L.injective (h.trans (map_zero L).symm))
  have hsmall : ‖(t : ℝ) • (f x - L x)‖ < ‖L x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    calc
      (t : ℝ) * ‖f x - L x‖ ≤ ‖f x - L x‖ := mul_le_of_le_one_left (norm_nonneg _) t.property.2
      _ ≤ (1 / 2 : ℝ) * ‖L x‖ := hbound
      _ < ‖L x‖ := by nlinarith [norm_pos_iff.mpr hL]
  intro h
  have heq : (t : ℝ) • (f x - L x) = -L x := by
    change L x + (t : ℝ) • (f x - L x) = 0 at h
    rw [add_comm] at h
    exact add_eq_zero_iff_eq_neg.mp h
  rw [heq, norm_neg] at hsmall
  exact (lt_irrefl _ hsmall)

private theorem
    Smale.LocalDegree.image_ne_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F) {x : E} (hx : x ≠ 0)
    (hbound : ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) : f x ≠ 0 := by
  have h := blend_ne_zero L (1 : (unitInterval)) hx hbound
  change L x + (1 : ℝ) • (f x - L x) ≠ 0 at h
  simpa using h

private def Smale.LocalDegree.linearSphereMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    C(Metric.sphere (0 : E) 1, Smale.PuncturedRadial.Space F) :=
  ⟨fun u =>
    ⟨L (r • (u : E)), fun h =>
      (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u))
        (L.injective (h.trans (map_zero L).symm))⟩,
    (L.continuous.comp (continuous_const.smul continuous_subtype_val)).subtype_mk _⟩

private def Smale.LocalDegree.boundaryMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : Continuous (fun u : Metric.sphere (0 : E) 1 => f (r • (u : E))))
    (hb :
      ∀ u : Metric.sphere (0 : E) 1,
        ‖f (r • (u : E)) - L (r • (u : E))‖ ≤ (1 / 2 : ℝ) * ‖L (r • (u : E))‖) :
    C(Metric.sphere (0 : E) 1, Smale.PuncturedRadial.Space F) :=
  ⟨fun u =>
    ⟨f (r • (u : E)),
      image_ne_zero L (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u)) (hb u)⟩,
    hc.subtype_mk _⟩

private def
    Smale.LocalDegree.boundaryHomotopy {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : Continuous (fun u : Metric.sphere (0 : E) 1 => f (r • (u : E))))
    (hb :
      ∀ u : Metric.sphere (0 : E) 1,
        ‖f (r • (u : E)) - L (r • (u : E))‖ ≤ (1 / 2 : ℝ) * ‖L (r • (u : E))‖) :
    (linearSphereMap L r hr).Homotopy (boundaryMap f L r hr hc hb)
    where
  toFun
    q :=
    ⟨blend f L q.1 (r • (q.2 : E)),
      blend_ne_zero L q.1 (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere q.2)) (hb q.2)⟩
  continuous_toFun := by
    have ht : Continuous (fun q : (unitInterval) × Metric.sphere (0 : E) 1 => (q.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hL :
      Continuous (fun q : (unitInterval) × Metric.sphere (0 : E) 1 => L (r • (q.2 : E))) :=
      L.continuous.comp (continuous_const.smul (continuous_subtype_val.comp continuous_snd))
    exact (hL.add (ht.smul ((hc.comp continuous_snd).sub hL))).subtype_mk _
  map_zero_left
    u := by
    apply Subtype.ext
    simp [blend, linearSphereMap]
  map_one_left
    u := by
    apply Subtype.ext
    simp [blend, boundaryMap]

private structure
    Smale.LocalDegree.BoundaryData {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F) (s : Set E) where
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : Metric.closedBall 0 radius ⊆ s
  continuous : Continuous (fun u : Metric.sphere (0 : E) 1 => f (radius • (u : E)))
  remainder_bound :
    ∀ u : Metric.sphere (0 : E) 1,
      ‖f (radius • (u : E)) - L (radius • (u : E))‖ ≤ (1 / 2 : ℝ) * ‖L (radius • (u : E))‖

public
theorem Smale.LocalDegree.norm_radius_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (u : Metric.sphere (0 : E) 1) : ‖r • (u : E)‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one]

private theorem Smale.LocalDegree.nonempty_boundaryData {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F)
    {s : Set E} (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) : Nonempty (BoundaryData f L s) := by
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨ε, hε, hεb⟩ := exists_pos_remainder_bound L hf hzero
  let r : ℝ := Min.min δ ε / 2
  have hr : 0 < r := half_pos (lt_min hδ hε)
  have hrδ : r < δ := (half_lt_self (lt_min hδ hε)).trans_le (min_le_left δ ε)
  have hrε : r < ε := (half_lt_self (lt_min hδ hε)).trans_le (min_le_right δ ε)
  have hball : Metric.closedBall (0 : E) r ⊆ s := (Metric.closedBall_subset_ball hrδ).trans hδs
  have hparam (u : Metric.sphere (0 : E) 1) : r • (u : E) ∈ Metric.closedBall (0 : E) r := by
    rw [mem_closedBall_zero_iff, norm_radius_smul r hr u]
  have hparamc : Continuous (fun u : Metric.sphere (0 : E) 1 => r • (u : E)) :=
    continuous_const.smul continuous_subtype_val
  refine ⟨⟨r, hr, hball, hc.comp_continuous hparamc (fun u => hball (hparam u)), ?_⟩⟩
  intro u
  apply hεb
  rw [mem_ball_zero_iff, norm_radius_smul r hr u]
  exact hrε

private theorem
    Smale.LocalDegree.nonempty_boundaryData_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F)
    {s : Set E} (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContDiffAt ℝ ∞ f 0) : Nonempty (BoundaryData f L s) := by
  obtain ⟨t, ht, htc⟩ := contDiffAt_zero.mp (hc.of_le (by simp))
  obtain ⟨b⟩ :=
    nonempty_boundaryData L hf hzero (Filter.inter_mem hs ht) (htc.mono Set.inter_subset_right)
  exact ⟨{ b with ball_subset := b.ball_subset.trans Set.inter_subset_left }⟩

private def
    Smale.LocalDegree.BoundaryData.map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F} {s : Set E}
    (b : Smale.LocalDegree.BoundaryData f L s) :
    C(Metric.sphere (0 : E) 1, Smale.PuncturedRadial.Space F) :=
  Smale.LocalDegree.boundaryMap f L b.radius b.radius_pos b.continuous b.remainder_bound

private theorem Smale.LocalDegree.BoundaryData.map_coe {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (b : Smale.LocalDegree.BoundaryData f L s) (u : Metric.sphere (0 : E) 1) :
    (b.map u).val = f (b.radius • (u : E)) :=
  rfl

private def
    Smale.LocalDegree.BoundaryData.homotopy {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F} {s : Set E}
    (b : Smale.LocalDegree.BoundaryData f L s) :
    (Smale.LocalDegree.linearSphereMap L b.radius b.radius_pos).Homotopy b.map :=
  Smale.LocalDegree.boundaryHomotopy f L b.radius b.radius_pos b.continuous b.remainder_bound

private def Smale.LocalDegree.puncturedLinearHomeomorph {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) :
    Smale.PuncturedRadial.Space E ≃ₜ Smale.PuncturedRadial.Space F :=
  L.toHomeomorph.subtype
    (fun x => by
      change x ≠ 0 ↔ L x ≠ 0
      constructor
      · intro hx h
        exact hx (L.injective (h.trans (map_zero L).symm))
      · intro hx h
        exact hx (h ▸ map_zero L))

private def
    Smale.LocalDegree.linearSphereEquiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    Metric.sphere (0 : E) 1 ≃ₕ Smale.PuncturedRadial.Space F :=
  (Smale.PuncturedRadial.sphereHomotopyEquiv r hr).trans
    (puncturedLinearHomeomorph L).toHomotopyEquiv

private theorem Smale.LocalDegree.BoundaryData.homology_compare {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (b : Smale.LocalDegree.BoundaryData f L s) (k : ℕ) :
    SingularMayerVietoris.singularHomologyMap b.map k =
      SingularMayerVietoris.singularHomologyMap
        (Smale.LocalDegree.linearSphereMap L b.radius b.radius_pos) k :=
  (PeriodTorusHigherHomology.homotopy_homologyMap b.homotopy k).symm

private def Smale.LocalDegree.BoundaryData.normalizedMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (b : Smale.LocalDegree.BoundaryData f L s) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1) :=
  Smale.PuncturedRadial.toSphere.comp b.map

private def MorseCancel.radialParameterChart (τ : ℝ) (u : (Smale.Hemisphere.Sphere 2)) :
    PartialDiffeomorph (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) (EuclideanSpace ℝ (Fin 3))
      (ℝ × (Smale.Hemisphere.Sphere 2)) ∞ := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let b := Degree.PassageHomology.cylinderPuncture τ u
  let T : Diffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞ :=
    { toEquiv :=
        { toFun := fun z => b + z
          invFun := fun z => z - b
          left_inv := fun z => add_sub_cancel_left b z
          right_inv := by intro z; simp }
      contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
      contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  exact
    T.toPartialDiffeomorph.trans
      (Degree.PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).symm

private theorem MorseCancel.radialParameterChart_zero_mem_source (τ : ℝ)
    (u : (Smale.Hemisphere.Sphere 2)) :
    (0 : (EuclideanSpace ℝ (Fin 3))) ∈ (radialParameterChart τ u).source := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  change
    (0 : (EuclideanSpace ℝ (Fin 3))) ∈ Set.univ ∧
      Degree.PassageHomology.cylinderPuncture τ u + 0 ∈
        (Degree.PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).target
  rw [add_zero, Degree.PassageHomology.radialCylinderChart_mem_target]
  exact
    ⟨Set.mem_univ _,
      norm_pos_iff.mp
        (by rw [Degree.PassageHomology.norm_cylinderPuncture]; exact Real.exp_pos τ)⟩

private theorem MorseCancel.radialParameterChart_zero (τ : ℝ) (u : (Smale.Hemisphere.Sphere 2)) :
    radialParameterChart τ u 0 = (τ, u) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  change
    (Degree.PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).symm
        (Degree.PassageHomology.cylinderPuncture τ u + 0) =
      (τ, u)
  rw [add_zero]
  have heq :
    Degree.PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u (τ, u) =
      Degree.PassageHomology.cylinderPuncture τ u :=
    rfl
  rw [← heq]
  exact
    (Degree.PassageHomology.radialCylinderChart (EuclideanSpace ℝ (Fin 3)) 2 u).left_inv
      (Degree.PassageHomology.radialCylinderChart_mem_source (EuclideanSpace ℝ (Fin 3)) 2 u
        (τ, u))

private theorem MorseCancel.radialParameterChart_apply (τ : ℝ) (u : (Smale.Hemisphere.Sphere 2))
    (z : (EuclideanSpace ℝ (Fin 3))) (hz : Degree.PassageHomology.cylinderPuncture τ u + z ≠ 0) :
    radialParameterChart τ u z =
      (Degree.PassageHomology.radialCylinderHomeomorph (EuclideanSpace ℝ (Fin 3))).symm
        ⟨Degree.PassageHomology.cylinderPuncture τ u + z, hz⟩ := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact
    Degree.PassageHomology.radialCylinderChart_symm_eq (EuclideanSpace ℝ (Fin 3)) 2 u
      (Degree.PassageHomology.cylinderPuncture τ u + z) hz

private theorem
    MorseCancel.radialParameterChart_link (τ : ℝ) (u : (Smale.Hemisphere.Sphere 2)) (ε : ℝ)
    (hε : 0 < ε) (hεu : ε < Real.exp τ) (w : (Smale.Hemisphere.Sphere 2)) :
    radialParameterChart τ u (ε • w.val) =
      (Degree.PassageHomology.cylinderLink τ u ε hε hεu w).val := by
  have hz : Degree.PassageHomology.cylinderPuncture τ u + ε • w.val ≠ 0 :=
    (Degree.PassageHomology.linkingSphere (Degree.PassageHomology.cylinderPuncture τ u) ε hε
          (by rwa [Degree.PassageHomology.norm_cylinderPuncture]) w).property.1
  exact radialParameterChart_apply τ u (ε • w.val) hz

private theorem
    NoExotic.IntLinearAutomorphism.apply_eq_mul (e : ℤ ≃ₗ[ℤ] ℤ) (k : ℤ) : e k = e 1 * k := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using e.map_smul k 1

private theorem NoExotic.IntLinearAutomorphism.apply_one_eq_one_or_neg_one (e : ℤ ≃ₗ[ℤ] ℤ) :
    e 1 = 1 ∨ e 1 = -1 := by
  apply Int.eq_one_or_neg_one_of_mul_eq_one (v := e.symm 1)
  rw [← apply_eq_mul, e.apply_symm_apply]

private theorem
    MorseCancel.two_sphere_map_unit_of_homology_bijective {Y : Type} [TopologicalSpace Y]
    (e : (Smale.Hemisphere.Sphere 2) ≃ₜ Y) (g : C((Smale.Hemisphere.Sphere 2), Y))
    (hg : Function.Bijective (SingularMayerVietoris.singularHomologyMap g 2)) :
    ∃ k : ℤ,
      (k = 1 ∨ k = -1) ∧
        SingularMayerVietoris.singularHomologyMap g 2 =
          k •
            SingularMayerVietoris.singularHomologyMap (e : C((Smale.Hemisphere.Sphere 2), Y)) 2 :=
  by
  let H := SphereHomology.unitSphereHomologyTopEquiv 1
  let B := LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap g 2) hg
  let J := PeriodTorusHigherHomology.homeomorphHomologyEquiv e 2
  let K : ℤ ≃ₗ[ℤ] ℤ := H.symm.trans (B.trans (J.symm.trans H))
  refine ⟨K 1, NoExotic.IntLinearAutomorphism.apply_one_eq_one_or_neg_one K, ?_⟩
  apply LinearMap.ext
  intro a
  change B a = K 1 • J a
  apply J.symm.injective
  rw [map_zsmul, J.symm_apply_apply]
  apply H.injective
  rw [map_zsmul]
  have hh := NoExotic.IntLinearAutomorphism.apply_eq_mul K (H a)
  simpa only [K, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, smul_eq_mul] using hh

private abbrev Smale.PuncturedBall.Space (E : Type*) [NormedAddCommGroup E] (R : ℝ) :=
  { x : E // x ≠ 0 ∧ ‖x‖ < R }

private def Smale.PuncturedBall.toPunctured {E : Type*} [NormedAddCommGroup E] (R : ℝ) :
    C(Space E R, Smale.PuncturedRadial.Space E) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

private def
    Smale.PuncturedBall.toSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    C(Space E R, Metric.sphere (0 : E) 1) :=
  Smale.PuncturedRadial.toSphere.comp (toPunctured R)

private def
    Smale.PuncturedBall.fromSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) : C(Metric.sphere (0 : E) 1, Space E R) :=
  ⟨fun u =>
    ⟨r • (u : E), smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u),
      by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property,
        mul_one]
      exact hrR⟩,
    (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

private theorem Smale.PuncturedBall.toSphere_fromSphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : ℝ) (r : ℝ) (hr : 0 < r) (hrR : r < R) (u : Metric.sphere (0 : E) 1) :
    toSphere R (fromSphere R r hr hrR u) = u :=
  Smale.PuncturedRadial.toSphere_fromSphere r hr u

private def
    Smale.PuncturedBall.blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ)
    (r : ℝ) (q : (unitInterval) × Space E R) : E :=
  Smale.PuncturedRadial.blendVector r (q.1, toPunctured R q.2)

private theorem Smale.PuncturedBall.continuous_blendVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : ℝ) (r : ℝ) : Continuous (blendVector (E := E) R r) :=
  (Smale.PuncturedRadial.continuous_blendVector r).comp
    (continuous_fst.prodMk ((toPunctured R).continuous.comp continuous_snd))

private theorem
    Smale.PuncturedBall.norm_blendVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (r : ℝ) (hr : 0 < r) (t : (unitInterval)) (x : Space E R) :
    ‖blendVector R r (t, x)‖ = (1 - (t : ℝ)) * ‖x.val‖ + (t : ℝ) * r := by
  have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property.1
  have hscale : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * (r / ‖x.val‖) :=
    add_nonneg (sub_nonneg.mpr t.property.2) (mul_nonneg t.property.1 (div_nonneg hr.le hn.le))
  change ‖((1 - (t : ℝ)) + (t : ℝ) * (r / ‖x.val‖)) • x.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale, add_mul, mul_assoc,
    div_mul_cancel₀ _ hn.ne']

private theorem Smale.PuncturedBall.norm_blendVector_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : ℝ) (r : ℝ) (hr : 0 < r) (hrR : r < R) (t : (unitInterval))
    (x : Space E R) : ‖blendVector R r (t, x)‖ < R := by
  rw [norm_blendVector R r hr]
  exact
    (convex_Iio (𝕜 := ℝ) R) x.property.2 hrR (sub_nonneg.mpr t.property.2) t.property.1
      (sub_add_cancel 1 (t : ℝ))

private def
    Smale.PuncturedBall.deformation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    (ContinuousMap.id (Space E R)).Homotopy ((fromSphere R r hr hrR).comp (toSphere R))
    where
  toFun
    q :=
    ⟨blendVector R r q, Smale.PuncturedRadial.blendVector_ne_zero r hr (q.1, toPunctured R q.2),
      norm_blendVector_lt R r hr hrR q.1 q.2⟩
  continuous_toFun := (continuous_blendVector R r).subtype_mk _
  map_zero_left
    x := by
    apply Subtype.ext
    simp [blendVector, Smale.PuncturedRadial.blendVector, toPunctured]
  map_one_left
    x := by
    apply Subtype.ext
    simp [blendVector, Smale.PuncturedRadial.blendVector, toPunctured, fromSphere, toSphere,
      Smale.PuncturedRadial.toSphere, Smale.RadialExtension.direction, div_eq_mul_inv, smul_smul]

private def
    Smale.PuncturedBall.sphereHomotopyEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (r : ℝ) (hr : 0 < r) (hrR : r < R) : Metric.sphere (0 : E) 1 ≃ₕ Space E R
    where
  toFun := fromSphere R r hr hrR
  invFun := toSphere R
  left_inv := by
    have h :
      (toSphere (E := E) R).comp (fromSphere R r hr hrR) =
        ContinuousMap.id (Metric.sphere (0 : E) 1) :=
      ContinuousMap.ext (toSphere_fromSphere R r hr hrR)
    rw [h]
  right_inv := ⟨(deformation R r hr hrR).symm⟩

private def MorseCancel.nativeBeltTubeSource {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.PositiveCoordinates) 1 ×
        Smale.PuncturedBall.Space d.chart.NegativeCoordinates 1,
      d.chart.beltSource d.radius d.radius_pos)
    where
  toFun
    z :=
    ⟨(z.1, z.2.val),
      d.chart.enlarged_closed_belt_subset_source d.radius d.radius_pos d.block
        ⟨Set.mem_univ _, by
          rw [mem_closedBall_zero_iff]
          exact z.2.property.2.le.trans (by norm_num)⟩⟩
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private def
    MorseCancel.nativeBeltTubeInComplement {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.PositiveCoordinates) 1 ×
        Smale.PuncturedBall.Space d.chart.NegativeCoordinates 1,
      ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel))
    where
  toFun
    z := by
    let y := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (nativeBeltTubeSource d z)
    refine ⟨y.val, ?_⟩
    intro hy
    have hz := (d.beltNormal_eq_zero_iff y.property).mpr hy
    have heq : d.beltNormal y.val = d.radius • z.2.val :=
      d.chart.beltNeighborhoodHomeomorph_normal d.radius d.radius_pos (nativeBeltTubeSource d z)
    rw [heq] at hz
    exact (smul_ne_zero d.radius_pos.ne' z.2.property.1) hz
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous.comp
            (nativeBeltTubeSource d).continuous)).subtype_mk
      _

private def MorseCancel.nativeBeltTubeMeridian {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    C(Metric.sphere (0 : d.chart.NegativeCoordinates) 1,
      ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) :=
  (nativeBeltTubeInComplement d).comp
    ((ContinuousMap.const _ v).prodMk (Smale.PuncturedBall.fromSphere 1 r hr hr1))

private theorem MorseCancel.nativeBeltTube_homotopic_meridian {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) {X : Type} [TopologicalSpace X]
    (a : C(X, Metric.sphere (0 : d.chart.PositiveCoordinates) 1))
    (b : C(X, Smale.PuncturedBall.Space d.chart.NegativeCoordinates 1))
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1)
    (ha : a.Homotopic (ContinuousMap.const _ v)) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ((nativeBeltTubeInComplement d).comp (a.prodMk b)).Homotopic
      ((nativeBeltTubeMeridian d v r hr hr1).comp ((Smale.PuncturedBall.toSphere 1).comp b)) := by
  let c := (Smale.PuncturedBall.toSphere 1).comp b
  let b' := (Smale.PuncturedBall.fromSphere 1 r hr hr1).comp c
  have hb : b.Homotopic b' := by
    have H := (Smale.PuncturedBall.deformation 1 r hr hr1).compContinuousMap b
    exact ⟨H⟩
  have hpair := ha.prodMk hb
  have hh := (ContinuousMap.Homotopic.refl (nativeBeltTubeInComplement d)).comp hpair
  have heq :
    (nativeBeltTubeInComplement d).comp ((ContinuousMap.const _ v).prodMk b') =
      (nativeBeltTubeMeridian d v r hr hr1).comp c := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [heq] at hh
  exact hh

private theorem MorseCancel.nativeBeltTubeMeridian_eq {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    [IsManifold 𝓘(ℝ, E) ∞ M] (S : AdaptedWindows E f)
    (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) :
    nativeBeltTubeMeridian (S.data q) v r hr hr1 =
      nativeUpperMeridianInComplement S q v ⟨r, hr.le, hr1.le⟩ hr := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  change
    (S.data q).chart.splitChart.symm
        ((Smale.MorseHandle.ambientMap (S.data q).radius (v.val, r • u.val)).swap) =
      (S.data q).chart.splitChart.symm (Degree.BeltPassage.upper (S.data q).radius r u.val v.val)
  congr 1
  simp only [Smale.MorseHandle.ambientMap, Degree.BeltPassage.upper, Prod.swap, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one, smul_smul]

private def
    MorseCancel.parameterBallBoundary {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] (r : ℝ)
    (hr : 0 < r) : C(Metric.sphere (0 : A) 1, Metric.closedBall (0 : A) r)
    where
  toFun
    u := ⟨r • u.val, by rw [mem_closedBall_zero_iff, Smale.LocalDegree.norm_radius_smul r hr u]⟩
  continuous_toFun := by
    have h : Continuous (fun u : Metric.sphere (0 : A) 1 => r • u.val) :=
      continuous_const.smul continuous_subtype_val
    exact h.subtype_mk _

private def MorseCancel.parameterBallCenter {A : Type} [NormedAddCommGroup A] (r : ℝ) (hr : 0 < r) :
    Metric.closedBall (0 : A) r :=
  ⟨0, by simpa using hr.le⟩

private def MorseCancel.parameterBallContraction {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (r : ℝ) (hr : 0 < r) :
    (parameterBallBoundary (A := A) r hr).Homotopy
      (ContinuousMap.const _ (parameterBallCenter r hr))
    where
  toFun
    z :=
    ⟨(1 - (z.1 : ℝ)) • (r • z.2.val),
      by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr z.1.property.2),
        Smale.LocalDegree.norm_radius_smul r hr z.2]
      exact mul_le_of_le_one_left hr.le (by linarith [z.1.property.1])⟩
  continuous_toFun := by
    have h :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : A) 1 => (1 - (z.1 : ℝ)) • (r • z.2.val)) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_const.smul (continuous_subtype_val.comp continuous_snd))
    exact h.subtype_mk _
  map_zero_left u := by apply Subtype.ext; simp [parameterBallBoundary]
  map_one_left u := by apply Subtype.ext; simp [parameterBallCenter]

private theorem MorseCancel.parameterBall_boundary_nullhomotopic {A : Type} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {Y : Type} [TopologicalSpace Y] (r : ℝ) (hr : 0 < r)
    (g : C(Metric.closedBall (0 : A) r, Y)) :
    (g.comp (parameterBallBoundary r hr)).Homotopic
      (ContinuousMap.const _ (g (parameterBallCenter r hr))) := by
  have h := (ContinuousMap.Homotopic.refl g).comp ⟨parameterBallContraction r hr⟩
  exact h

private theorem MorseCancel.normalized_pos_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℝ) (hr : 0 < r) (x : F) : ‖r • x‖⁻¹ • (r • x) = ‖x‖⁻¹ • x := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev, smul_smul, mul_assoc,
    inv_mul_cancel₀ hr.ne', mul_one]

private def MorseCancel.beltBallCoordinates {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} [NormedAddCommGroup A]
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (ε : ℝ)
    (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius)) :
    C(Metric.closedBall (0 : A) ε,
      Metric.sphere (0 : d.chart.PositiveCoordinates) 1 × d.chart.NegativeCoordinates) :=
  ⟨fun z => ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm (F z)).val,
    continuous_subtype_val.comp
      ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm.continuous.comp
        F.continuous)⟩

private theorem MorseCancel.beltBallCoordinates_normal {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (z : Metric.closedBall (0 : A) ε) :
    (beltBallCoordinates d ε F z).2 = d.radius⁻¹ • d.beltNormal (F z).val :=
  rfl

private def
    MorseCancel.beltBallBoundaryNormal {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (ε : ℝ) (hε : 0 < ε)
    (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) :
    C(Metric.sphere (0 : A) 1, Smale.PuncturedBall.Space d.chart.NegativeCoordinates 1) :=
  ⟨fun u => ⟨(beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2, hne u, hsmall _⟩,
    ((beltBallCoordinates d ε F).continuous.snd.comp
          (parameterBallBoundary ε hε).continuous).subtype_mk
      _⟩

private def MorseCancel.beltBallBoundaryInComplement {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) :
    C(Metric.sphere (0 : A) 1, ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) :=
  (nativeBeltTubeInComplement d).comp
    (((ContinuousMap.fst.comp (beltBallCoordinates d ε F)).comp
          (parameterBallBoundary ε hε)).prodMk
      (beltBallBoundaryNormal d ε hε F hsmall hne))

private theorem MorseCancel.beltBallBoundaryInComplement_coe {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (u : Metric.sphere (0 : A) 1) :
    (beltBallBoundaryInComplement d ε hε F hsmall hne u).val =
      (F (parameterBallBoundary ε hε u)).val := by
  let y := F (parameterBallBoundary ε hε u)
  let e := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
  change
    (e
          (nativeBeltTubeSource d
            ((e.symm y).val.1, (beltBallBoundaryNormal d ε hε F hsmall hne u)))).val =
      y.val
  have hs :
    nativeBeltTubeSource d ((e.symm y).val.1, (beltBallBoundaryNormal d ε hε F hsmall hne u)) =
      e.symm y := by
    apply Subtype.ext
    rfl
  rw [hs, e.apply_symm_apply]

private theorem
    MorseCancel.beltBallBoundary_homotopic_meridian {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (beltBallBoundaryInComplement d ε hε F hsmall hne).Homotopic
      ((nativeBeltTubeMeridian d (beltBallCoordinates d ε F (parameterBallCenter ε hε)).1 r hr
            hr1).comp
        ((Smale.PuncturedBall.toSphere 1).comp (beltBallBoundaryNormal d ε hε F hsmall hne))) := by
  let a := ContinuousMap.fst.comp (beltBallCoordinates d ε F)
  have ha := parameterBall_boundary_nullhomotopic ε hε a
  exact
    nativeBeltTube_homotopic_meridian d (a.comp (parameterBallBoundary ε hε))
      (beltBallBoundaryNormal d ε hε F hsmall hne) (a (parameterBallCenter ε hε)) ha r hr hr1

private theorem MorseCancel.beltBallBoundary_normalized_coe {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (u : Metric.sphere (0 : A) 1) :
    (Smale.PuncturedBall.toSphere 1 (beltBallBoundaryNormal d ε hε F hsmall hne u)).val =
      ‖d.beltNormal (F (parameterBallBoundary ε hε u)).val‖⁻¹ •
        d.beltNormal (F (parameterBallBoundary ε hε u)).val := by
  change
    ‖d.radius⁻¹ • d.beltNormal (F (parameterBallBoundary ε hε u)).val‖⁻¹ •
        (d.radius⁻¹ • d.beltNormal (F (parameterBallBoundary ε hε u)).val) =
      _
  exact normalized_pos_smul d.radius⁻¹ (inv_pos.mpr d.radius_pos) _

private theorem MorseCancel.normal_boundary_homotopic_native_meridian {E M A : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (g : A → d.UpperLevel)
    {L : A ≃L[ℝ] d.chart.NegativeCoordinates} {s : Set A}
    (b : Smale.LocalDegree.BoundaryData (d.beltNormal ∘ g) L s) (hc : ContinuousOn g s)
    (hdomain : ∀ z ∈ s, g z ∈ d.beltNormalDomain)
    (hsmall : ∀ z ∈ s, ‖d.radius⁻¹ • d.beltNormal (g z)‖ < 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ J : C(Metric.sphere (0 : A) 1, ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)),
      (∀ u, (J u).val = g (b.radius • u.val)) ∧
        ∃ v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1,
          J.Homotopic ((nativeBeltTubeMeridian d v r hr hr1).comp b.normalizedMap) := by
  let F : C(Metric.closedBall (0 : A) b.radius, d.chart.beltTarget d.radius) :=
    { toFun := fun z => ⟨g z.val, hdomain z.val (b.ball_subset z.property)⟩
      continuous_toFun :=
        (hc.comp_continuous continuous_subtype_val (fun z => b.ball_subset z.property)).subtype_mk
          _ }
  have hsmallF : ∀ z, ‖(beltBallCoordinates d b.radius F z).2‖ < 1 := by
    intro z
    rw [beltBallCoordinates_normal]
    exact hsmall z.val (b.ball_subset z.property)
  have hne :
    ∀ u,
      (beltBallCoordinates d b.radius F (parameterBallBoundary b.radius b.radius_pos u)).2 ≠ 0 := by
    intro u
    rw [beltBallCoordinates_normal]
    exact smul_ne_zero (inv_ne_zero d.radius_pos.ne') (b.map u).property
  let J := beltBallBoundaryInComplement d b.radius b.radius_pos F hsmallF hne
  have hJ : ∀ u, (J u).val = g (b.radius • u.val) := by
    intro u
    exact beltBallBoundaryInComplement_coe d b.radius b.radius_pos F hsmallF hne u
  let v := (beltBallCoordinates d b.radius F (parameterBallCenter b.radius b.radius_pos)).1
  have hH := beltBallBoundary_homotopic_meridian d b.radius b.radius_pos F hsmallF hne r hr hr1
  have heq :
    (Smale.PuncturedBall.toSphere 1).comp
        (beltBallBoundaryNormal d b.radius b.radius_pos F hsmallF hne) =
      b.normalizedMap := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    exact beltBallBoundary_normalized_coe d b.radius b.radius_pos F hsmallF hne u
  rw [heq] at hH
  exact ⟨J, hJ, v, hH⟩

private theorem
    MorseCancel.exists_small_native_belt_neighborhood {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (G : A → d.UpperLevel) (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) {t : Set A}
    (ht : t ∈ 𝓝 (0 : A)) (hc : ContinuousOn G t) (hcenter : G 0 = d.surgery.beltSphere v) :
    ∃ s : Set A,
      s ∈ 𝓝 (0 : A) ∧
        s ⊆ t ∧
          ContinuousOn G s ∧
            (∀ z ∈ s, G z ∈ d.beltNormalDomain) ∧
              (∀ z ∈ s, ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1) := by
  have hG : ContinuousAt G 0 := hc.continuousAt ht
  have hdomain : G 0 ∈ d.beltNormalDomain := hcenter ▸ d.belt_mem_normalDomain v
  have hsplit : ContinuousAt d.chart.splitChart (G 0).val :=
    d.chart.splitChart.contMDiffOn_toFun.continuousOn.continuousAt
      (d.chart.splitChart.open_source.mem_nhds hdomain)
  have hGM : ContinuousAt (fun z : A => (G z).val) 0 :=
    (continuous_subtype_val : Continuous (Subtype.val : d.UpperLevel → M)).continuousAt.comp hG
  have hsplitG : ContinuousAt (fun z : A => d.chart.splitChart (G z).val) 0 :=
    ContinuousAt.comp (f := fun z : A => (G z).val) hsplit hGM
  have hnormal : ContinuousAt (fun z => d.beltNormal (G z)) 0 := by
    change ContinuousAt (fun z : A => (d.chart.splitChart (G z).val).1) 0
    exact hsplitG.fst
  have hsize : ContinuousAt (fun z => ‖d.radius⁻¹ • d.beltNormal (G z)‖) 0 :=
    (hnormal.const_smul d.radius⁻¹).norm
  have hzero : ‖d.radius⁻¹ • d.beltNormal (G 0)‖ < 1 := by
    rw [hcenter, d.beltNormal_belt, smul_zero, norm_zero]
    norm_num
  have h₀ : G ⁻¹' d.beltNormalDomain ∈ 𝓝 (0 : A) :=
    hG.preimage_mem_nhds (d.isOpen_beltNormalDomain.mem_nhds hdomain)
  have h₁ : {z : A | ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1} ∈ 𝓝 (0 : A) :=
    hsize.preimage_mem_nhds (Iio_mem_nhds hzero)
  let s := t ∩ (G ⁻¹' d.beltNormalDomain ∩ {z : A | ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1})
  refine
    ⟨s, Filter.inter_mem ht (Filter.inter_mem h₀ h₁), Set.inter_subset_left,
      hc.mono Set.inter_subset_left, ?_, ?_⟩
  · intro z hz
    exact hz.2.1
  · intro z hz
    exact hz.2.2

private theorem Degree.MorseRearrangement.exists_radius_supported_bump_preparation {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source)
    {C : Set M} (hC : ∀ y ∈ C, y ∉ Φ '' tsupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∀ e : Diffeomorph J J M M ∞,
              (∀ y, e y = Smale.SupportedDiffeomorph.bumpFamily Φ β (a, y)) →
                Nonempty
                  (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e (Φ '' tsupport β) C) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    Smale.SupportedDiffeomorph.exists_small_supported_bump_isotopy Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro a ha e he
  obtain ⟨A, hA, hzero, hdiff, hfix, hterminal⟩ := hsmall a ha
  have hone : ∀ y, A (1, y) = e y := by
    intro y
    rw [he]
    by_cases hy : y ∈ Φ.target
    · have hh := hterminal (Φ.symm y) (Φ.map_target' hy)
      have hpoint : Φ (Φ.symm y) = y := Φ.right_inv' hy
      rw [hpoint] at hh
      change A (1, y) = Smale.SupportedDiffeomorph.extendMap Φ (fun x => x + β x • a) y
      rw [Smale.SupportedDiffeomorph.extendMap_of_mem Φ _ hy]
      exact hh
    · have hnot : y ∉ Φ '' tsupport β := by
        rintro ⟨x, hx, rfl⟩
        exact hy (Φ.map_source' (hsupport hx))
      rw [hfix 1 y hnot, Smale.SupportedDiffeomorph.bumpFamily_fixed_outside Φ β a hnot]
  refine
    ⟨{  family := A
        smooth := hA
        zero := hzero
        one := hone
        slices := ?_
        fixedOutside := hfix
        fixedOn := fun t y hy => hfix t y (hC y hy) }⟩
  intro t
  obtain ⟨d, hd⟩ := hdiff t
  exact ⟨d, fun y => (hd y).symm⟩

private theorem Degree.MorseRearrangement.ambient_patch_support_compact {G K N X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] [TopologicalSpace X]
    (p : Smale.NativeTransversality.Patch J X (N := N)) :
    IsCompact (p.chart.symm '' tsupport p.cutoff) :=
  p.cutoff_compact.isCompact.image_of_continuousOn
    (p.chart.contMDiffOn_invFun.continuousOn.mono p.cutoff_support)

private theorem Degree.MorseRearrangement.exists_ambient_patch_in_open {G K N X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] [TopologicalSpace X] [FiniteDimensional ℝ G]
    [J.Boundaryless] [IsManifold J ∞ N] [CompactSpace X] [T2Space X] {f : X → N}
    (hf : Continuous f) {U : Set N} (hU : IsOpen U) (x : X) (hfxU : f x ∈ U) :
    ∃ p : Smale.NativeTransversality.Patch J X (N := N),
      p.Compatible f ∧ x ∈ interior p.core ∧ p.chart.symm '' tsupport p.cutoff ⊆ U := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  have hcx : f x ∈ c.source := mem_extChartAt_source _
  let V : Set G := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hU
  have hcv : c (f x) ∈ V :=
    ⟨c.map_source' hcx, by
      change c.symm (c (f x)) ∈ U
      have heq : c.symm (c (f x)) = f x := c.left_inv' hcx
      rw [heq]
      exact hfxU⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hcv)
  obtain ⟨β, hβ, hsupport, W, hW, hcenter, -, hone⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed (K := {c (f x)}) (U :=
      Metric.ball (c (f x)) r) isClosed_singleton Metric.isOpen_ball
      (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  have hcompact : HasCompactSupport β :=
    (ProperSpace.isCompact_closedBall (c (f x)) r).of_isClosed_subset (isClosed_tsupport β)
      (hsupport.trans Metric.ball_subset_closedBall)
  let O : Set N := c.source ∩ c ⁻¹' W
  have hO : IsOpen O := c.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_source hW
  have hfx : f x ∈ O := ⟨hcx, hcenter (Set.mem_singleton _)⟩
  obtain ⟨C, hC, -, hxC, hCO⟩ :=
    exists_compact_closed_between (isCompact_singleton (x := x)) (hO.preimage hf)
      (Set.singleton_subset_iff.mpr hfx)
  let p : Smale.NativeTransversality.Patch J X (N := N) :=
    { core := C
      core_compact := hC
      chart := c
      cutoff := β
      cutoff_smooth := hβ
      cutoff_compact := hcompact
      cutoff_support := hsupport.trans (hball.trans Set.inter_subset_left)
      plateau := O
      plateau_open := hO
      plateau_source := Set.inter_subset_left
      plateau_one := by
        intro y hy
        filter_upwards [hW.mem_nhds hy.2] with z hz
        exact hone hz }
  refine ⟨p, hCO, hxC (Set.mem_singleton x), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact (hball (hsupport hz)).2

private theorem
    Degree.MorseRearrangement.exists_relative_ambient_patch_step {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι]
    (p : ι → Smale.NativeTransversality.Patch J X (N := N)) (i : ι) {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {B : Set X}
    (hB : IsCompact B) (htrans : ∀ x ∈ B, ∀ y, Smale.NativeTransversality.At I I' J f g x y)
    {C : Set N} (hC : ∀ y ∈ C, y ∉ (p i).chart.symm '' tsupport (p i).cutoff) :
    ∃ e : Diffeomorph J J N N ∞,
      (∀ j, (p j).Compatible (e ∘ f)) ∧
        (∀ x ∈ B ∪ (p i).core, ∀ y, Smale.NativeTransversality.At I I' J (e ∘ f) g x y) ∧
          Nonempty
            (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e
              ((p i).chart.symm '' tsupport (p i).cutoff) C) := by
  let A : G × X → N := fun q =>
    Smale.SupportedDiffeomorph.bumpFamily (p i).chart.symm (p i).cutoff (q.1, f q.2)
  have hkeep : ∀ᶠ a in 𝓝 (0 : G), ∀ j, (p j).Compatible (fun x => A (a, x)) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.SupportedDiffeomorph.eventually_bumpFamily_maps_compact_into_open (p i).chart.symm
        (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hf.continuous
        (p j).core_compact (p j).plateau_open (hcompatible j)
  obtain ⟨δ, hδ, -, hsmooth, -⟩ :=
    Smale.SupportedDiffeomorph.exists_radius_ambient_bumpFamily (p i).chart.symm
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support
  have hA : ContMDiffOn (𝓘(ℝ, G).prod I) J ∞ A (Metric.ball (0 : G) δ ×ˢ Set.univ) := by
    intro q hq
    have hsmall : ‖q.1‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hq.1
    have hpair :
      ContMDiffAt (𝓘(ℝ, G).prod I) (𝓘(ℝ, G).prod J) ∞ (fun r : G × X => (r.1, f r.2)) q :=
      contMDiffAt_fst.prodMk (hf.comp contMDiff_snd).contMDiffAt
    exact ((hsmooth (q.1, f q.2) hsmall).comp q hpair).contMDiffWithinAt
  have hzero : (fun x => A (0, x)) = f := by
    funext x
    exact Smale.SupportedDiffeomorph.bumpFamily_zero _ _ _
  have hregular :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ z ∈ B ×ˢ (Set.univ : Set Y),
        Smale.NativeTransversality.At I I' J (fun x => A (a, x)) g z.1 z.2 := by
    apply
      Smale.NativeTransversality.eventually_on_compact Metric.isOpen_ball hA hg hdim
        (hB.prod isCompact_univ) (Metric.mem_ball_self hδ)
    intro z hz
    rw [hzero]
    exact htrans z.1 hz.1 z.2
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp (hkeep.and hregular)
  obtain ⟨η, hη, hisotopy⟩ :=
    exists_radius_supported_bump_preparation (p i).chart.symm (p i).cutoff_smooth
      (p i).cutoff_compact (p i).cutoff_support hC
  obtain ⟨a, ha, e, he, -, -, hnew⟩ :=
    Smale.ChartMapPerturbation.exists_ambient_transverse_plateau (p i).chart hf hg
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hdim (lt_min hε hη)
  have hgood :=
    hsmall
      (show a ∈ Metric.ball (0 : G) ε by
        simpa only [Metric.mem_ball, dist_zero_right] using (lt_min_iff.mp ha).1)
  have heq : (fun x => A (a, x)) = e ∘ f := funext (fun x => (he (f x)).symm)
  refine ⟨e, ?_, ?_, hisotopy a (lt_min_iff.mp ha).2 e he⟩
  · intro j
    exact heq ▸ hgood.1 j
  · intro x hx y
    rcases hx with hx | hx
    · exact heq ▸ hgood.2 (x, y) ⟨hx, Set.mem_univ y⟩
    · intro hxy
      have hplateau := hcompatible i hx
      exact hnew x ((p i).plateau_source hplateau) ((p i).plateau_one _ hplateau) y hxy

private def Degree.MorseRearrangement.compose_supported_ambient_isotopies {G K N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] {e d : Diffeomorph J J N N ∞} {K₁ K₂ C : Set N}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K₁ C)
    (B : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy d K₂ C) :
    Smale.SupportedDiffeomorph.SupportedRelativeIsotopy (e.trans d) (K₁ ∪ K₂) C
    where
  family := fun p => B.family (p.1, A.family p)
  smooth := B.smooth.comp (contMDiff_fst.prodMk A.smooth)
  zero := fun x => by rw [A.zero, B.zero]
  one := fun x => by change B.family (1, A.family (1, x)) = d (e x); rw [A.one, B.one]
  slices := by
    intro t
    obtain ⟨d₁, hd₁⟩ := A.slices t
    obtain ⟨d₂, hd₂⟩ := B.slices t
    refine ⟨d₁.trans d₂, ?_⟩
    intro x
    change d₂ (d₁ x) = B.family (t, A.family (t, x))
    rw [hd₁, hd₂]
  fixedOutside := by
    intro t x hx
    rw [A.fixedOutside t x (fun h => hx (Or.inl h)), B.fixedOutside t x (fun h => hx (Or.inr h))]
  fixedOn := by
    intro t x hx
    rw [A.fixedOn t x hx, B.fixedOn t x hx]

private theorem Degree.MorseRearrangement.exists_finite_relative_patch_diffeomorph
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [LindelofSpace (X × Y)] {ι : Type*}
    [Finite ι] (p : ι → Smale.NativeTransversality.Patch J X (N := N)) {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {U : Set N}
    (hsupport : ∀ j, (p j).chart.symm '' tsupport (p j).cutoff ⊆ U) (s : Finset ι) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧
        C ⊆ U ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e C Uᶜ) ∧
            (∀ j, (p j).Compatible (e ∘ f)) ∧
              ∀ j ∈ s,
                ∀ x ∈ (p j).core, ∀ y, Smale.NativeTransversality.At I I' J (e ∘ f) g x y := by
  classical
    induction s using Finset.induction_on with
  |
    empty =>
    let A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy (Diffeomorph.refl J N ∞) ∅ Uᶜ :=
      { family := Prod.snd
        smooth := contMDiff_snd
        zero := fun _ => rfl
        one := fun _ => rfl
        slices := fun _ => ⟨Diffeomorph.refl J N ∞, fun _ => rfl⟩
        fixedOutside := fun _ _ _ => rfl
        fixedOn := fun _ _ _ => rfl }
    refine ⟨Diffeomorph.refl J N ∞, ∅, isCompact_empty, Set.empty_subset _, ⟨A⟩, hcompatible, ?_⟩
    intro j hj
    simp at hj
  | @insert i s _ ih =>
    obtain ⟨e₁, C₁, hC₁, hC₁U, ⟨A₁⟩, hc₁, ht₁⟩ := ih
    let B : Set X := ⋃ j ∈ s, (p j).core
    have hB : IsCompact B := s.isCompact_biUnion (fun j _ => (p j).core_compact)
    have htrans : ∀ x ∈ B, ∀ y, Smale.NativeTransversality.At I I' J (e₁ ∘ f) g x y := by
      intro x hx y
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      exact ht₁ j hj x hxj y
    obtain ⟨e₂, hc₂, ht₂, ⟨A₂⟩⟩ :=
      exists_relative_ambient_patch_step (C := Uᶜ) p i (e₁.contMDiff.comp hf) hg hc₁ hdim hB
        htrans (fun y hy hys => hy (hsupport i hys))
    refine
      ⟨e₁.trans e₂, C₁ ∪ ((p i).chart.symm '' tsupport (p i).cutoff),
        hC₁.union (ambient_patch_support_compact (p i)), Set.union_subset hC₁U (hsupport i),
        ⟨compose_supported_ambient_isotopies A₁ A₂⟩, hc₂, ?_⟩
    intro j hj x hx y
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact ht₂ x (Or.inr hx) y
    · exact ht₂ x (Or.inl (Set.mem_iUnion₂.mpr ⟨j, hjs, hx⟩)) y

private theorem Degree.MorseRearrangement.exists_supported_ambient_transverse_in_open
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [CompactSpace X] [T2Space X] {f : X → N}
    {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {U : Set N}
    (hU : IsOpen U) (hfU : Set.range f ⊆ U) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧
        C ⊆ U ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e C Uᶜ) ∧
            ∀ x y, Smale.NativeTransversality.At I I' J (e ∘ f) g x y := by
  classical
  choose p hp hx hs using fun x : X =>
    exists_ambient_patch_in_open (J := J) hf.continuous hU x (hfU (Set.mem_range_self x))
  have hcover : (Set.univ : Set X) ⊆ ⋃ x : X, interior (p x).core := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hscover⟩ :=
    isCompact_univ.elim_finite_subcover (fun x : X => interior (p x).core)
      (fun _ => isOpen_interior) hcover
  obtain ⟨e, C, hC, hCU, hIso, -, ht⟩ :=
    exists_finite_relative_patch_diffeomorph (fun i : s => p i.1) hf hg (fun i => hp i.1) hdim
      (fun i => hs i.1) Finset.univ
  refine ⟨e, C, hC, hCU, hIso, ?_⟩
  intro x y
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hscover (Set.mem_univ x))
  exact ht ⟨i, hi⟩ (Finset.mem_univ _) x (interior_subset hxi) y

private theorem Degree.MorseRearrangement.exists_supported_ambient_disjoint_in_open
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) {U : Set N}
    (hU : IsOpen U) (hfU : Set.range f ⊆ U) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧
        C ⊆ U ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e C Uᶜ) ∧
            Disjoint (Set.range (e ∘ f)) (Set.range g) := by
  classical
  let d := Module.finrank ℝ G - (Module.finrank ℝ D + Module.finrank ℝ Z)
  let f' : X × Smale.Hemisphere.Sphere d → N := f ∘ Prod.fst
  have hf' : ContMDiff (I.prod (𝓡 d)) J ∞ f' := hf.comp contMDiff_fst
  have hdim' :
    Module.finrank ℝ (D × EuclideanSpace ℝ (Fin d)) + Module.finrank ℝ Z = Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    dsimp [d]
    omega
  have hf'U : Set.range f' ⊆ U := by
    rintro _ ⟨x, rfl⟩
    exact hfU (Set.mem_range_self x.1)
  obtain ⟨e, C, hC, hCU, hIso, ht⟩ :=
    exists_supported_ambient_transverse_in_open hf' hg hdim' hU hf'U
  have htrans : ∀ x y, Smale.NativeTransversality.At I I' J (e ∘ f) g x y := by
    intro x y
    let w : Smale.Hemisphere.Sphere d := Smale.Hemisphere.point Bool.true ⟨0, by simp []⟩
    apply
      native_transverse_of_ignored_factor (I'' := 𝓡 d) w
        ((e.contMDiff.comp hf).mdifferentiable (by simp) x)
    exact ht (x, w) y
  exact ⟨e, C, hC, hCU, hIso, disjoint_ranges_of_native_transverse_dimension htrans hdim⟩

private theorem Degree.MorseRearrangement.exists_supported_ambient_disjoint_fixing_closed
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) {C : Set N}
    (hC : IsClosed C) (hfC : Disjoint (Set.range f) C) :
    ∃ (e : Diffeomorph J J N N ∞) (K : Set N),
      IsCompact K ∧
        K ⊆ Cᶜ ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K C) ∧
            Disjoint (Set.range (e ∘ f)) (Set.range g) := by
  have hfU : Set.range f ⊆ Cᶜ := fun _ hx hy => Set.disjoint_left.mp hfC hx hy
  obtain ⟨e, K, hK, hKU, hIso, hdisj⟩ :=
    exists_supported_ambient_disjoint_in_open hf hg hdim hC.isOpen_compl hfU
  refine ⟨e, K, hK, hKU, ?_, hdisj⟩
  simpa only [compl_compl] using hIso

private def
    Degree.MorseRearrangement.otherSheetImages {ι X N : Type*} (a : ι → X → N) (i : ι) : Set N :=
  ⋃ j : { j : ι // j ≠ i }, Set.range (a j.val)

private theorem
    Degree.MorseRearrangement.mem_otherSheetImages {ι X N : Type*} (a : ι → X → N) (i j : ι)
    (hji : j ≠ i) (x : X) : a j x ∈ otherSheetImages a i :=
  Set.mem_iUnion.mpr ⟨⟨j, hji⟩, Set.mem_range_self x⟩

private def Degree.MorseRearrangement.sheetSum (X : Type) : ℕ → Type
  | 0 => PEmpty
  | n + 1 => X ⊕ sheetSum X n

private instance Degree.MorseRearrangement.sheetSumTopology {X : Type} [TopologicalSpace X] :
    (n : ℕ) → TopologicalSpace (sheetSum X n)
  | 0 => inferInstanceAs (TopologicalSpace PEmpty)
  | n + 1 =>
    let _ := sheetSumTopology (X := X) n
    inferInstanceAs (TopologicalSpace (X ⊕ sheetSum X n))

private instance Degree.MorseRearrangement.sheetSumCompact {X : Type} [TopologicalSpace X]
    [CompactSpace X] : (n : ℕ) → CompactSpace (sheetSum X n)
  | 0 => inferInstanceAs (CompactSpace PEmpty)
  | n + 1 =>
    let _ := sheetSumCompact (X := X) n
    inferInstanceAs (CompactSpace (X ⊕ sheetSum X n))

private instance Degree.MorseRearrangement.sheetSumT2 {X : Type} [TopologicalSpace X] [T2Space X] :
    (n : ℕ) → T2Space (sheetSum X n)
  | 0 => inferInstanceAs (T2Space PEmpty)
  | n + 1 =>
    let _ := sheetSumT2 (X := X) n
    inferInstanceAs (T2Space (X ⊕ sheetSum X n))

private instance Degree.MorseRearrangement.sheetSumSecondCountable {X : Type} [TopologicalSpace X]
    [SecondCountableTopology X] : (n : ℕ) → SecondCountableTopology (sheetSum X n)
  | 0 => inferInstanceAs (SecondCountableTopology PEmpty)
  | n + 1 =>
    let _ := sheetSumSecondCountable (X := X) n
    inferInstanceAs (SecondCountableTopology (X ⊕ sheetSum X n))

private instance
    Degree.MorseRearrangement.sheetSumChartedSpace {X : Type} [TopologicalSpace X] {H : Type}
    [TopologicalSpace H] [ChartedSpace H X] : (n : ℕ) → ChartedSpace H (sheetSum X n)
  | 0 => ChartedSpace.empty H PEmpty
  | n + 1 =>
    let _ := sheetSumChartedSpace (X := X) (H := H) n
    inferInstanceAs (ChartedSpace H (X ⊕ sheetSum X n))

private instance
    Degree.MorseRearrangement.sheetSumIsManifold {X : Type} [TopologicalSpace X] {E H : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [ChartedSpace H X] [IsManifold I ∞ X] : (n : ℕ) → IsManifold I ∞ (sheetSum X n)
  | 0 =>
    let _ : ChartedSpace H PEmpty := sheetSumChartedSpace (X := X) 0
    inferInstanceAs (IsManifold I ∞ PEmpty)
  | n + 1 =>
    let _ := sheetSumIsManifold (X := X) (I := I) n
    inferInstanceAs (IsManifold I ∞ (X ⊕ sheetSum X n))

private def Degree.MorseRearrangement.sheetSumMap {X : Type} {N : Type} :
    (n : ℕ) → (Fin n → X → N) → sheetSum X n → N
  | 0, _, x => x.elim
  | n + 1, a, x => Sum.elim (a 0) (sheetSumMap n (fun i => a i.succ)) x

private theorem
    Degree.MorseRearrangement.range_sheetSumMap {X : Type} {N : Type}
    (n : ℕ) (a : Fin n → X → N) : Set.range (sheetSumMap n a) = ⋃ i, Set.range (a i) := by
  induction n with
  | zero =>
    ext y
    simp only [Set.mem_range, Set.mem_iUnion]
    constructor
    · rintro ⟨x, _⟩
      exact x.elim
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
    ext y
    constructor
    · rintro ⟨x, hx⟩
      rcases x with x | x
      · exact Set.mem_iUnion.mpr ⟨0, ⟨x, hx⟩⟩
      · have hy : y ∈ Set.range (sheetSumMap n (fun i => a i.succ)) := ⟨x, hx⟩
        rw [ih] at hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
        exact Set.mem_iUnion.mpr ⟨i.succ, hi⟩
    · intro hy
      obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp hy
      cases i using Fin.cases with
      | zero => exact ⟨Sum.inl x, hx⟩
      | succ
        i =>
        have hy' : y ∈ ⋃ i : Fin n, Set.range (a i.succ) := Set.mem_iUnion.mpr ⟨i, ⟨x, hx⟩⟩
        rw [← ih] at hy'
        obtain ⟨z, hz⟩ := hy'
        exact ⟨Sum.inr z, hz⟩

private theorem Degree.MorseRearrangement.contMDiff_sheetSumMap {X : Type} [TopologicalSpace X]
    {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H X] {G K N : Type} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] (n : ℕ) (a : Fin n → X → N) (ha : ∀ i, ContMDiff I J ∞ (a i)) :
    ContMDiff I J ∞ (sheetSumMap n a) := by
  induction n with
  | zero => intro x; exact x.elim
  | succ n ih => exact (ha 0).sumElim (ih (fun i => a i.succ) (fun i => ha i.succ))

private theorem Degree.MorseRearrangement.exists_sheetSumMap_for_finite_family {X : Type}
    [TopologicalSpace X] {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H X] {G K N : Type}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] {ι : Type} [Finite ι] (a : ι → X → N)
    (ha : ∀ i, ContMDiff I J ∞ (a i)) :
    ∃ (n : ℕ) (b : sheetSum X n → N), ContMDiff I J ∞ b ∧ Set.range b = ⋃ i, Set.range (a i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let a' : Fin (Fintype.card ι) → X → N := fun j => a (e.symm j)
  refine
    ⟨Fintype.card ι, sheetSumMap (Fintype.card ι) a',
      contMDiff_sheetSumMap _ a' (fun j => ha (e.symm j)), ?_⟩
  rw [range_sheetSumMap]
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨e.symm j, hj⟩
  · intro hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨e i, ?_⟩
    simpa only [a', e.symm_apply_apply] using hi

private theorem
    Degree.FlowSuspension.exists_relative_regular_level_isotopy_realization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V) {a b c : ℝ} (ha : a < c)
    (hb : c < b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hreg : ∀ y, f y = c → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (z : { y : M // f y = c }) :
    let _ := Smale.RegularLevel.chartedSpace hf hreg
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          { y : M // f y = c } { y : M // f y = c } ∞)
      (K T : Set { y : M // f y = c }),
      IsCompact K →
        Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K T →
          ∃ (r : ℝ) (C : Set M) (W V' : (y : M) → TangentSpace 𝓘(ℝ, E) y) (H G : Flow ℝ M),
            0 < r ∧
              r < c - a ∧
                IsCompact C ∧
                  C ⊆ f ⁻¹' Set.Ioo a b ∧
                    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                        (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                      (∀ y, IsMIntegralCurve (fun t => H t y) W) ∧
                        (∀ y,
                            Set.range (fun t => H t y) = Set.range (fun t => F t y) ∧
                              (∀ p,
                                  Filter.Tendsto (fun t => H t y) Filter.atTop (𝓝 p) ↔
                                    Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) ∧
                                ∀ p,
                                  Filter.Tendsto (fun t => H t y) Filter.atBot (𝓝 p) ↔
                                    Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 p)) ∧
                          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                              (fun y => (⟨y, V' y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                            (∀ y, IsMIntegralCurve (fun t => G t y) V') ∧
                              (∀ y, V' y = 0 ↔ V y = 0) ∧
                                (∀ y,
                                    y ∉ Smale.ManifoldMorse.criticalPoints E f →
                                      mvfderiv 𝓘(ℝ, E) f y (V' y) < 0) ∧
                                  (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f,
                                      ∀ᶠ x in 𝓝 y, V' x = V x) ∧
                                    (∀ y ∉ C, ∀ᶠ x in 𝓝 y, V' x = W x) ∧
                                      (∀ x : { y : M // f y = c }, G 1 x = H 1 (D x)) ∧
                                        (∀ x : { y : M // f y = c }, f (H 1 x) = c - r) ∧
                                          (∀ x : { y : M // f y = c },
                                              ∀ t : ℝ, t ≤ 0 → G t x = H t x) ∧
                                            (∀ x : { y : M // f y = c },
                                                ∀ t : ℝ, 0 ≤ t → G t (H 1 x) = H t (H 1 x)) ∧
                                              ∀ x ∈ T, ∀ t : ℝ, G t x = H t x := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  dsimp only
  intro D K T hK I
  obtain
    ⟨r, W, H, A, hr, hrbound, hW, hH, hWzero, hWneg, hWgerm, hgeometry, hsource, -, hformula,
      hheight, hmodel⟩ :=
    Degree.FlowTimeChange.exists_normalized_whole_level_cylinder hf hV hdesc F hF ha hb hband hreg
      z
  obtain
    ⟨C, V', G, Ψ, hC, hCsub, hV', hG, hzero, hneg, hgerm, -, -, hfull, hend, hfixed, -, hleft,
      hright, -⟩ :=
    exists_native_whole_level_holonomy A hsource hf hr (fun p hp => hheight p ⟨hp.1.le, hp.2.le⟩)
      W hW hmodel H hH D hK I
  have hCband : C ⊆ f ⁻¹' Set.Ioo a b := by
    intro y hy
    have hh := (hCsub hy).2
    change f y ∈ Set.Ioo (c - r) c at hh
    exact ⟨by linarith [hh.1], lt_trans hh.2 hb⟩
  have hcritical (y : M) (hy : y ∈ Smale.ManifoldMorse.criticalPoints E f) :
    ∀ᶠ x in 𝓝 y, V' x = V x := by
    have hout : y ∉ C := fun hc => hband y ⟨(hCband hc).1.le, (hCband hc).2.le⟩ hy
    filter_upwards [hgerm y hout, hWgerm y hy] with x hx hx'
    exact hx.trans hx'
  obtain ⟨htailLeft, htailRight⟩ :=
    native_whole_level_exterior_tails A Subtype.val H G hformula D Ψ hleft hright hfull
  have hA0 (x : { y : M // f y = c }) : A (x, 0) = (x : M) := by rw [hformula, H.map_zero_apply]
  have hA1 (x : { y : M // f y = c }) : A (x, 1) = H 1 x := hformula (x, 1)
  refine
    ⟨r, C, W, V', H, G, hr, hrbound, hC, hCband, hW, hH, hgeometry, hV', hG, fun y =>
      (hzero y).trans (hWzero y), fun y hy => hneg y (hWneg y hy), hcritical, hgerm, ?_, ?_, ?_,
      ?_, ?_⟩
  · intro x
    rw [← hA0 x, hend, hA1]
  · intro x
    have hh := hheight (x, 1) (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    rw [hA1, mul_one] at hh
    exact hh
  · intro x t ht
    simpa only [hA0] using htailLeft x t ht
  · intro x t ht
    simpa only [hA1] using htailRight x t ht
  · intro x hx t
    have hh := hfixed x hx 0 t
    rw [hA0, zero_add, hformula] at hh
    exact hh

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_morseSurgeryData_of_field_germ_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hunique : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x = f p → x = p)
    (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : Smale.ManifoldMorse.MorseSurgeryData E f p,
      d.radius < ε ∧
        d.chart = c ∧
          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
              f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p) ∧
            ∀ z,
              z ∈
                  Metric.closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
                    Metric.closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) →
                ∀ᶠ x in 𝓝 (d.chart.splitChart.symm z), V x = d.chart.descentField x := by
  obtain ⟨ρ, hρ, hρε, W, hW, -, heqW, hblockW, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock_lt hfinite hunique V heq hε
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hmodel :
    ∀ z,
      z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) →
        ∀ᶠ x in 𝓝 (c.splitChart.symm z), V x = c.descentField x := by
    intro z hz
    filter_upwards [hW.mem_nhds (hblockW hz).2] with x hx
    exact heqW x hx
  have hagreement :
    ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    exact hmodel _ (Smale.MorseHandle.modelMap_mem_product hρ z)
  obtain ⟨e, hfront, hfixed, horbit⟩ :=
    c.exists_attachingUnionHomeomorph_with_level_and_orbits hf hV hzero hdesc F hF ρ hρ hblock
      hagreement hband
  have hregular (b : ℝ) (hb : b ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p) (x : M)
    (hx : f x = b) : x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro hcrit
    exact hne (hx.symm.trans (congrArg f (hband x hcrit (hx ▸ hb))))
  have hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f :=
    hregular _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f :=
    hregular _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f p - ρ ^ 2 := by
    intro x hx t ht
    have hh :=
      Smale.FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp)) F hF hzero hdesc
        (hlower x hx) ht
    simpa only [F.map_zero_apply, hx] using hh
  have hlevel :=
    Smale.FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F
      (Smale.FlowConstruction.antitone_flow_height hf F hF hzero hdesc) hbottom
  have horbits :=
    c.followsModelBoundaryOrbits_of_flow (hV.of_le (by simp)) F hF ρ hρ hblock (e := e) (horbit :=
      horbit) hmodel
  exact
    ⟨{  radius := ρ
        radius_pos := hρ
        chart := c
        block := hblock
        attachmentHomeomorph := e
        attachment_frontier := hfront
        attachment_fixed := hfixed
        attachment_model_orbits := horbits
        surgery := c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e hfront
        oldExterior_eq := fun _ => rfl
        newExterior_eq := fun _ => rfl
        oldPiece_eq := fun _ => rfl
        newPiece_eq := fun _ => rfl
        belt_eq := c.beltSphere_eq_beltCoreMap hf.continuous ρ hρ hblock hlevel e hfront hfixed
        lower_regular := hlower
        upper_regular := hupper }, hρε, rfl, hband, hmodel⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_adapted_windows_with_prescribed_flow {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (c :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        Smale.ManifoldMorse.SignedMorseChart (E := E) f p.val)
    (hmodel :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 p.val, V x = (c p).descentField x) :
    ∃ S : AdaptedWindows E f, S.field = V ∧ S.flow = F ∧ ∀ p, (S.data p).chart = c p := by
  have hfinite := Smale.ManifoldMorse.finite_criticalPoints hf hm
  obtain ⟨r, hr, hgap⟩ := Smale.ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex (p : Smale.ManifoldMorse.criticalPoints E f) :=
    exists_morseSurgeryData_of_field_germ_lt hf hfinite hV F hF hzero hdesc (c p)
      (fun x hx hfx => hinj hx p.property hfx) (hmodel p) (hr p)
  choose d hd hchart hisolated hgerm using hex
  have hseparated (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + (d p).radius ^ 2 < f q - (d q).radius ^ 2 := by
    have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hd p)) (add_pos (hr p) (d p).radius_pos)]
    have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hd q)) (add_pos (hr q) (d q).radius_pos)]
    linarith [hgap p q hpq]
  exact
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := hseparated
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hgerm }, rfl, rfl, hchart⟩

private theorem
    AdaptedWindows.exists_embedded_level_transport {E M G H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace X]
    [ChartedSpace H X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (γ : C(X, { x : M // f x = a })) (x₀ : X) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    let _ := Smale.RegularLevel.chartedSpace hf hb
    ContMDiff J 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv J 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          (∀ z, (γ z).val ∈ Degree.FlowCancellation.levelBasin S.flow f b) →
            ∃ D :
              PartialDiffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
                { x : M // f x = a } { x : M // f x = b } ∞,
              D.source = {x | x.val ∈ Degree.FlowCancellation.levelBasin S.flow f b} ∧
                D.target = {y | y.val ∈ Degree.FlowCancellation.levelBasin S.flow f a} ∧
                  ∃ Γ : C(X, { x : M // f x = b }),
                    ContMDiff J 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ Γ ∧
                      Function.Injective Γ ∧
                        (∀ z,
                            Function.Injective (mfderiv J 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z)) ∧
                          (∀ z, D (γ z) = Γ z) ∧
                            (∀ z, D.symm (Γ z) = γ z) ∧
                              ∀ z, ∃ t : ℝ, S.flow t (γ z).val = (Γ z).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  let _ := Smale.RegularLevel.isManifold hf ha
  let _ := Smale.RegularLevel.isManifold hf hb
  change
    ContMDiff J 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv J 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          (∀ z, (γ z).val ∈ Degree.FlowCancellation.levelBasin S.flow f b) → _
  intro hγ hγi hγd hreach
  obtain ⟨t, ht⟩ := hreach x₀
  let zb : { x : M // f x = b } := ⟨S.flow t (γ x₀).val, ht⟩
  obtain ⟨D, hsource, htarget, horbit⟩ := S.exists_native_level_basin_transport hf ha hb (γ x₀) zb
  have hmaps (z : X) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hDγ : ContMDiff J 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (D ∘ γ) := by
    intro z
    exact
      (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hmaps z))).comp z hγ.contMDiffAt
  let Γ : C(X, { x : M // f x = b }) := ⟨D ∘ γ, hDγ.continuous⟩
  have hΓi : Function.Injective Γ := by
    intro x y hxy
    exact hγi (D.toPartialEquiv.injOn (hmaps x) (hmaps y) hxy)
  have hΓd : ∀ z, Function.Injective (mfderiv J 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z) := by
    intro z
    change Function.Injective (mfderiv J 𝓘(ℝ, Smale.RegularLevel.Model E) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hmaps z)) (hγ.mdifferentiableAt (by simp))]
    exact (Smale.PartialChart.bijective_mfderiv D (hmaps z)).1.comp (hγd z)
  refine ⟨D, hsource, htarget, Γ, hDγ, hΓi, hΓd, fun _ => rfl, ?_, ?_⟩
  · intro z
    exact D.left_inv' (hmaps z)
  · intro z
    exact horbit (γ z) (hmaps z)

private def MorseCancel.standardCircleParametrization :
    Diffeomorph (𝓡 1) (𝓡 1) (Smale.Hemisphere.Sphere 1) Circle ∞ := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  exact Smale.SphereCoordinates.standardParametrization ℂ 1

private theorem MorseCancel.contMDiff_comp_standardCircle {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff (𝓡 1) J ∞ γ) :
    ContMDiff (𝓡 1) J ∞ (γ ∘ standardCircleParametrization) :=
  hγ.comp standardCircleParametrization.contMDiff

private theorem MorseCancel.injective_comp_standardCircle {N : Type*}
    {γ : Circle → N} (hγ : Function.Injective γ) :
    Function.Injective (γ ∘ standardCircleParametrization) :=
  hγ.comp standardCircleParametrization.injective

private theorem MorseCancel.injective_derivative_comp_standardCircle {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff (𝓡 1) J ∞ γ)
    (hi : ∀ z, Function.Injective (mfderiv (𝓡 1) J γ z)) (z : Smale.Hemisphere.Sphere 1) :
    Function.Injective (mfderiv (𝓡 1) J (γ ∘ standardCircleParametrization) z) := by
  rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp))
      (standardCircleParametrization.contMDiff.mdifferentiableAt (by simp))]
  exact
    (hi _).comp
      (standardCircleParametrization.mfderivToContinuousLinearEquiv (by simp) z).injective

private theorem MorseCancel.transverse_comp_standardCircle {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] {γ : Circle → N}
    (hγ : ContMDiff (𝓡 1) J ∞ γ) (B : D →L[ℝ] G) (z : Smale.Hemisphere.Sphere 1)
    (htrans :
      Function.Surjective
        ((mfderiv (𝓡 1) J γ (standardCircleParametrization z) :
              EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod
          B)) :
    Function.Surjective
      ((mfderiv (𝓡 1) J (γ ∘ standardCircleParametrization) z :
            EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod
        B) := by
  let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] G := mfderiv (𝓡 1) J γ (standardCircleParametrization z)
  let P : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    mfderiv (𝓡 1) (𝓡 1) standardCircleParametrization z
  have hP : Function.Surjective P :=
    (standardCircleParametrization.mfderivToContinuousLinearEquiv (by simp) z).surjective
  rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp))
      (standardCircleParametrization.contMDiff.mdifferentiableAt (by simp))]
  change Function.Surjective ((L.comp P).coprod B)
  exact surjective_coprod_comp_left L B P hP htrans

private theorem
    AdaptedWindows.attachingSphere_reaches_lower_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) {a : ℝ}
    (hap : a < f p) (hgap : ∀ q : Smale.ManifoldMorse.criticalPoints E f, f q < f p → f q < a)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1) :
    ((S.data p).surgery.attachingSphere u).val ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  let x := (S.data p).surgery.attachingSphere u
  have hback := (S.attaching_basin_iff hf p x).mpr ⟨u, rfl⟩
  obtain ⟨r, hr, q, hq, -, hforward, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have hxreg : x.val ∉ Smale.ManifoldMorse.criticalPoints E f :=
    (S.data p).lower_regular x.val x.property
  have hxp : f x.val < f p := by
    have hh := x.property
    change f x.val = f p - (S.data p).radius ^ 2 at hh
    rw [hh]
    nlinarith [(S.data p).radius_pos]
  have hqa : f q < a := hgap ⟨q, hq⟩ ((hheights hxreg).1.trans hxp)
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward hap hqa

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.exists_attaching_circle_lower_transport {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 1 + 1)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : Smale.ManifoldMorse.criticalPoints E f, f q < f p → f q < a) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∃ e :
      Diffeomorph (𝓡 1) (𝓡 1) (Smale.Hemisphere.Sphere 1)
        (Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1) ∞,
      ∃ D :
        PartialDiffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          (S.data p).LowerLevel { y : M // f y = a } ∞,
        D.source = {x | x.val ∈ Degree.FlowCancellation.levelBasin S.flow f a} ∧
          D.target =
              {y |
                y.val ∈
                  Degree.FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p)} ∧
            ∃ Γ : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }),
              ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ Γ ∧
                Function.Injective Γ ∧
                  (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z)) ∧
                    (∀ z, D ((S.data p).surgery.attachingSphere (e z)) = Γ z) ∧
                      (∀ z, D.symm (Γ z) = (S.data p).surgery.attachingSphere (e z)) ∧
                        ∀ z,
                          ∃ t : ℝ,
                            S.flow t ((S.data p).surgery.attachingSphere (e z)).val = (Γ z).val :=
  by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.isManifold hf (S.data p).lower_regular
  let _ := Smale.RegularLevel.isManifold hf ha
  let e := Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 1
  let γ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf 1).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf 1).comp e.contMDiff
  have hγi : Function.Injective γ :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z) := by
    intro z
    change
      Function.Injective
        (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e)
          z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf 1).mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiableAt (by simp))]
    exact
      ((S.data p).attaching_derivative_injective hf 1 (e z)).comp
        (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Smale.Hemisphere.Sphere 1) :
    (γ z).val ∈ Degree.FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  obtain ⟨D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ
      (MorseCancel.standardCircleParametrization.symm (1 : Circle)) hγ hγi hγd hreach
  exact ⟨e, D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩

private theorem
    AdaptedWindows.backward_basin_reaches_attaching_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) {x : M}
    (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)) :
    x ∈ Degree.FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p) := by
  obtain ⟨r, hr, q, hq, hback', hforward, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x
  have hrp : r = p.val := tendsto_nhds_unique hback' hback
  have hqp : f q < f p := by
    have hh := (hheights hx).1.trans (hheights hx).2
    rwa [hrp] at hh
  have hqlo : f q < S.toSurgeryWindows.lower p :=
    (S.toSurgeryWindows.value_lt_upper ⟨q, hq⟩).trans (S.separated ⟨q, hq⟩ p hqp)
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward (S.toSurgeryWindows.lower_lt_value p) hqlo

private theorem AdaptedWindows.transported_attaching_range_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {X : Type*}
    (e : X → Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (he : Function.Surjective e) (Γ : X → { y : M // f y = a })
    (hflow : ∀ z, ∃ t : ℝ, S.flow t ((S.data p).surgery.attachingSphere (e z)).val = (Γ z).val)
    (y : { x : M // f x = a }) :
    y ∈ Set.range Γ ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := hflow z
    have hback :=
      (S.attaching_basin_iff hf p ((S.data p).surgery.attachingSphere (e z))).mpr ⟨e z, rfl⟩
    rw [← ht]
    exact (MorseCancel.flow_time_atBot_limit_iff S.flow t _ p.val).mpr hback
  · intro hy
    obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf p (ha y.val y.property) hy
    let x : (S.data p).LowerLevel := ⟨S.flow t y.val, ht⟩
    have hxback : Filter.Tendsto (fun s => S.flow s x.val) Filter.atBot (𝓝 p.val) :=
      (MorseCancel.flow_time_atBot_limit_iff S.flow t y.val p.val).mpr hy
    obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p x).mp hxback
    obtain ⟨z, hz⟩ := he u
    obtain ⟨s, hs⟩ := hflow z
    have hattach : S.flow t y.val = ((S.data p).surgery.attachingSphere (e z)).val := by
      rw [hz]
      exact (congrArg Subtype.val hu).symm
    have hshared : S.flow 0 (Γ z).val = S.flow (s + t) y.val := by
      rw [S.flow.map_zero_apply, S.flow.map_add, hattach, hs]
    refine ⟨z, Subtype.ext ?_⟩
    exact
      MorseCancel.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun w hw => S.descent w (ha w hw)) (Γ z).property y.property hshared

private theorem
    AdaptedWindows.forward_endpoint_of_attaching_branches {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hbranches :
      ∀ u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
          (𝓝 p.val))
    {x : M} (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val)) :
    Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val) := by
  obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf q hx hback
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Filter.Tendsto (fun s => S.flow s y.val) Filter.atBot (𝓝 q.val) :=
    (MorseCancel.flow_time_atBot_limit_iff S.flow t x q.val).mpr hback
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf q y).mp hyback
  have hyforward : Filter.Tendsto (fun s => S.flow s y.val) Filter.atTop (𝓝 p.val) := by
    rw [← hu]
    exact hbranches u
  exact (MorseCancel.flow_time_atTop_limit_iff S.flow t x p.val).mp hyforward

private theorem AdaptedWindows.attaching_branches_of_same_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hflow : T.flow = S.flow)
    (hbranches :
      ∀ u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
          (𝓝 p.val)) :
    ∀ u : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
      Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val) := by
  intro u
  let x := (T.data q).surgery.attachingSphere u
  have hback := (T.attaching_basin_iff hf q x).mpr ⟨u, rfl⟩
  rw [hflow] at hback ⊢
  exact
    S.forward_endpoint_of_attaching_branches hf p q hbranches
      ((T.data q).lower_regular x.val x.property) hback

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_adapted_windows_with_prescribed_flow_lt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (c :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        Smale.ManifoldMorse.SignedMorseChart (E := E) f p.val)
    (hmodel :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 p.val, V x = (c p).descentField x)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    ∃ S : AdaptedWindows E f,
      S.field = V ∧ S.flow = F ∧ (∀ p, (S.data p).chart = c p) ∧ ∀ p, (S.data p).radius < ε p := by
  have hfinite := Smale.ManifoldMorse.finite_criticalPoints hf hm
  obtain ⟨r, hr, hgap⟩ := Smale.ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex (p : Smale.ManifoldMorse.criticalPoints E f) :=
    exists_morseSurgeryData_of_field_germ_lt hf hfinite hV F hF hzero hdesc (c p)
      (fun x hx hfx => hinj hx p.property hfx) (hmodel p) (lt_min (hr p) (hε p))
  choose d hd hchart hisolated hgerm using hex
  have hdr (p : Smale.ManifoldMorse.criticalPoints E f) : (d p).radius < r p :=
    (hd p).trans_le (min_le_left _ _)
  have hde (p : Smale.ManifoldMorse.criticalPoints E f) : (d p).radius < ε p :=
    (hd p).trans_le (min_le_right _ _)
  have hseparated (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + (d p).radius ^ 2 < f q - (d q).radius ^ 2 := by
    have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hdr p)) (add_pos (hr p) (d p).radius_pos)]
    have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hdr q)) (add_pos (hr q) (d q).radius_pos)]
    linarith [hgap p q hpq]
  exact
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := hseparated
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hgerm }, rfl, rfl, hchart, hde⟩

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.exists_same_flow_windows_avoiding_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ T : AdaptedWindows E f,
      T.field = S.field ∧
        T.flow = S.flow ∧
          (∀ p, (T.data p).chart = (S.data p).chart) ∧
            (∀ p : Smale.ManifoldMorse.criticalPoints E f,
                f p < a → T.toSurgeryWindows.upper p < a) ∧
              ∀ p : Smale.ManifoldMorse.criticalPoints E f,
                a < f p → a < T.toSurgeryWindows.lower p := by
  let ε : Smale.ManifoldMorse.criticalPoints E f → ℝ := fun p => Real.sqrt |f p - a|
  have hε (p : Smale.ManifoldMorse.criticalPoints E f) : 0 < ε p := by
    apply Real.sqrt_pos.mpr
    exact abs_pos.mpr (sub_ne_zero.mpr (fun h => ha p.val h p.property))
  obtain ⟨T, hfield, hflow, hcharts, hsmall⟩ :=
    MorseCancel.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct S.smooth S.flow
      S.integral S.zero S.descent (fun p => (S.data p).chart) S.critical_model_germ ε hε
  have hsq (p : Smale.ManifoldMorse.criticalPoints E f) : (T.data p).radius ^ 2 < |f p - a| := by
    have hp := mul_pos (sub_pos.mpr (hsmall p)) (add_pos (hε p) (T.data p).radius_pos)
    have heq : (ε p) ^ 2 = |f p - a| := Real.sq_sqrt (abs_nonneg _)
    nlinarith
  refine ⟨T, hfield, hflow, hcharts, ?_, ?_⟩
  · intro p hp
    have hh := hsq p
    rw [abs_of_neg (sub_neg.mpr hp)] at hh
    change f p + (T.data p).radius ^ 2 < a
    linarith
  · intro p hp
    have hh := hsq p
    rw [abs_of_pos (sub_pos.mpr hp)] at hh
    change a < f p - (T.data p).radius ^ 2
    linarith

private theorem AdaptedWindows.regular_interval_around_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    {a : ℝ} (hreg : ∀ x, f x = a → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ l u : ℝ,
      l < a ∧ a < u ∧ ∀ x, f x ∈ Set.Icc l u → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
  have ha : a ∉ f '' Smale.ManifoldMorse.criticalPoints E f := by
    rintro ⟨x, hx, hfx⟩
    exact hreg x hfx hx
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp ((S.finite.image f).isClosed.isOpen_compl.mem_nhds ha)
  refine ⟨a - ε / 2, a + ε / 2, by linarith, by linarith, ?_⟩
  intro x hx hcrit
  have hh : f x ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact hball hh ⟨x, hcrit, rfl⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    AdaptedWindows.realize_one_handle_minimum_branches {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (hone : MorseCancel.nativeMorseIndex E f q = 1)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v)) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M) (p r :
      Smale.ManifoldMorse.criticalPoints E f),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, V y = S.field y) ∧
                MorseCancel.nativeMorseIndex E f p = 0 ∧
                  MorseCancel.nativeMorseIndex E f r = 0 ∧
                    p ≠ r ∧
                      f p < S.toSurgeryWindows.lower q ∧
                        f r < S.toSurgeryWindows.lower q ∧
                          (∀ x : (S.data q).LowerLevel,
                              Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
                                x ∈ Set.range (S.data q).surgery.attachingSphere) ∧
                            Filter.Tendsto
                                (fun t => G t ((S.data q).surgery.attachingSphere u).val)
                                Filter.atTop (𝓝 p.val) ∧
                              Filter.Tendsto
                                  (fun t => G t ((S.data q).surgery.attachingSphere v).val)
                                  Filter.atTop (𝓝 r.val) ∧
                                (∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
                                    Filter.Tendsto
                                        (fun t => G t ((S.data q).surgery.attachingSphere w).val)
                                        Filter.atTop (𝓝 p.val) ∨
                                      Filter.Tendsto
                                        (fun t => G t ((S.data q).surgery.attachingSphere w).val)
                                        Filter.atTop (𝓝 r.val)) ∧
                                  ∀ j : Smale.ManifoldMorse.criticalPoints E f,
                                    j ≠ q →
                                      j ≠ p →
                                        j ≠ r →
                                          ∀ x,
                                            ¬(Filter.Tendsto (fun t => G t x) Filter.atBot
                                                  (𝓝 q.val) ∧
                                                Filter.Tendsto (fun t => G t x) Filter.atTop
                                                  (𝓝 j.val)) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨d, hd, p, r, hp, hr, hpr, hpq, hrq, hpu, hrv, hall⟩ :=
    S.place_one_handle_in_distinct_minimum_basins hf q hone u v hnot
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level (S.data q).lower_regular
  obtain
    ⟨ρ, C, W, V, H, G, hρ, hρbound, hC, hCband, hW, hH, hgeometry, hV, hG, hzero, hdesc, hgerms,
      houtside, hend, hheight, hleft, hright⟩ :=
    Degree.FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) d hd
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val d
      (fun x z => (hgeometry x).2.1 z) (fun x z => (hgeometry x).2.2 z) hend hleft hright
  have hbq (x : (S.data q).LowerLevel) :
    Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
      x ∈ Set.range (S.data q).surgery.attachingSphere :=
    (hback x q.val).trans (S.attaching_basin_iff hf q x)
  have hends (w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
        (𝓝 p.val) ∨
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
        (𝓝 r.val) :=
    (hall w).imp ((hforward _ p.val).mpr) ((hforward _ r.val).mpr)
  refine
    ⟨V, G, p, r, hV, hG, (fun x hx => (hzero x).mpr (S.zero x hx)), hdesc, hgerms, hp, hr, hpr,
      hpq, hrq, hbq, (hforward _ p.val).mpr hpu, (hforward _ r.val).mpr hrv, hends, ?_⟩
  intro j hjq hjp hjr x hx
  have hmono :=
    Smale.FlowConstruction.antitone_flow_height hf G hG (fun y hy => (hzero y).mpr (S.zero y hy))
      hdesc x
  have hforwardHeight := hf.continuous.continuousAt.tendsto.comp hx.2
  have hbackwardHeight := hf.continuous.continuousAt.tendsto.comp hx.1
  have hle : f j ≤ f q :=
    (hmono.le_of_tendsto hforwardHeight 0).trans (hmono.ge_of_tendsto hbackwardHeight 0)
  have hjq' : f j < f q :=
    lt_of_le_of_ne hle (fun h => hjq (Subtype.ext (S.distinct j.property q.property h)))
  have hjlow : f j < S.toSurgeryWindows.lower q :=
    (S.toSurgeryWindows.value_lt_upper j).trans (S.separated j q hjq')
  obtain ⟨t, ht⟩ :=
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits G hf.continuous hx.1 hx.2
      (S.toSurgeryWindows.lower_lt_value q) hjlow
  let z : (S.data q).LowerLevel := ⟨G t x, ht⟩
  have hzq : Filter.Tendsto (fun s => G s z) Filter.atBot (𝓝 q.val) :=
    (MorseCancel.flow_time_atBot_limit_iff G t x q.val).mpr hx.1
  have hzj : Filter.Tendsto (fun s => G s z) Filter.atTop (𝓝 j.val) :=
    (MorseCancel.flow_time_atTop_limit_iff G t x j.val).mpr hx.2
  obtain ⟨w, hw⟩ := (hbq z).mp hzq
  have hh := hends w
  rw [hw] at hh
  rcases hh with hp' | hr'
  · exact hjp (Subtype.ext (tendsto_nhds_unique hzj hp'))
  · exact hjr (Subtype.ext (tendsto_nhds_unique hzj hr'))

private theorem
    AdaptedWindows.exists_relative_level_surgery_system {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f) {c : ℝ}
    (hc : ∀ y, f y = c → y ∉ Smale.ManifoldMorse.criticalPoints E f) (z : { y : M // f y = c })
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    let _ := Smale.RegularLevel.chartedSpace hf hc
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          { y : M // f y = c } { y : M // f y = c } ∞)
      (K P : Set { y : M // f y = c }),
      IsCompact K →
        Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K P →
          ∃ T : AdaptedWindows E f,
            (∀ p, (T.data p).chart = (S.data p).chart) ∧
              (∀ p, (T.data p).radius < ε p) ∧
                (∀ p ∈ Smale.ManifoldMorse.criticalPoints E f,
                    ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
                  (∀ x : { y : M // f y = c },
                      ∀ p : M,
                        Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p) ↔
                          Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p)) ∧
                    (∀ x : { y : M // f y = c },
                        ∀ p : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
                            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p)) ∧
                      ∀ x ∈ P,
                        Set.range (fun t => T.flow t x.val) =
                          Set.range (fun t => S.flow t x.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf hc
  dsimp only
  intro D K P hK I
  obtain ⟨a, b, ha, hb, hband⟩ := S.regular_interval_around_level hc
  obtain
    ⟨_, _, _, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright, hprotected⟩ :=
    Degree.FlowSuspension.exists_relative_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral ha hb hband hc z D K P hK I
  have hmodel (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p.val p.property, S.critical_model_germ p] with y hy hys
    exact hy.trans hys
  obtain ⟨T, hfield, hflow, hcharts, hradii⟩ :=
    MorseCancel.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct hV G hG
      (fun y hy => (hzero y).mpr (S.zero y hy)) hdesc (fun p => (S.data p).chart) hmodel ε hε
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val D
      (fun x p => (hgeometry x).2.1 p) (fun x p => (hgeometry x).2.2 p) hend hleft hright
  refine ⟨T, hcharts, hradii, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hfield]
    exact hgerms p hp
  · intro x p
    rw [hflow]
    exact hback x p
  · intro x p
    rw [hflow]
    exact hforward x p
  · intro x hx
    rw [hflow]
    have heq : (fun t => G t x.val) = (fun t => H t x.val) := funext (fun t => hprotected x hx t)
    rw [heq]
    exact (hgeometry x.val).1

private theorem AdaptedWindows.exists_native_family_level_transport {ι E M F H X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) (za : { x : M // f x = a })
    (zb : { x : M // f x = b }) (α : ι → X → { x : M // f x = a }) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    let _ := Smale.RegularLevel.chartedSpace hf hb
    (∀ j, ContMDiff I 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv I 𝓘(ℝ, Smale.RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            (∀ j x, (α j x).val ∈ Degree.FlowCancellation.levelBasin S.flow f b) →
              ∃ β : ι → X → { x : M // f x = b },
                (∀ j, ContMDiff I 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (β j)) ∧
                  (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                    (∀ j x,
                        Function.Injective (mfderiv I 𝓘(ℝ, Smale.RegularLevel.Model E) (β j) x)) ∧
                      Pairwise (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  let _ := Smale.RegularLevel.isManifold hf ha
  let _ := Smale.RegularLevel.isManifold hf hb
  dsimp only
  intro hα hαinj hαimm hpair hreach
  obtain ⟨P, hsource, -, horbit⟩ := S.exists_native_level_basin_transport hf ha hb za zb
  have hsrc (j : ι) (x : X) : α j x ∈ P.source := by
    rw [hsource]
    exact hreach j x
  let β : ι → X → { x : M // f x = b } := fun j => P ∘ α j
  have hβ (j : ι) : ContMDiff I 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (β j) := by
    intro x
    exact
      (P.contMDiffOn_toFun.contMDiffAt (P.open_source.mem_nhds (hsrc j x))).comp x
        (hα j).contMDiffAt
  have hinj (j : ι) : Function.Injective (β j) := by
    intro x y hxy
    exact hαinj j (P.toPartialEquiv.injOn (hsrc j x) (hsrc j y) hxy)
  refine
    ⟨β, hβ, fun j => (hβ j).continuous.isClosedEmbedding (hinj j), ?_, ?_, fun j x =>
      horbit (α j x) (hsrc j x)⟩
  · intro j x
    have hP := P.contMDiffOn_toFun.contMDiffAt (P.open_source.mem_nhds (hsrc j x))
    change Function.Injective (mfderiv I 𝓘(ℝ, Smale.RegularLevel.Model E) (P ∘ α j) x)
    rw [mfderiv_comp x (hP.mdifferentiableAt (by simp)) ((hα j).mdifferentiableAt (by simp))]
    exact (Smale.PartialChart.bijective_mfderiv P (hsrc j x)).injective.comp (hαimm j x)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hiz hjz
    obtain ⟨x, hx⟩ := hiz
    obtain ⟨y, hy⟩ := hjz
    have heq : α i x = α j y := P.toPartialEquiv.injOn (hsrc i x) (hsrc j y) (hx.trans hy.symm)
    exact Set.disjoint_left.mp (hpair hij) (Set.mem_range_self x) ⟨y, heq.symm⟩

private theorem AdaptedWindows.reaches_lower_of_excluded_critical_limit {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) (p : M)
    (hwindow : ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f, f q ∈ Set.Icc a b → q = p)
    (x : { y : M // f y = b })
    (hexcluded : ¬Filter.Tendsto (fun t => S.flow t x.val) Filter.atTop (𝓝 p)) :
    x.val ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  obtain ⟨q, hq, r, hr, hback, hforward, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have hregular := hb x.val x.property
  have hbelow : f r < a := by
    by_contra h
    have hrb : f r < b := by simpa only [x.property] using (hheights hregular).1
    have heq := hwindow r hr ⟨le_of_not_gt h, hrb.le⟩
    exact hexcluded (heq ▸ hforward)
  have habove : a < f q := by
    have hbq : b < f q := by simpa only [x.property] using (hheights hregular).2
    exact hab.trans hbq
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward habove hbelow

private theorem
    AdaptedWindows.reaches_old_lower_of_belt_avoidance {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (D : (S.data p).UpperLevel → (S.data p).UpperLevel)
    (hforward :
      ∀ x : (S.data p).UpperLevel,
        ∀ q : M,
          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 q) ↔
            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 q))
    (x : (S.data p).UpperLevel) (hx : D x ∉ Set.range (S.data p).surgery.beltSphere) :
    x.val ∈ Degree.FlowCancellation.levelBasin T.flow f (S.toSurgeryWindows.lower p) := by
  apply
    T.reaches_lower_of_excluded_critical_limit hf
      ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p))
      (S.data p).upper_regular p.val (S.isolated p) x
  intro h
  exact hx ((S.belt_basin_iff hf p (D x)).mp ((hforward x p.val).mp h))

private theorem
    Degree.MorseRearrangement.exists_whole_family_avoidance {ι D Z G H H' K X Y N : Type}
    [Finite ι] [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] (a : ι → X → N)
    (ha : ∀ j, ContMDiff I J ∞ (a j)) {g : Y → N} (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) {C : Set N}
    (hC : IsClosed C) (haC : ∀ j, Disjoint (Set.range (a j)) C) :
    ∃ (e : Diffeomorph J J N N ∞) (K : Set N),
      IsCompact K ∧
        K ⊆ Cᶜ ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K C) ∧
            ∀ j, Disjoint (Set.range (e ∘ a j)) (Set.range g) := by
  obtain ⟨n, b, hb, hbrange⟩ := exists_sheetSumMap_for_finite_family a ha
  have hbC : Disjoint (Set.range b) C := by
    apply Set.disjoint_left.mpr
    intro z hz hzC
    rw [hbrange] at hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    exact Set.disjoint_left.mp (haC j) hj hzC
  obtain ⟨e, K, hK, hKC, hIso, hdisj⟩ :=
    exists_supported_ambient_disjoint_fixing_closed hb hg hdim hC hbC
  refine ⟨e, K, hK, hKC, hIso, ?_⟩
  intro j
  apply Set.disjoint_left.mpr
  intro z hz hzg
  obtain ⟨x, hx⟩ := hz
  have hx' : a j x ∈ Set.range b := by
    rw [hbrange]
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_range_self x⟩
  obtain ⟨w, hw⟩ := hx'
  apply Set.disjoint_left.mp hdisj _ hzg
  refine ⟨w, ?_⟩
  change e (b w) = z
  rw [hw]
  exact hx

private theorem AdaptedWindows.exists_middle_family_descent {ι E M : Type} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (p : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancel.nativeMorseIndex E f p = 3)
    (α : ι → (Smale.Hemisphere.Sphere 2) → (S.data p).UpperLevel) {P : Set (S.data p).UpperLevel}
    (hP : IsClosed P) (hαP : ∀ j, Disjoint (Set.range (α j)) P)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ T : AdaptedWindows E f,
              (∀ q, (T.data q).chart = (S.data q).chart) ∧
                (∀ q, (T.data q).radius < ε q) ∧
                  (∀ q ∈ Smale.ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
                    (∀ x : (S.data p).UpperLevel,
                        ∀ q : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 q) ↔
                            Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        ∃ β : ι → (Smale.Hemisphere.Sphere 2) → (S.data p).LowerLevel,
                          (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (β j)) ∧
                            (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                              (∀ j x,
                                  Function.Injective
                                    (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (β j) x)) ∧
                                Pairwise
                                    (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                                  (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (β j x).val) ∧
                                    ∀ j x q,
                                      Filter.Tendsto (fun t => T.flow t (β j x).val) Filter.atBot
                                          (𝓝 q) ↔
                                        Filter.Tendsto (fun t => S.flow t (α j x).val)
                                          Filter.atBot (𝓝 q) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by
      have hs := (S.data p).chart.finrank_negative_add_positive
      have hn := (MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
      omega⟩
  dsimp only
  intro hα hαinj hαimm hpair
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) <
      Module.finrank ℝ (Smale.RegularLevel.Model E) := by simp [Smale.RegularLevel.Model, hdim]
  obtain ⟨D, K, hK, -, ⟨A⟩, havoid⟩ :=
    Degree.MorseRearrangement.exists_whole_family_avoidance α hα ((S.data p).belt_smooth hf 2)
      hdim' hP hαP
  let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp []⟩
  let u :=
    Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2 x₀
  let v :=
    Smale.SphereCoordinates.standardParametrization (S.data p).chart.PositiveCoordinates 2 x₀
  obtain ⟨T, hcharts, hradii, hgerms, hback, hforward, hprotected⟩ :=
    S.exists_relative_level_surgery_system hf hm (S.data p).upper_regular
      ((S.data p).surgery.beltSphere v) ε hε D K P hK A
  have hreach (j : ι) (x : (Smale.Hemisphere.Sphere 2)) :
    (α j x).val ∈ Degree.FlowCancellation.levelBasin T.flow f (S.toSurgeryWindows.lower p) := by
    apply S.reaches_old_lower_of_belt_avoidance T hf p D hforward (α j x)
    intro hx
    exact Set.disjoint_left.mp (havoid j) ⟨x, rfl⟩ hx
  obtain ⟨β, hβ, hβe, hβi, hβpair, horbit⟩ :=
    T.exists_native_family_level_transport hf (S.data p).upper_regular (S.data p).lower_regular
      ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u) α hα hαinj hαimm
      hpair hreach
  refine ⟨T, hcharts, hradii, hgerms, hback, hprotected, β, hβ, hβe, hβi, hβpair, horbit, ?_⟩
  intro j x q
  obtain ⟨t, ht⟩ := horbit j x
  rw [← ht]
  exact (MorseCancel.flow_time_atBot_limit_iff T.flow t (α j x).val q).trans (hback (α j x) q)

private theorem AdaptedWindows.exists_native_attaching_lower_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = n + 1)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : Smale.ManifoldMorse.criticalPoints E f, f q < f p → f q < a) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∃ Γ : C(Smale.Hemisphere.Sphere n, { y : M // f y = a }),
      ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ Γ ∧
        Topology.IsClosedEmbedding Γ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z)) ∧
            (∀ z,
                ∃ t : ℝ,
                  S.flow t
                      ((S.data p).surgery.attachingSphere
                          (Smale.SphereCoordinates.standardParametrization
                            (S.data p).chart.NegativeCoordinates n z)).val =
                    (Γ z).val) ∧
              ∀ y : { x : M // f x = a },
                y ∈ Set.range Γ ↔
                  Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let e := Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates n
  let γ : C(Smale.Hemisphere.Sphere n, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf n).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf n).comp e.contMDiff
  have hγi : Function.Injective γ :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z) := by
    intro z
    change
      Function.Injective
        (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e)
          z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf n).mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiableAt (by simp))]
    exact
      ((S.data p).attaching_derivative_injective hf n (e z)).comp
        (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Smale.Hemisphere.Sphere n) :
    (γ z).val ∈ Degree.FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  let x₀ : Smale.Hemisphere.Sphere n := Smale.Hemisphere.point Bool.true ⟨0, by simp []⟩
  obtain ⟨D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ x₀ hγ hγi hγd hreach
  refine ⟨Γ, hΓ, hΓ.continuous.isClosedEmbedding hΓi, hΓd, hflow, ?_⟩
  intro y
  exact S.transported_attaching_range_iff hf p ha e e.surjective Γ hflow y

private theorem AdaptedWindows.not_backward_basin_on_upper_level {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (x : (S.data p).UpperLevel) :
    ¬Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) := by
  intro hx
  obtain ⟨q, hq, r, hr, hback, _, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have heq : q = p.val := tendsto_nhds_unique hback hx
  have hh := (hheights ((S.data p).upper_regular x.val x.property)).2
  rw [heq, x.property] at hh
  exact (not_lt_of_ge (S.toSurgeryWindows.value_lt_upper p).le) hh

private theorem
    AdaptedWindows.transported_backward_basin_image {E M X : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) (p : M) (hap : a < f p)
    (α : X → { y : M // f y = a }) (β : X → { y : M // f y = b })
    (hα :
      ∀ x : { y : M // f y = a },
        x ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p))
    (horbit : ∀ z, ∃ t : ℝ, S.flow t (α z).val = (β z).val) :
    ∀ y : { x : M // f x = b },
      y ∈ Set.range β ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p) := by
  intro y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := horbit z
    rw [← ht]
    exact
      (MorseCancel.flow_time_atBot_limit_iff S.flow t (α z).val p).mpr
        ((hα (α z)).mp (Set.mem_range_self z))
  · intro hy
    obtain ⟨q, hq, r, hr, _, hforward, hheights⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct y.val
    have hrb : f r < b := by simpa only [y.property] using (hheights (hb y.val y.property)).1
    obtain ⟨s, hs⟩ :=
      Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hy
        hforward hap (hrb.trans hab)
    let x : { z : M // f z = a } := ⟨S.flow s y.val, hs⟩
    have hx : Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p) :=
      (MorseCancel.flow_time_atBot_limit_iff S.flow s y.val p).mpr hy
    obtain ⟨z, hz⟩ := (hα x).mpr hx
    obtain ⟨t, ht⟩ := horbit z
    have hshared : S.flow 0 (β z).val = S.flow (t + s) y.val := by
      rw [S.flow.map_zero_apply, ← ht, hz]
      exact (S.flow.map_add t s y.val).symm
    refine ⟨z, Subtype.ext ?_⟩
    exact
      MorseCancel.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (hb z hz)) (β z).property y.property hshared

private def MorseCancel.nativeIndexThreeAttachingSphere {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : nativeMorseIndex E f p = 3) : C((Smale.Hemisphere.Sphere 2), (S.data p).LowerLevel) := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  exact
    (S.data p).surgery.attachingSphere.comp
      ((Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
            2).toHomeomorph :
        C((Smale.Hemisphere.Sphere 2),
          Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1))

private theorem AdaptedWindows.exists_middle_family_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) (n : ℕ)
    (α : Fin n → (Smale.Hemisphere.Sphere 2) → (S.data p).UpperLevel)
    {P : Set (S.data p).UpperLevel} (hP : IsClosed P) (hαP : ∀ j, Disjoint (Set.range (α j)) P)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ T : AdaptedWindows E f,
              (∀ q, (T.data q).chart = (S.data q).chart) ∧
                (∀ q, (T.data q).radius < ε q) ∧
                  (∀ q ∈ Smale.ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
                    (∀ x : (S.data p).UpperLevel,
                        ∀ q : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 q) ↔
                            Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        ∃ Γ : Fin (n + 1) → (Smale.Hemisphere.Sphere 2) → (S.data p).LowerLevel,
                          (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (Γ j)) ∧
                            (∀ j, Topology.IsClosedEmbedding (Γ j)) ∧
                              (∀ j x,
                                  Function.Injective
                                    (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (Γ j) x)) ∧
                                Pairwise
                                    (fun i j => Disjoint (Set.range (Γ i)) (Set.range (Γ j))) ∧
                                  (∀ x,
                                      ∃ t : ℝ,
                                        T.flow t
                                            (MorseCancel.nativeIndexThreeAttachingSphere T p hp
                                                x).val =
                                          (Γ 0 x).val) ∧
                                    (∀ y : (S.data p).LowerLevel,
                                        y ∈ Set.range (Γ 0) ↔
                                          Filter.Tendsto (fun t => T.flow t y.val) Filter.atBot
                                            (𝓝 p.val)) ∧
                                      (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (Γ j.succ x).val) ∧
                                        (∀ j x q,
                                            Filter.Tendsto (fun t => T.flow t (Γ j.succ x).val)
                                                Filter.atBot (𝓝 q) ↔
                                              Filter.Tendsto (fun t => S.flow t (α j x).val)
                                                Filter.atBot (𝓝 q)) ∧
                                          ∀ j q,
                                            S.toSurgeryWindows.upper p < f q →
                                              (∀ x : (S.data p).UpperLevel,
                                                  x ∈ Set.range (α j) ↔
                                                    Filter.Tendsto (fun t => S.flow t x.val)
                                                      Filter.atBot (𝓝 q)) →
                                                ∀ y : (S.data p).LowerLevel,
                                                  y ∈ Set.range (Γ j.succ) ↔
                                                    Filter.Tendsto (fun t => T.flow t y.val)
                                                      Filter.atBot (𝓝 q) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  dsimp only
  intro hα hαinj hαimm hpair
  obtain
    ⟨T, hcharts, hradii, hgerms, hback, hprotected, β, hβ, hβe, hβi, hβpair, horbit, hlabels⟩ :=
    S.exists_middle_family_descent hf hm hdim p hp α hP hαP ε hε hα hαinj hαimm hpair
  let _ : Fact (Module.finrank ℝ (T.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (T.data p).chart).symm.trans hp⟩
  have hgap (q : Smale.ManifoldMorse.criticalPoints E f) (hqp : f q < f p) :
    f q < S.toSurgeryWindows.lower p :=
    (S.toSurgeryWindows.value_lt_upper q).trans (S.separated q p hqp)
  obtain ⟨γ, hγ, hγe, hγi, hγflow, hγrange⟩ :=
    T.exists_native_attaching_lower_cut hf p 2 (S.data p).lower_regular
      (S.toSurgeryWindows.lower_lt_value p) hgap
  have hdisj (j : Fin n) : Disjoint (Set.range γ) (Set.range (β j)) := by
    apply Set.disjoint_left.mpr
    intro z hzγ hzβ
    obtain ⟨x, hx⟩ := hzβ
    have hb := (hγrange z).mp hzγ
    rw [← hx] at hb
    exact S.not_backward_basin_on_upper_level hf p (α j x) ((hlabels j x p.val).mp hb)
  let Γ : Fin (n + 1) → (Smale.Hemisphere.Sphere 2) → (S.data p).LowerLevel := Fin.cases γ β
  have hΓpair : Pairwise (fun i j => Disjoint (Set.range (Γ i)) (Set.range (Γ j))) := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hdisj j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (hdisj i).symm
      | succ j => exact hβpair (fun h => hij (congrArg Fin.succ h))
  refine
    ⟨T, hcharts, hradii, hgerms, hback, hprotected, Γ, ?_, ?_, ?_, hΓpair, hγflow, hγrange,
      horbit, hlabels, ?_⟩
  · intro j
    cases j using Fin.cases with
    | zero => exact hγ
    | succ j => exact hβ j
  · intro j
    cases j using Fin.cases with
    | zero => exact hγe
    | succ j => exact hβe j
  · intro j
    cases j using Fin.cases with
    | zero => exact hγi
    | succ j => exact hβi j
  · intro j q hq hfull
    apply
      T.transported_backward_basin_image hf
        ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p))
        (S.data p).lower_regular q hq (α j) (β j)
    · intro x
      exact (hfull x).trans (hback x q).symm
    · exact horbit j

private theorem AdaptedWindows.reaches_lower_in_regular_band {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (x : { y : M // f y = a }) : x.val ∈ Degree.FlowCancellation.levelBasin S.flow f b := by
  obtain ⟨q, hq, r, hr, hback, hforward, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have hra : f r < a := by simpa only [x.property] using (hheights (ha x.val x.property)).1
  have haq : a < f q := by simpa only [x.property] using (hheights (ha x.val x.property)).2
  have hrb : f r < b := by
    by_contra h
    exact hgap r hr ⟨le_of_not_gt h, hra.le⟩
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward (hab.trans haq) hrb

private theorem AdaptedWindows.exists_regular_band_family_transport {ι E M F H X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (za : { x : M // f x = a }) (α : ι → X → { x : M // f x = a }) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    let _ := Smale.RegularLevel.chartedSpace hf hb
    (∀ j, ContMDiff I 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv I 𝓘(ℝ, Smale.RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ β : ι → X → { x : M // f x = b },
              (∀ j, ContMDiff I 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (β j)) ∧
                (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                  (∀ j x,
                      Function.Injective (mfderiv I 𝓘(ℝ, Smale.RegularLevel.Model E) (β j) x)) ∧
                    Pairwise (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                      (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
                        ∀ j q,
                          a < f q →
                            (∀ x : { y : M // f y = a },
                                x ∈ Set.range (α j) ↔
                                  Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) →
                              ∀ y : { x : M // f x = b },
                                y ∈ Set.range (β j) ↔
                                  Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 q) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  dsimp only
  intro hα hαinj hαimm hpair
  obtain ⟨t, ht⟩ := S.reaches_lower_in_regular_band hf hab ha hgap za
  obtain ⟨β, hβ, hβe, hβi, hβpair, horbit⟩ :=
    S.exists_native_family_level_transport hf ha hb za ⟨S.flow t za.val, ht⟩ α hα hαinj hαimm
      hpair (fun j x => S.reaches_lower_in_regular_band hf hab ha hgap (α j x))
  refine ⟨β, hβ, hβe, hβi, hβpair, horbit, ?_⟩
  intro j q hq hfull
  exact S.transported_backward_basin_image hf hab hb q hq (α j) (β j) hfull (horbit j)

private def
    MorseCancel.IsNativeMiddleBasinFamily {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (α : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = a }) : Prop :=
  let _ := Smale.RegularLevel.chartedSpace hf ha
  (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (α j)) ∧
    (∀ j, Topology.IsClosedEmbedding (α j)) ∧
      (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (α j) x)) ∧
        Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) ∧
          ∀ j y,
            y ∈ Set.range (α j) ↔
              Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 (p j).val)

private theorem
    AdaptedWindows.exists_regular_band_middle_basin_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (za : { x : M // f x = a }) {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, a < f (p j)) (α : Fin n → (Smale.Hemisphere.Sphere 2) → { x : M // f x = a })
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p α) :
    ∃ β : Fin n → (Smale.Hemisphere.Sphere 2) → { x : M // f x = b },
      MorseCancel.IsNativeMiddleBasinFamily S hf hb p β ∧
        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨β, hβs, hβe, hβi, hβpair, hflow, hβfull⟩ :=
    S.exists_regular_band_family_transport hf hab ha hb hgap za α hs (fun j => (he j).injective)
      hi hpair
  exact ⟨β, ⟨hβs, hβe, hβi, hβpair, fun j => hβfull j (p j).val (hp j) (hfull j)⟩, hflow⟩

private theorem AdaptedWindows.exists_middle_basin_family_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (q : Smale.ManifoldMorse.criticalPoints E f)
    (hq : MorseCancel.nativeMorseIndex E f q = 3) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → (Smale.Hemisphere.Sphere 2) → (S.data q).UpperLevel)
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p α)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ r, 0 < ε r) :
    ∃ T : AdaptedWindows E f,
      (∀ r, (T.data r).chart = (S.data r).chart) ∧
        (∀ r, (T.data r).radius < ε r) ∧
          (∀ r ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 r, T.field y = S.field y) ∧
            ∃ Γ : Fin (n + 1) → (Smale.Hemisphere.Sphere 2) → (S.data q).LowerLevel,
              MorseCancel.IsNativeMiddleBasinFamily T hf (S.data q).lower_regular (Fin.cases q p)
                Γ := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨T, hcharts, hradii, hgerms, -, -, Γ, hΓs, hΓe, hΓi, hΓpair, -, hΓzero, -, -, hΓfull⟩ :=
    S.exists_middle_family_step hf hm hdim q hq n α isClosed_empty (fun j => Set.disjoint_empty _)
      ε hε hs (fun j => (he j).injective) hi hpair
  refine ⟨T, hcharts, hradii, hgerms, Γ, hΓs, hΓe, hΓi, hΓpair, ?_⟩
  intro j
  cases j using Fin.cases with
  | zero => exact hΓzero
  | succ j => exact hΓfull j (p j).val (hp j) (hfull j)

private theorem AdaptedWindows.exists_middle_block_realization {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (n : ℕ) {c : ℝ}
    (hc : ∀ y, f y = c → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (horder : StrictMono (fun j => f (p j))) (habove : ∀ j, c < f (p j))
    (hblock :
      ∀ j (q : Smale.ManifoldMorse.criticalPoints E f), c < f q → f q ≤ f (p j) → q ∈ Set.range p)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    ∃ T : AdaptedWindows E f,
      (∀ q, (T.data q).chart = (S.data q).chart) ∧
        (∀ q, (T.data q).radius < ε q) ∧
          (∀ q ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
            ∃ α : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = c },
              MorseCancel.IsNativeMiddleBasinFamily T hf hc p α := by
  induction n generalizing S c ε with
  |
    zero =>
    obtain ⟨T, hfield, -, hcharts, hradii⟩ :=
      MorseCancel.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct S.smooth S.flow
        S.integral S.zero S.descent (fun q => (S.data q).chart) S.critical_model_germ ε hε
    refine ⟨T, hcharts, hradii, ?_, (fun j => Fin.elim0 j), ?_⟩
    · intro q hq
      exact Filter.Eventually.of_forall (fun y => congrFun hfield y)
    · exact
        ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
          fun j => Fin.elim0 j⟩
  | succ n ih =>
    let a := S.toSurgeryWindows.upper (p 0)
    have hpa : f (p 0) < a := S.toSurgeryWindows.value_lt_upper (p 0)
    have htail (j : Fin n) : a < f (p j.succ) :=
      (S.separated (p 0) (p j.succ) (horder (Fin.succ_pos j))).trans
        (S.toSurgeryWindows.lower_lt_value (p j.succ))
    have htailblock (j : Fin n) (q : Smale.ManifoldMorse.criticalPoints E f) (haq : a < f q)
      (hqj : f q ≤ f (p j.succ)) : q ∈ Set.range (fun i : Fin n => p i.succ) := by
      obtain ⟨i, hi⟩ := hblock j.succ q ((habove 0).trans (hpa.trans haq)) hqj
      cases i using Fin.cases with
      | zero => exact (not_lt_of_ge haq.le (hi ▸ hpa)).elim
      | succ i => exact ⟨i, hi⟩
    let δ := Real.sqrt (f (p 0) - c)
    have hδ : 0 < δ := Real.sqrt_pos.mpr (sub_pos.mpr (habove 0))
    let η : Smale.ManifoldMorse.criticalPoints E f → ℝ := fun q =>
      Min.min (ε q) (Min.min (S.data q).radius δ)
    have hη (q : Smale.ManifoldMorse.criticalPoints E f) : 0 < η q :=
      lt_min (hε q) (lt_min (S.data q).radius_pos hδ)
    obtain ⟨T, hchartsT, hradiiT, hgermsT, α, hα⟩ :=
      ih S (S.data (p 0)).upper_regular (fun j => p j.succ) (fun j => hp j.succ)
        (fun i j hij => horder (Fin.succ_lt_succ_iff.mpr hij)) htail htailblock η hη
    have hradius : (T.data (p 0)).radius < (S.data (p 0)).radius :=
      (hradiiT (p 0)).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hradδ : (T.data (p 0)).radius < δ :=
      (hradiiT (p 0)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hupper : T.toSurgeryWindows.upper (p 0) < a := by
      have hh :=
        mul_pos (sub_pos.mpr hradius)
          (add_pos (S.data (p 0)).radius_pos (T.data (p 0)).radius_pos)
      change f (p 0) + (T.data (p 0)).radius ^ 2 < f (p 0) + (S.data (p 0)).radius ^ 2
      nlinarith
    have hlower : c < T.toSurgeryWindows.lower (p 0) := by
      have hh := mul_pos (sub_pos.mpr hradδ) (add_pos hδ (T.data (p 0)).radius_pos)
      have hs : δ ^ 2 = f (p 0) - c := Real.sq_sqrt (sub_pos.mpr (habove 0)).le
      change c < f (p 0) - (T.data (p 0)).radius ^ 2
      nlinarith
    have hgapUpper :
      ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f,
        f q ∉ Set.Icc (T.toSurgeryWindows.upper (p 0)) a := by
      intro q hq hh
      have heq :=
        S.isolated (p 0) q hq
          ⟨((S.toSurgeryWindows.lower_lt_value (p 0)).trans
                  (T.toSurgeryWindows.value_lt_upper (p 0))).le.trans
              hh.1,
            hh.2⟩
      rw [heq] at hh
      exact not_le_of_gt (T.toSurgeryWindows.value_lt_upper (p 0)) hh.1
    let _ : Fact (Module.finrank ℝ (S.data (p 0)).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by
        have hs := (S.data (p 0)).chart.finrank_negative_add_positive
        have hn := (MorseCancel.nativeMorseIndex_eq_chart (S.data (p 0)).chart).symm.trans (hp 0)
        omega⟩
    let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
    let v :=
      Smale.SphereCoordinates.standardParametrization (S.data (p 0)).chart.PositiveCoordinates 2
        x₀
    obtain ⟨β, hβ, -⟩ :=
      T.exists_regular_band_middle_basin_family hf hupper (S.data (p 0)).upper_regular
        (T.data (p 0)).upper_regular hgapUpper ((S.data (p 0)).surgery.beltSphere v)
        (fun j => p j.succ) htail α hα
    obtain ⟨U, hchartsU, hradiiU, hgermsU, Γ, hΓ⟩ :=
      T.exists_middle_basin_family_step hf hm hdim (p 0) (hp 0) (fun j => p j.succ)
        (fun j => hupper.trans (htail j)) β hβ ε hε
    have hp_cases : Fin.cases (p 0) (fun j => p j.succ) = p := by
      funext j
      cases j using Fin.cases <;> rfl
    rw [hp_cases] at hΓ
    have hbelow (q : Smale.ManifoldMorse.criticalPoints E f) (hqp : f q < f (p 0)) : f q < c := by
      by_contra h
      have hcq : c < f q :=
        lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (fun heq => hc q.val heq q.property))
      obtain ⟨j, hj⟩ := hblock 0 q hcq hqp.le
      have hh := horder.monotone (Fin.zero_le j)
      rw [hj] at hh
      exact not_lt_of_ge hh hqp
    have hgapLower :
      ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f,
        f q ∉ Set.Icc c (T.toSurgeryWindows.lower (p 0)) := by
      intro q hq hh
      exact
        not_le_of_gt (hbelow ⟨q, hq⟩ (hh.2.trans_lt (T.toSurgeryWindows.lower_lt_value (p 0))))
          hh.1
    obtain ⟨Ω, hΩ, -⟩ :=
      U.exists_regular_band_middle_basin_family hf hlower (T.data (p 0)).lower_regular hc
        hgapLower (MorseCancel.nativeIndexThreeAttachingSphere T (p 0) (hp 0) x₀) p
        (fun j =>
          (T.toSurgeryWindows.lower_lt_value (p 0)).trans_le (horder.monotone (Fin.zero_le j)))
        Γ hΓ
    refine ⟨U, fun q => (hchartsU q).trans (hchartsT q), hradiiU, ?_, Ω, hΩ⟩
    intro q hq
    filter_upwards [hgermsU q hq, hgermsT q hq] with y hyU hyT
    exact hyU.trans hyT

private theorem MorseCancel.unique_connection_of_distinct_minimum_branches {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : Continuous f) (G : Flow ℝ M)
    (p r q : Smale.ManifoldMorse.criticalPoints E f) (hone : nativeMorseIndex E f q = 1)
    (hpr : p ≠ r) (hp : f p < S.lower q)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hback :
      ∀ x : (S.data q).LowerLevel,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
          x ∈ Set.range (S.data q).surgery.attachingSphere)
    (hu :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val))
    (hv :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val) Filter.atTop
        (𝓝 r.val)) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atBot
        (𝓝 q.val) ∧
      ∀ x,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) →
          Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p.val) →
            ∃ t, G t ((S.data q).surgery.attachingSphere u).val = x := by
  have hdim : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  have huv : u ≠ v := by
    intro h
    apply hpr
    apply Subtype.ext
    exact tendsto_nhds_unique (h ▸ hu) hv
  have hbu :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atBot
      (𝓝 q.val) :=
    (hback _).mpr (Set.mem_range_self u)
  have hsingle (x : (S.data q).LowerLevel)
    (hb : Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val))
    (hp' : Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p.val)) :
    x = (S.data q).surgery.attachingSphere u := by
    obtain ⟨w, hw⟩ := (hback x).mp hb
    rcases unitSphere_eq_two_points_of_finrank_one hdim u v huv w with h | h
    · exact (congrArg (S.data q).surgery.attachingSphere h).symm.trans hw |>.symm
    · have hx : (S.data q).surgery.attachingSphere v = x := h ▸ hw
      have hrv : Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 r.val) := hx ▸ hv
      exact False.elim (hpr (Subtype.ext (tendsto_nhds_unique hp' hrv)))
  have h :=
    Degree.FlowSuspension.unique_connection_of_level_basin_intersection G G hf
      (S.lower_lt_value q) hp id (fun _ => Iff.rfl) (fun _ => Iff.rfl)
      ((S.data q).surgery.attachingSphere u) hbu hu hsingle
  exact ⟨h.1, h.2.2⟩

private def
    MorseCancel.shiftedSignedMorseChart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (k : ℝ) :
    Smale.ManifoldMorse.SignedMorseChart (E := E) (fun x => f x + k) p
    where
  weights := c.weights
  signs := c.signs
  chart := c.chart
  mem_source := c.mem_source
  center := c.center
  equation x hx := by rw [c.equation x hx]; ring
  inverse_equation z hz := by rw [c.inverse_equation z hz]; ring

private theorem
    MorseCancel.isMorseAt_add_const {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (hm : Smale.ManifoldMorse.IsMorseAt E f p) (k : ℝ) :
    Smale.ManifoldMorse.IsMorseAt E (fun x => f x + k) p := by
  obtain ⟨e, he, hp, hgood⟩ := hm
  have hd : fderiv ℝ ((fun x => f x + k) ∘ e.symm) = fderiv ℝ (f ∘ e.symm) := by
    funext z
    exact fderiv_add_const k
  refine ⟨e, he, hp, ?_⟩
  rw [hd]
  exact hgood

private theorem MorseCancel.isMorseAt_of_add_const_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (hm : Smale.ManifoldMorse.IsMorseAt E f p) {k : ℝ} (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    Smale.ManifoldMorse.IsMorseAt E g p :=
  Degree.MorseCancellationPreservation.isMorseAt_of_same_germ (isMorseAt_add_const hm k) hgerm

private theorem MorseCancel.nativeMorseIndex_add_const {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (k : ℝ) :
    nativeMorseIndex E (fun x => f x + k) p = nativeMorseIndex E f p := by
  rw [nativeMorseIndex_eq_chart (shiftedSignedMorseChart c k), nativeMorseIndex_eq_chart c]
  rfl

private theorem MorseCancel.nativeMorseIndex_of_add_const_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) : nativeMorseIndex E g p = nativeMorseIndex E f p :=
  (nativeMorseIndex_congr_germ hgerm).trans (nativeMorseIndex_add_const c k)

private theorem MorseCancel.mfderiv_of_add_const_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p) {k : ℝ} (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g p = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p := by
  calc
    _ = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun x => f x + k) p : E →L[ℝ] ℝ) := hgerm.mfderiv_eq
    _ = _ := by
      have hs : mvfderiv 𝓘(ℝ, E) (fun x => f x + k) p = mvfderiv 𝓘(ℝ, E) f p := by
        rw [mvfderiv_fun_add hf mdifferentiableAt_const, mvfderiv_const, add_zero]
      exact hs

private theorem MorseCancel.exists_signed_morse_chart_of_germ_preserving_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hgerm : g =ᶠ[𝓝 p] f) :
    ∃ d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p, d.descentField = c.descentField := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgerm
  let d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p :=
    { weights := c.weights
      signs := c.signs
      chart := Smale.PartialChart.restrictSource c.chart hU
      mem_source := ⟨c.mem_source, hpU⟩
      center := c.center
      equation := by
        intro x hx
        have hxs : x ∈ c.chart.source ∩ U := hx
        have hxeq : g x = f x := hUsub hxs.2
        change g x = g p + ∑ i, c.weights i * (c.chart x i) ^ 2
        rw [hxeq, hgerm.self_of_nhds]
        exact c.equation x hxs.1
      inverse_equation := by
        intro z hz
        have hzs : z ∈ c.chart.target ∩ c.chart.symm ⁻¹' U := hz
        have hzeq : g (c.chart.symm z) = f (c.chart.symm z) := hUsub hzs.2
        change g (c.chart.symm z) = g p + ∑ i, c.weights i * z i ^ 2
        rw [hzeq, hgerm.self_of_nhds]
        exact c.inverse_equation z hzs.1 }
  exact ⟨d, rfl⟩

private theorem MorseCancel.exists_signed_morse_chart_of_shift_germ_preserving_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    ∃ d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p, d.descentField = c.descentField := by
  obtain ⟨d, hd⟩ :=
    exists_signed_morse_chart_of_germ_preserving_field (shiftedSignedMorseChart c k) hgerm
  exact ⟨d, hd⟩

private theorem Degree.FlowCancellation.levelBasin_eq_of_orbit_level_bridge {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) (f : X → ℝ) (a b : ℝ) (D : X → X)
    (hlevel : D '' {x | f x = a} = {x | f x = b}) (horbit : ∀ x, ∃ t, F t x = D x) :
    levelBasin F f a = levelBasin F f b := by
  ext x
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨t, ht⟩ := horbit (F s x)
    have hDy : f (D (F s x)) = b := by
      have hh : D (F s x) ∈ D '' {y | f y = a} := Set.mem_image_of_mem D hs
      rw [hlevel] at hh
      exact hh
    exact ⟨t + s, by rw [F.map_add, ht]; exact hDy⟩
  · rintro ⟨s, hs⟩
    have hy : F s x ∈ D '' {y | f y = a} := by rw [hlevel]; exact hs
    obtain ⟨y, hy, heq⟩ := hy
    change f y = a at hy
    obtain ⟨t, ht⟩ := horbit y
    have hyB : y ∈ levelBasin F f a := ⟨0, by simpa only [F.map_zero_apply] using hy⟩
    have hh := (levelBasin_flow_iff F f a t y).mpr hyB
    rw [ht, heq] at hh
    exact (levelBasin_flow_iff F f a s x).mp hh

private theorem
    Degree.FlowCancellation.levelBasin_eq_of_regular_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    levelBasin F f a = levelBasin F f b := by
  obtain ⟨D, hlevel, -, horbit⟩ :=
    Degree.FlowTimeChange.exists_orbit_preserving_ambient_band_bridge hf hV hdesc F hF hab hband
  exact levelBasin_eq_of_orbit_level_bridge F f a b D hlevel horbit

private theorem MorseCancel.image_flow_invariant_section {X A B : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B] (F : Flow ℝ X) (e : A ≃ₜ B) (ι : A → X) (κ : B → X)
    (horbit : ∀ x, ∃ t, F t (ι x) = κ (e x)) {P : X → Prop} (hP : ∀ t x, P (F t x) ↔ P x) :
    e '' {x | P (ι x)} = {y | P (κ y)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := horbit x
    have hh := (hP t (ι x)).mpr hx
    rwa [ht] at hh
  · intro hy
    obtain ⟨t, ht⟩ := horbit (e.symm y)
    have heq : e (e.symm y) = y := e.apply_symm_apply y
    rw [heq] at ht
    refine ⟨e.symm y, ?_, heq⟩
    apply (hP t (ι (e.symm y))).mp
    rwa [ht]

private theorem
    MorseCancel.isCompact_flow_invariant_section_iff {X A B : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B] (F : Flow ℝ X) (e : A ≃ₜ B) (ι : A → X) (κ : B → X)
    (horbit : ∀ x, ∃ t, F t (ι x) = κ (e x)) {P : X → Prop} (hP : ∀ t x, P (F t x) ↔ P x) :
    IsCompact {y : B | P (κ y)} ↔ IsCompact {x : A | P (ι x)} := by
  rw [← image_flow_invariant_section F e ι κ horbit hP]
  exact e.isCompact_image

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.isCompact_native_belt_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsCompact
      {x : { y : M // f y = f p + r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} := by
  have heq :
    {x : { y : M // f y = f p + r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} =
      Set.range (c.beltCoreMap r hr hblock) := by
    ext x
    simpa only [Set.mem_ofPred_eq, Set.mem_range, Subtype.ext_iff] using
      native_belt_core_basin_iff c hf hV F hF r hr hblock hfield hboundary x.property
  rw [heq]
  exact isCompact_range (c.beltCoreMap r hr hblock).continuous

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.isCompact_native_attaching_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p - r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsCompact
      {x : { y : M // f y = f p - r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} := by
  have heq :
    {x : { y : M // f y = f p - r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} =
      Set.range (c.attachingCoreMap r hr hblock) := by
    ext x
    simpa only [Set.mem_ofPred_eq, Set.mem_range, Subtype.ext_iff] using
      native_attaching_core_basin_iff c hf hV F hF r hr hblock hfield hboundary x.property
  rw [heq]
  exact isCompact_range (c.attachingCoreMap r hr hblock).continuous

private theorem
    Degree.FlowCancellation.isCompact_invariant_section_iff_of_regular_band {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {P : M → Prop}
    (hP : ∀ t x, P (F t x) ↔ P x) :
    IsCompact {x : { y : M // f y = b } | P (x : M)} ↔
      IsCompact {x : { y : M // f y = a } | P (x : M)} := by
  have ha : ∀ x, f x = a → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hband x (by rw [hx]; exact ⟨le_rfl, hab⟩)
  have hb : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hband x (by rw [hx]; exact ⟨hab, le_rfl⟩)
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  obtain ⟨D, e, -, he, horbit⟩ :=
    Degree.FlowTimeChange.exists_orbit_preserving_native_band_bridge hf hV hdesc F hF hab hband ha
      hb
  apply
    MorseCancel.isCompact_flow_invariant_section_iff F e.toHomeomorph Subtype.val Subtype.val _ hP
  intro x
  obtain ⟨t, ht⟩ := horbit x
  exact ⟨t, ht.trans (he x).symm⟩

private theorem Degree.FlowCancellation.isCompact_forward_section_iff_of_regular_band {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) (p : M) :
    IsCompact
        {x : { y : M // f y = b } | Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} ↔
      IsCompact
        {x : { y : M // f y = a } | Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} :=
  isCompact_invariant_section_iff_of_regular_band hf hV hdesc F hF hab hband (P := fun x =>
    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (fun t x => MorseCancel.flow_time_atTop_limit_iff F t x p)

private theorem Degree.FlowCancellation.isCompact_backward_section_iff_of_regular_band {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) (p : M) :
    IsCompact
        {x : { y : M // f y = b } | Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} ↔
      IsCompact
        {x : { y : M // f y = a } | Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} :=
  isCompact_invariant_section_iff_of_regular_band hf hV hdesc F hF hab hband (P := fun x =>
    Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (fun t x => MorseCancel.flow_time_atBot_limit_iff F t x p)

private def
    Degree.MorseRearrangement.nativeCylinderWeight {Z H N E M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H} [TopologicalSpace N]
    [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) (θ : N → ℝ)
    (x : M) : ℝ :=
  θ (A.symm x).1

private theorem Degree.MorseRearrangement.contMDiffOn_nativeCylinderWeight {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) {θ : N → ℝ}
    (hθ : ContMDiff I 𝓘(ℝ, ℝ) ∞ θ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (nativeCylinderWeight A θ) A.target :=
  hθ.comp_contMDiffOn (contMDiff_fst.comp_contMDiffOn A.contMDiffOn_invFun)

private theorem Degree.MorseRearrangement.nativeCylinderWeight_mem_Icc {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) {θ : N → ℝ}
    (hθ : ∀ z, θ z ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    nativeCylinderWeight A θ x ∈ Set.Icc (0 : ℝ) 1 :=
  hθ _

end Mathoverflow1973

end
