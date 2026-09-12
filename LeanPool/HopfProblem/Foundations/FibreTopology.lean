/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Elliptic.Core4
import all LeanPool.HopfProblem.Elliptic.Core4

/-!
# Hopf problem: foundations · fibre topology

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

private theorem isLocalDiffeomorphAt_of_comp_localDiffeomorph {E F F' H K K' M N R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup F'] [NormedSpace ℂ F'] [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace K'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] [TopologicalSpace R] [ChartedSpace K' R] (I : ModelWithCorners ℂ E H)
    (J : ModelWithCorners ℂ F K) (L : ModelWithCorners ℂ F' K') {f : M → N} {g : N → R} {x : M}
    (hf : IsLocalDiffeomorphAt I J ω f x) (hgf : IsLocalDiffeomorphAt I L ω (g ∘ f) x) :
    IsLocalDiffeomorphAt J L ω g (f x) := by
  obtain ⟨φ, hx, he⟩ := hgf
  have hinv : hf.localInverse (f x) = x := hf.localInverse_left_inv hf.localInverse_mem_target
  refine ⟨hf.localInverse.trans φ, ⟨hf.localInverse_mem_source, ?_⟩, ?_⟩
  · change hf.localInverse (f x) ∈ φ.source
    rwa [hinv]
  · intro y hy
    change g y = φ (hf.localInverse y)
    exact (congrArg g (hf.localInverse_right_inv hy.1).symm).trans (he hy.2)

private theorem
    isLocalDiffeomorph_of_comp_surjective {E F F' H K K' M N R : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F']
    [NormedSpace ℂ F'] [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace K']
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
    [TopologicalSpace R] [ChartedSpace K' R] (I : ModelWithCorners ℂ E H)
    (J : ModelWithCorners ℂ F K) (L : ModelWithCorners ℂ F' K') {f : M → N} {g : N → R}
    (hf : IsLocalDiffeomorph I J ω f) (hsurj : Function.Surjective f)
    (hgf : IsLocalDiffeomorph I L ω (g ∘ f)) : IsLocalDiffeomorph J L ω g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact isLocalDiffeomorphAt_of_comp_localDiffeomorph I J L (hf x) (hgf x)

private theorem retraction_leftInverse {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (r : C(X, A)) (hir : r.comp i = ContinuousMap.id A) :
    Function.LeftInverse r i := fun a => congrArg (fun f : C(A, A) => f a) hir

private def
    retractionHomotopyEquiv {A X : Type*} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X))
    (r : C(X, A)) (hir : r.comp i = ContinuousMap.id A)
    (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i)) :
    ContinuousMap.HomotopyEquiv A X where
  toFun := i
  invFun := r
  left_inv := by rw [hir]
  right_inv := ⟨H.toHomotopy.symm⟩

private def
    FibreTopology.restrictPreimageFibreHomeomorph {X Y : Type*} [TopologicalSpace X] (f : X → Y)
    (S : Set Y) (b : S) : (S.restrictPreimage f ⁻¹' { b }) ≃ₜ (f ⁻¹' {(b : Y)}) := by
  let forward : (S.restrictPreimage f ⁻¹' { b }) → (f ⁻¹' {(b : Y)}) := fun x =>
    ⟨x.val.val, congrArg (fun y : S => (y : Y)) x.property⟩
  let backward : (f ⁻¹' {(b : Y)}) → (S.restrictPreimage f ⁻¹' { b }) := fun x =>
    ⟨⟨x.val, by
        change f x.val ∈ S
        rw [show f x.val = b.val from x.property]
        exact b.property⟩,
      Subtype.ext x.property⟩
  refine
    { toFun := forward
      invFun := backward
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

private theorem FibreTopology.restrictPreimage_fibre_isConnected {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (S : Set Y) (b : S) (h : IsConnected (f ⁻¹' {(b : Y)})) :
    IsConnected (S.restrictPreimage f ⁻¹' { b }) :=
  isConnected_iff_connectedSpace.mpr
    ((restrictPreimageFibreHomeomorph f S b).connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp h))

private theorem
    FibreTopology.preimage_singleton_comp_injective {X Y Z : Type*} (f : X → Y) (g : Y → Z)
    (hg : Function.Injective g) (b : Y) : (g ∘ f) ⁻¹' {g b} = f ⁻¹' { b } := by
  ext x
  exact hg.eq_iff

private theorem FibreTopology.fibre_isConnected_comp_injective {X Y Z : Type*} [TopologicalSpace X]
    (f : X → Y) (g : Y → Z) (hg : Function.Injective g) (b : Y) (h : IsConnected (f ⁻¹' { b })) :
    IsConnected ((g ∘ f) ⁻¹' {g b}) := by
  rw [preimage_singleton_comp_injective f g hg b]
  exact h

public
theorem FibreTopology.fibre_isConnected_comp_homeomorph {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : X → Y) (e : Y ≃ₜ Z) (b : Z)
    (h : IsConnected (f ⁻¹' {e.symm b})) : IsConnected ((e ∘ f) ⁻¹' { b }) := by
  have he := fibre_isConnected_comp_injective f e e.injective (e.symm b) h
  simpa only [e.apply_symm_apply] using he

private theorem FibreTopology.isConnected_preimage_of_closed_of_connected_fibres {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    (hclosed : IsClosedMap f) (hconn : ∀ y, IsConnected (f ⁻¹' { y })) {s : Set Y}
    (hs : IsConnected s) : IsConnected (f ⁻¹' s) := by
  have hsurj : Function.Surjective f := fun y => (hconn y).nonempty
  have hq : Topology.IsQuotientMap (s.restrictPreimage f) :=
    (hclosed.restrictPreimage s).isQuotientMap hf.restrictPreimage (hsurj.restrictPreimage s)
  have hlocal : ∀ y : s, IsConnected (s.restrictPreimage f ⁻¹' { y }) := fun y =>
    restrictPreimage_fibre_isConnected f s y (hconn y)
  let : ConnectedSpace s := isConnected_iff_connectedSpace.mp hs
  apply isConnected_iff_connectedSpace.mpr
  apply connectedSpace_iff_univ.mpr
  simpa only [Set.preimage_univ] using
    hq.isCoinducing.isConnected_preimage_of_isClosed hlocal isClosed_univ
      (isConnected_univ : IsConnected (Set.univ : Set s))

private theorem FibreTopology.isConnected_preimage_of_proper_of_connected_fibres {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hproper : IsProperMap f)
    (hconn : ∀ y, IsConnected (f ⁻¹' { y })) {s : Set Y} (hs : IsConnected s) :
    IsConnected (f ⁻¹' s) :=
  isConnected_preimage_of_closed_of_connected_fibres hproper.continuous hproper.isClosedMap hconn
    hs

private theorem FibreTopology.isPathConnected_preimage_of_proper_of_connected_fibres {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} [LocallyPathConnectedSpace X]
    (hproper : IsProperMap f) (hconn : ∀ y, IsConnected (f ⁻¹' { y })) {s : Set Y}
    (hsopen : IsOpen s) (hs : IsConnected s) : IsPathConnected (f ⁻¹' s) :=
  ((hsopen.preimage hproper.continuous).isConnected_iff_isPathConnected).mp
    (isConnected_preimage_of_proper_of_connected_fibres hproper hconn hs)

end Mathoverflow1973

end
