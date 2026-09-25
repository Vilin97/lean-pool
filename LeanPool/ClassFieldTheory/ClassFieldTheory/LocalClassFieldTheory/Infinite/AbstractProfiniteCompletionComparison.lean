/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion
/-!
# Comparison with the abstract profinite completion

The abstract profinite completion of a group is the completion formed from all
finite-index normal subgroups, without reference to a topology.  We realize it
by applying the open-quotient construction to a discrete copy of the group.

When every finite-index normal subgroup is open in the given topology, the
open-quotient completion and the abstract completion are canonically
isomorphic as topological groups.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace LocalClassFieldTheory

universe u v

/-- A copy of a group equipped with the discrete topology. -/
@[ext]
structure AbstractProfiniteSource (G : Type u) where
  /-- The underlying group element. -/
  val : G

namespace AbstractProfiniteSource

variable (G : Type u)

/-- The tautological equivalence between the discrete copy and the underlying type. -/
def equiv : AbstractProfiniteSource G ≃ G where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The discrete source copy inherits the group structure of `G`. -/
instance [Group G] : Group (AbstractProfiniteSource G) := (equiv G).group

/-- The abstract profinite source carries the discrete topology. -/
instance : TopologicalSpace (AbstractProfiniteSource G) := ⊥

/-- The topology on the abstract profinite source is discrete. -/
instance : DiscreteTopology (AbstractProfiniteSource G) := ⟨rfl⟩

/-- The discrete source copy of a group is a topological group. -/
instance [Group G] : IsTopologicalGroup (AbstractProfiniteSource G) := inferInstance

/-- The tautological multiplicative equivalence from the discrete copy. -/
def mulEquiv [Group G] : AbstractProfiniteSource G ≃* G where
  toEquiv := equiv G
  map_mul' _ _ := rfl

end AbstractProfiniteSource

/-- The abstract profinite completion formed from all finite-index normal
subgroups.  This is a stable, non-`abbrev` public object; its inverse-limit
realization is available through `abstractProfiniteCompletionEquivModel`. -/
noncomputable def AbstractProfiniteCompletion
    (G : Type u) [Group G] : ProfiniteGrp :=
  TopologicalProfiniteCompletion (AbstractProfiniteSource G)

/-- Canonical comparison with the concrete open-finite-quotient model used
to construct the abstract profinite completion. -/
noncomputable def abstractProfiniteCompletionEquivModel
    (G : Type u) [Group G] :
    AbstractProfiniteCompletion G ≃ₜ*
      TopologicalProfiniteCompletion (AbstractProfiniteSource G) := by
  change TopologicalProfiniteCompletion (AbstractProfiniteSource G) ≃ₜ*
    TopologicalProfiniteCompletion (AbstractProfiniteSource G)
  exact ContinuousMulEquiv.refl _

/-- The canonical dense class map from the discrete source into the stable
abstract completion. -/
noncomputable def abstractProfiniteCompletionClass
    (G : Type u) [Group G] :
    AbstractProfiniteSource G →ₜ* AbstractProfiniteCompletion G :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (abstractProfiniteCompletionEquivModel G).symm).comp
    (topologicalProfiniteCompletionMap (AbstractProfiniteSource G))

/-- The model equivalence sends an abstract completion class to the canonical topological class. -/
@[simp] theorem abstractProfiniteCompletionEquivModel_class
    (G : Type u) [Group G] (g : AbstractProfiniteSource G) :
    abstractProfiniteCompletionEquivModel G
        (abstractProfiniteCompletionClass G g) =
      topologicalProfiniteCompletionMap (AbstractProfiniteSource G) g :=
  (abstractProfiniteCompletionEquivModel G).apply_symm_apply _

/-- The canonical class map has dense range.  Clients can use this theorem
without knowing which inverse-limit model realizes the abstract completion. -/
theorem abstractProfiniteCompletionClass_denseRange
    (G : Type u) [Group G] :
    DenseRange (abstractProfiniteCompletionClass G) := by
  let e := abstractProfiniteCompletionEquivModel G
  have he : DenseRange e.symm := e.symm.surjective.denseRange
  have hmap :=
    topologicalProfiniteCompletionMap_denseRange (AbstractProfiniteSource G)
  change DenseRange
    ((e.symm : TopologicalProfiniteCompletion (AbstractProfiniteSource G) →
        AbstractProfiniteCompletion G) ∘
      topologicalProfiniteCompletionMap (AbstractProfiniteSource G))
  exact he.comp hmap e.symm.continuous_toFun

/-- Extend a continuous homomorphism from the discrete source across the
stable abstract profinite completion.  This is the representation-independent
universal-property entry point for `AbstractProfiniteCompletion`. -/
noncomputable def abstractProfiniteCompletionLift
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P) :
    AbstractProfiniteCompletion G →ₜ* P :=
  (topologicalProfiniteCompletionLift P f).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (abstractProfiniteCompletionEquivModel G))

/-- The universal lift agrees with the original map on abstract completion classes. -/
@[simp] theorem abstractProfiniteCompletionLift_class
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P)
    (g : AbstractProfiniteSource G) :
    abstractProfiniteCompletionLift G P f
        (abstractProfiniteCompletionClass G g) = f g := by
  unfold abstractProfiniteCompletionLift
  change topologicalProfiniteCompletionLift P f
      (abstractProfiniteCompletionEquivModel G
        (abstractProfiniteCompletionClass G g)) = f g
  rw [abstractProfiniteCompletionEquivModel_class,
    topologicalProfiniteCompletionLift_map]

/-- Composing the universal lift with the class map recovers the source homomorphism. -/
@[simp] theorem abstractProfiniteCompletionLift_comp_class
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P) :
    (abstractProfiniteCompletionLift G P f).comp
        (abstractProfiniteCompletionClass G) = f := by
  ext g
  exact abstractProfiniteCompletionLift_class G P f g

/-- A continuous homomorphism out of the stable abstract completion is
determined by its values on the canonical dense class map. -/
theorem abstractProfiniteCompletionLift_unique
    (G : Type u) [Group G]
    (P : ProfiniteGrp.{v})
    (f : AbstractProfiniteSource G →ₜ* P)
    (h : AbstractProfiniteCompletion G →ₜ* P)
    (hh : h.comp (abstractProfiniteCompletionClass G) = f) :
    h = abstractProfiniteCompletionLift G P f := by
  let e := abstractProfiniteCompletionEquivModel G
  let hModel :
      TopologicalProfiniteCompletion (AbstractProfiniteSource G) →ₜ* P :=
    h.comp (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
  have hModel_comp :
      hModel.comp
          (topologicalProfiniteCompletionMap (AbstractProfiniteSource G)) = f := by
    ext g
    simpa [hModel, e, abstractProfiniteCompletionClass] using
      DFunLike.congr_fun hh g
  have hModel_eq :=
    topologicalProfiniteCompletionLift_unique P f hModel hModel_comp
  apply ContinuousMonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hModel_eq (e x)
  change h (e.symm (e x)) =
    topologicalProfiniteCompletionLift P f (e x) at hx
  rw [e.symm_apply_apply] at hx
  change h x = topologicalProfiniteCompletionLift P f (e x)
  exact hx

section Comparison

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The model-valued completion map used internally to establish continuity. -/
private def abstractProfiniteCompletionModelMapMonoidHom :
    G →* TopologicalProfiniteCompletion (AbstractProfiniteSource G) :=
  (topologicalProfiniteCompletionMap (AbstractProfiniteSource G)).toMonoidHom.comp
    (AbstractProfiniteSource.mulEquiv G).symm.toMonoidHom

/-- The abstract completion map, viewed as a homomorphism from the original group. -/
def abstractProfiniteCompletionMapMonoidHom : G →* AbstractProfiniteCompletion G :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (abstractProfiniteCompletionEquivModel G).symm).toMonoidHom.comp
    (abstractProfiniteCompletionModelMapMonoidHom G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The completion map sends `g` to the class of its discrete source copy. -/
@[simp] theorem abstractProfiniteCompletionMapMonoidHom_apply (g : G) :
    abstractProfiniteCompletionMapMonoidHom G g =
      abstractProfiniteCompletionClass G
        ((AbstractProfiniteSource.mulEquiv G).symm g) :=
  by
    change (abstractProfiniteCompletionEquivModel G).symm
        (topologicalProfiniteCompletionMap (AbstractProfiniteSource G)
          ((AbstractProfiniteSource.mulEquiv G).symm g)) =
      (abstractProfiniteCompletionEquivModel G).symm
        (topologicalProfiniteCompletionMap (AbstractProfiniteSource G)
          ((AbstractProfiniteSource.mulEquiv G).symm g))
    rfl

/-- If every finite-index normal subgroup is open, the abstract completion map
is continuous for the original topology. -/
private theorem abstractProfiniteCompletionModelMapMonoidHom_continuous
    (hOpen : ∀ H : Subgroup G, H.Normal → H.FiniteIndex → IsOpen (H : Set G)) :
    Continuous (abstractProfiniteCompletionModelMapMonoidHom G) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro H
  let e : G ≃* AbstractProfiniteSource G :=
    (AbstractProfiniteSource.mulEquiv G).symm
  let K : Subgroup G := H.toOpenNormalSubgroup.toSubgroup.comap e.toMonoidHom
  have hKnormal : K.Normal :=
    H.toOpenNormalSubgroup.toSubgroup.normal_comap e.toMonoidHom
  have hKfinite : K.FiniteIndex := by
    constructor
    rw [H.toOpenNormalSubgroup.toSubgroup.index_comap_of_surjective e.surjective]
    exact H.finiteIndex'.index_ne_zero
  have hKopen : IsOpen (K : Set G) := hOpen K hKnormal hKfinite
  apply Continuous.mk
  intro s _
  change IsOpen
    ((fun g : G =>
      (QuotientGroup.mk (e g) :
        AbstractProfiniteSource G ⧸ H.toOpenNormalSubgroup.toSubgroup)) ⁻¹' s)
  let q : G → AbstractProfiniteSource G ⧸ H.toOpenNormalSubgroup.toSubgroup :=
    fun g => QuotientGroup.mk (e g)
  change IsOpen (q ⁻¹' s)
  rw [← Set.biUnion_preimage_singleton q s]
  refine isOpen_iUnion (fun i => isOpen_iUnion (fun _ => ?_))
  let representative : G := e.symm (Quotient.out i)
  convert IsOpen.leftCoset hKopen representative using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
  simp only [representative, Set.mem_smul_set_iff_inv_smul_mem]
  change (Quotient.out i)⁻¹ * e x ∈ H.toOpenNormalSubgroup.toSubgroup ↔
    representative⁻¹ * x ∈ K
  simp [K, representative]

/-- If every finite-index normal subgroup is open, the abstract completion map
is continuous for the original topology. -/
theorem abstractProfiniteCompletionMapMonoidHom_continuous
    (hOpen : ∀ H : Subgroup G, H.Normal → H.FiniteIndex → IsOpen (H : Set G)) :
    Continuous (abstractProfiniteCompletionMapMonoidHom G) :=
  (abstractProfiniteCompletionEquivModel G).symm.continuous_toFun.comp
    (abstractProfiniteCompletionModelMapMonoidHom_continuous G hOpen)

/-- The canonical continuous map from the topological completion to the
abstract completion. -/
def topologicalProfiniteCompletionToAbstract
    (hOpen : ∀ H : Subgroup G, H.Normal → H.FiniteIndex → IsOpen (H : Set G)) :
    TopologicalProfiniteCompletion G →ₜ* AbstractProfiniteCompletion G :=
  topologicalProfiniteCompletionLift
    (AbstractProfiniteCompletion G)
    { toMonoidHom := abstractProfiniteCompletionMapMonoidHom G
      continuous_toFun := abstractProfiniteCompletionMapMonoidHom_continuous G hOpen }

/-- The comparison map agrees with the abstract completion map on the source group. -/
theorem topologicalProfiniteCompletionToAbstract_map
    (hOpen : ∀ H : Subgroup G, H.Normal → H.FiniteIndex → IsOpen (H : Set G))
    (g : G) :
    topologicalProfiniteCompletionToAbstract G hOpen
        (topologicalProfiniteCompletionMap G g) =
      abstractProfiniteCompletionClass G
        ((AbstractProfiniteSource.mulEquiv G).symm g) := by
  unfold topologicalProfiniteCompletionToAbstract
  rw [topologicalProfiniteCompletionLift_map]
  exact abstractProfiniteCompletionMapMonoidHom_apply G g

/-- The canonical continuous map from the abstract completion to the
topological completion. -/
def abstractProfiniteCompletionToTopological :
    AbstractProfiniteCompletion G →ₜ* TopologicalProfiniteCompletion G :=
  abstractProfiniteCompletionLift G
    (TopologicalProfiniteCompletion G)
    { toMonoidHom :=
        (topologicalProfiniteCompletionMap G).toMonoidHom.comp
          (AbstractProfiniteSource.mulEquiv G).toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }

/-- The reverse comparison map agrees with the topological completion map on the discrete source. -/
theorem abstractProfiniteCompletionToTopological_map
    (g : AbstractProfiniteSource G) :
    abstractProfiniteCompletionToTopological G
        (abstractProfiniteCompletionClass G g) =
      topologicalProfiniteCompletionMap G (AbstractProfiniteSource.mulEquiv G g) := by
  unfold abstractProfiniteCompletionToTopological
  rw [abstractProfiniteCompletionLift_class]
  rfl

/-- Under the condition that all finite-index normal subgroups are open, the
open-quotient completion is canonically the abstract profinite completion. -/
def topologicalProfiniteCompletionCompareAbstract
    (hOpen : ∀ H : Subgroup G, H.Normal → H.FiniteIndex → IsOpen (H : Set G)) :
    TopologicalProfiniteCompletion G ≃ₜ* AbstractProfiniteCompletion G := by
  let forward := topologicalProfiniteCompletionToAbstract G hOpen
  let backward := abstractProfiniteCompletionToTopological G
  have hleft : backward.comp forward = ContinuousMonoidHom.id _ := by
    calc
      backward.comp forward =
          topologicalProfiniteCompletionLift
            (TopologicalProfiniteCompletion G)
            (topologicalProfiniteCompletionMap G) := by
        apply topologicalProfiniteCompletionLift_unique
        ext g
        simp [backward, forward,
          topologicalProfiniteCompletionToAbstract_map,
          abstractProfiniteCompletionToTopological_map]
      _ = ContinuousMonoidHom.id _ := by
        symm
        apply topologicalProfiniteCompletionLift_unique
        rfl
  have hright : forward.comp backward = ContinuousMonoidHom.id _ := by
    calc
      forward.comp backward =
          abstractProfiniteCompletionLift G
            (AbstractProfiniteCompletion G)
            (abstractProfiniteCompletionClass G) := by
        apply abstractProfiniteCompletionLift_unique
        ext g
        simp [backward, forward,
          topologicalProfiniteCompletionToAbstract_map,
          abstractProfiniteCompletionToTopological_map]
      _ = ContinuousMonoidHom.id _ := by
        symm
        apply abstractProfiniteCompletionLift_unique
        rfl
  let e : TopologicalProfiniteCompletion G ≃* AbstractProfiniteCompletion G :=
    { toFun := forward
      invFun := backward
      left_inv := fun x => by
        have hx := congrArg (fun f => f x) hleft
        simpa using hx
      right_inv := fun y => by
        have hy := congrArg (fun f => f y) hright
        simpa using hy
      map_mul' := forward.map_mul }
  exact ContinuousMulEquiv.mk e forward.continuous_toFun backward.continuous_toFun

end Comparison

end LocalClassFieldTheory
