/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.OpenSubgroup
/-!
# Completion by open finite quotients

This module constructs the topological profinite completion of a topological
group from its open finite-index normal subgroups.  Unlike the abstract
completion by all finite quotients, the indexing category records the topology
on the source group.  This is the completion needed for infinite local
reciprocity.

The construction uses Mathlib's category of profinite groups, products, and
closed subgroups; it does not depend on a separate copied inverse-system implementation.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Pointwise

namespace LocalClassFieldTheory

universe u v w

/-- An open normal subgroup whose quotient has finite cardinality.

This is a property subtype of the standard `OpenNormalSubgroup`, so its order
and proof irrelevance come from the underlying object instead of a parallel
hand-written order implementation. -/
def OpenFiniteIndexNormalSubgroup (G : Type u) [Group G] [TopologicalSpace G] :=
  { H : OpenNormalSubgroup G // H.toSubgroup.FiniteIndex }

namespace OpenFiniteIndexNormalSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The underlying open normal subgroup. -/
def toOpenNormalSubgroup (H : OpenFiniteIndexNormalSubgroup G) :
    OpenNormalSubgroup G :=
  H.1

/-- The finite-index witness carried by the subtype. -/
theorem finiteIndex' (H : OpenFiniteIndexNormalSubgroup G) :
    H.toOpenNormalSubgroup.toSubgroup.FiniteIndex :=
  H.2

/-- Finite-index open normal subgroups are determined by their underlying open normal subgroups. -/
@[ext]
theorem ext {H K : OpenFiniteIndexNormalSubgroup G}
    (h : H.toOpenNormalSubgroup = K.toOpenNormalSubgroup) : H = K :=
  Subtype.ext h

/-- An indexed open normal subgroup carries its finite-index witness as an instance. -/
instance (H : OpenFiniteIndexNormalSubgroup G) :
    H.toOpenNormalSubgroup.toSubgroup.FiniteIndex :=
  H.finiteIndex'

/-- Open finite-index normal subgroups are ordered by inclusion. -/
instance : PartialOrder (OpenFiniteIndexNormalSubgroup G) :=
  Subtype.partialOrder
    (fun H : OpenNormalSubgroup G => H.toSubgroup.FiniteIndex)

/-- The inclusion preorder makes open finite-index normal subgroups a small thin category. -/
instance : SmallCategory (OpenFiniteIndexNormalSubgroup G) :=
  Preorder.smallCategory _

/-- A morphism of open finite-index normal subgroups induces inclusion of the underlying
subgroups. -/
theorem le_of_hom {H K : OpenFiniteIndexNormalSubgroup G} (f : H ⟶ K) :
    H.toOpenNormalSubgroup.toSubgroup ≤ K.toOpenNormalSubgroup.toSubgroup := by
  have h : H ≤ K := CategoryTheory.leOfHom f
  change H.toOpenNormalSubgroup ≤ K.toOpenNormalSubgroup at h
  exact h

end OpenFiniteIndexNormalSubgroup

section Completion

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The functor of finite quotients attached to open finite-index normal
subgroups. Inclusion of subgroups induces the corresponding quotient map. -/
def openFiniteQuotientFunctor :
    OpenFiniteIndexNormalSubgroup G ⥤ FiniteGrp where
  obj H := FiniteGrp.of (G ⧸ H.toOpenNormalSubgroup.toSubgroup)
  map := fun hHK => FiniteGrp.ofHom <|
    QuotientGroup.map _ _ (.id _) (by
      simpa using OpenFiniteIndexNormalSubgroup.le_of_hom hHK)
  map_id _ := ConcreteCategory.ext <| QuotientGroup.map_id _
  map_comp f g := ConcreteCategory.ext <|
    (QuotientGroup.map_comp_map _ _ _ (.id _) (.id _)
      (by simpa using OpenFiniteIndexNormalSubgroup.le_of_hom f)
      (by simpa using OpenFiniteIndexNormalSubgroup.le_of_hom g)).symm

/-- The same finite-quotient diagram, regarded in profinite groups with the
discrete topology on every finite stage. -/
noncomputable def openFiniteQuotientDiagram :
    OpenFiniteIndexNormalSubgroup G ⥤ ProfiniteGrp :=
  openFiniteQuotientFunctor G ⋙ forget₂ FiniteGrp ProfiniteGrp

/-- The finite profinite quotient attached to an open finite-index normal
subgroup. -/
noncomputable def openFiniteQuotient
    (H : OpenFiniteIndexNormalSubgroup G) : ProfiniteGrp :=
  (openFiniteQuotientDiagram G).obj H

/-- The product of all open finite quotients. -/
private abbrev openFiniteQuotientProduct : ProfiniteGrp :=
  ProfiniteGrp.pi (fun H : OpenFiniteIndexNormalSubgroup G =>
    openFiniteQuotient G H)

/-- The diagonal homomorphism to the product of all open finite quotients. -/
def openFiniteQuotientProductMapMonoidHom :
    G →* openFiniteQuotientProduct G where
  toFun g H := QuotientGroup.mk g
  map_one' := by
    funext H
    rfl
  map_mul' x y := by
    funext H
    rfl

/-- The diagonal map into the product of open finite quotients is continuous. -/
theorem openFiniteQuotientProductMapMonoidHom_continuous :
    Continuous (openFiniteQuotientProductMapMonoidHom G) := by
  apply continuous_pi
  intro H
  apply Continuous.mk
  intro s _
  change IsOpen ((fun g : G => (QuotientGroup.mk g : G ⧸ H.toOpenNormalSubgroup.toSubgroup)) ⁻¹' s)
  rw [← Set.biUnion_preimage_singleton QuotientGroup.mk s]
  refine isOpen_iUnion (fun i => isOpen_iUnion (fun _ => ?_))
  convert IsOpen.leftCoset
    H.toOpenNormalSubgroup.toOpenSubgroup.isOpen' (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
  exact Iff.symm (Set.mem_smul_set_iff_inv_smul_mem)

/-- The topological profinite completion over open finite quotients, realized
as the closure of the diagonal image in their product. -/
noncomputable def TopologicalProfiniteCompletion : ProfiniteGrp :=
  ProfiniteGrp.ofClosedSubgroup
    { toSubgroup :=
        (MonoidHom.range (openFiniteQuotientProductMapMonoidHom G)).topologicalClosure
      isClosed' := Subgroup.isClosed_topologicalClosure _ }

/-- The canonical continuous homomorphism into the open-quotient completion. -/
def topologicalProfiniteCompletionMap :
    G →ₜ* TopologicalProfiniteCompletion G where
  toFun g :=
    ⟨openFiniteQuotientProductMapMonoidHom G g,
      Subgroup.le_topologicalClosure
        (MonoidHom.range (openFiniteQuotientProductMapMonoidHom G)) ⟨g, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact (openFiniteQuotientProductMapMonoidHom G).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (openFiniteQuotientProductMapMonoidHom G).map_mul x y
  continuous_toFun :=
    (openFiniteQuotientProductMapMonoidHom_continuous G).subtype_mk _

/-- The canonical map has dense image in the open-quotient completion. -/
theorem topologicalProfiniteCompletionMap_denseRange :
    DenseRange (topologicalProfiniteCompletionMap G) := by
  let S : Subgroup (openFiniteQuotientProduct G) :=
    MonoidHom.range (openFiniteQuotientProductMapMonoidHom G)
  let incl : S → S.topologicalClosure :=
    Set.inclusion (Subgroup.le_topologicalClosure S)
  have hincl : DenseRange incl :=
    (denseRange_inclusion_iff
      (Subgroup.le_topologicalClosure S :
        (S : Set (openFiniteQuotientProduct G)) ⊆
          (S.topologicalClosure : Set (openFiniteQuotientProduct G)))).2 <| by
      simp [Subgroup.topologicalClosure_coe]
  have hrange :
      Set.range (topologicalProfiniteCompletionMap G) = Set.range incl := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(openFiniteQuotientProductMapMonoidHom G).rangeRestrict g, rfl⟩
    · rintro ⟨y, rfl⟩
      rcases y.2 with ⟨g, hg⟩
      refine ⟨g, ?_⟩
      apply Subtype.ext
      change (openFiniteQuotientProductMapMonoidHom G) g = y
      exact hg
  intro x
  rw [hrange]
  exact hincl x

/-- Projection of the completion to one of its defining finite quotients. -/
def topologicalProfiniteCompletionProjection
    (H : OpenFiniteIndexNormalSubgroup G) :
    TopologicalProfiniteCompletion G →ₜ* openFiniteQuotient G H where
  toFun x := x.1 H
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_apply H).comp continuous_subtype_val

/-- Projecting the canonical completion image of `g` gives its quotient class. -/
@[simp]
theorem topologicalProfiniteCompletionProjection_map
    (H : OpenFiniteIndexNormalSubgroup G) (g : G) :
    topologicalProfiniteCompletionProjection G H
        (topologicalProfiniteCompletionMap G g) =
      QuotientGroup.mk g :=
  rfl

/-- Every defining finite quotient is reached by the canonical projection
from the topological profinite completion. -/
theorem topologicalProfiniteCompletionProjection_surjective
    (H : OpenFiniteIndexNormalSubgroup G) :
    Function.Surjective (topologicalProfiniteCompletionProjection G H) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨topologicalProfiniteCompletionMap G g,
    topologicalProfiniteCompletionProjection_map G H g⟩

/-- The kernel of the canonical completion map is the intersection of all
open finite-index normal subgroups. -/
theorem topologicalProfiniteCompletionMap_ker :
    (topologicalProfiniteCompletionMap G).ker =
      ⨅ H : OpenFiniteIndexNormalSubgroup G,
        H.toOpenNormalSubgroup.toSubgroup := by
  ext g
  rw [Subgroup.mem_iInf]
  constructor
  · intro hg H
    have hval :
        openFiniteQuotientProductMapMonoidHom G g =
          (1 : openFiniteQuotientProduct G) :=
      congrArg Subtype.val hg
    have hcoord := congrFun hval H
    exact (QuotientGroup.eq_one_iff g).mp hcoord
  · intro hg
    change topologicalProfiniteCompletionMap G g = 1
    apply Subtype.ext
    funext H
    exact (QuotientGroup.eq_one_iff g).mpr (hg H)

/-- The canonical completion map is injective exactly when the intersection
of all open finite-index normal subgroups is trivial. -/
theorem topologicalProfiniteCompletionMap_injective_iff :
    Function.Injective (topologicalProfiniteCompletionMap G) ↔
      (⨅ H : OpenFiniteIndexNormalSubgroup G,
        H.toOpenNormalSubgroup.toSubgroup) = ⊥ := by
  change Function.Injective (topologicalProfiniteCompletionMap G).toMonoidHom ↔ _
  rw [← MonoidHom.ker_eq_bot_iff, topologicalProfiniteCompletionMap_ker]

/-- A separated open finite-quotient topology gives an injective canonical
completion map. -/
theorem topologicalProfiniteCompletionMap_injective_of_iInf_eq_bot
    (h :
      (⨅ H : OpenFiniteIndexNormalSubgroup G,
        H.toOpenNormalSubgroup.toSubgroup) = ⊥) :
    Function.Injective (topologicalProfiniteCompletionMap G) :=
  (topologicalProfiniteCompletionMap_injective_iff G).2 h

/-- The finite quotient projections commute with every transition map in the
open finite-quotient diagram. -/
theorem topologicalProfiniteCompletionProjection_transition
    {H K : OpenFiniteIndexNormalSubgroup G} (f : H ⟶ K)
    (x : TopologicalProfiniteCompletion G) :
    (openFiniteQuotientDiagram G).map f
        (topologicalProfiniteCompletionProjection G H x) =
      topologicalProfiniteCompletionProjection G K x := by
  let lhs : TopologicalProfiniteCompletion G → openFiniteQuotient G K :=
    fun y =>
      (openFiniteQuotientDiagram G).map f
        (topologicalProfiniteCompletionProjection G H y)
  let rhs : TopologicalProfiniteCompletion G → openFiniteQuotient G K :=
    fun y => topologicalProfiniteCompletionProjection G K y
  have hlhs : Continuous lhs :=
    ((openFiniteQuotientDiagram G).map f).hom.continuous_toFun.comp
      (topologicalProfiniteCompletionProjection G H).continuous_toFun
  have hrhs : Continuous rhs :=
    (topologicalProfiniteCompletionProjection G K).continuous_toFun
  have heq : lhs = rhs :=
    (topologicalProfiniteCompletionMap_denseRange G).equalizer hlhs hrhs <| by
      funext g
      rfl
  exact congrFun heq x

end Completion

/-! ### Universal property -/

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The open finite-index normal subgroup obtained by pulling an open normal
subgroup of a profinite target back along a continuous homomorphism. -/
def topologicalProfiniteCompletionPreimageIndex
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) (N : OpenNormalSubgroup P) :
    OpenFiniteIndexNormalSubgroup G :=
  ⟨
    { toOpenSubgroup := N.toOpenSubgroup.comap f.toMonoidHom f.continuous_toFun
      isNormal' := by
        change ((N : Subgroup P).comap f.toMonoidHom).Normal
        infer_instance },
    by
    let q : G →* P ⧸ (N : Subgroup P) :=
      (QuotientGroup.mk' (N : Subgroup P)).comp f.toMonoidHom
    let : q.ker.FiniteIndex := Subgroup.finiteIndex_ker q
    apply Subgroup.finiteIndex_of_le (H := q.ker)
    intro g hg
    change f g ∈ N
    exact (QuotientGroup.eq_one_iff (f g)).mp hg⟩

/-- The finite-stage map induced by a continuous homomorphism to a profinite
group, after quotienting by the pulled-back open normal subgroup. -/
def topologicalProfiniteCompletionFiniteQuotientMap
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) (N : OpenNormalSubgroup P) :
    G ⧸ (topologicalProfiniteCompletionPreimageIndex P f N).toOpenNormalSubgroup.toSubgroup →*
      P ⧸ (N : Subgroup P) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (N : Subgroup P)).comp f.toMonoidHom) <| by
      intro g hg
      exact (QuotientGroup.eq_one_iff (f g)).mpr hg

/-- The finite-stage map as a continuous homomorphism between the corresponding
finite profinite quotients.

This is deliberately a `ContinuousMonoidHom`, rather than a categorical
`ProfiniteGrp` morphism: the latter forces source and target into the same
universe even though the universal property has no such mathematical
restriction. -/
def topologicalProfiniteCompletionFiniteQuotientMorphism
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) (N : OpenNormalSubgroup P) :
    openFiniteQuotient G (topologicalProfiniteCompletionPreimageIndex P f N) →ₜ*
      (P.toFiniteQuotientFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp).obj N where
  toMonoidHom := topologicalProfiniteCompletionFiniteQuotientMap P f N
  continuous_toFun := by
    let : DiscreteTopology
        (openFiniteQuotient G
          (topologicalProfiniteCompletionPreimageIndex P f N)) :=
      ⟨rfl⟩
    exact continuous_of_discreteTopology

/-- The continuous projection from the open-quotient completion to an open
finite quotient of a profinite target. -/
def topologicalProfiniteCompletionFiniteProjection
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) (N : OpenNormalSubgroup P) :
    TopologicalProfiniteCompletion G →ₜ*
      (P.toFiniteQuotientFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp).obj N :=
  (topologicalProfiniteCompletionFiniteQuotientMorphism P f N).comp
    (topologicalProfiniteCompletionProjection G
      (topologicalProfiniteCompletionPreimageIndex P f N))

/-- The induced finite projection sends the completion image of `g` to the class of `f g`. -/
theorem topologicalProfiniteCompletionFiniteProjection_map
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) (N : OpenNormalSubgroup P) (g : G) :
    topologicalProfiniteCompletionFiniteProjection P f N
        (topologicalProfiniteCompletionMap G g) =
      QuotientGroup.mk' (N : Subgroup P) (f g) :=
  rfl

/-- The finite projections induced by a map to a profinite group commute with
the transition maps between the target's open finite quotients. -/
theorem topologicalProfiniteCompletionFiniteProjection_transition
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P)
    {N M : OpenNormalSubgroup P} (i : N ⟶ M)
    (x : TopologicalProfiniteCompletion G) :
    (P.toFiniteQuotientFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp).map i
        (topologicalProfiniteCompletionFiniteProjection P f N x) =
      topologicalProfiniteCompletionFiniteProjection P f M x := by
  let lhs :=
    fun y =>
      (P.toFiniteQuotientFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp).map i
        (topologicalProfiniteCompletionFiniteProjection P f N y)
  let rhs :=
    fun y => topologicalProfiniteCompletionFiniteProjection P f M y
  have hlhs : Continuous lhs :=
    ((P.toFiniteQuotientFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp).map i).hom.continuous_toFun.comp
      (topologicalProfiniteCompletionFiniteProjection P f N).continuous_toFun
  have hrhs : Continuous rhs :=
    (topologicalProfiniteCompletionFiniteProjection P f M).continuous_toFun
  have heq : lhs = rhs :=
    (topologicalProfiniteCompletionMap_denseRange G).equalizer hlhs hrhs <| by
      funext g
      rfl
  exact congrFun heq x

/-- The map from the open-quotient completion to the inverse limit of all
finite quotients of a profinite target. -/
noncomputable def topologicalProfiniteCompletionToFiniteQuotientLimit
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) :
    TopologicalProfiniteCompletion G →ₜ*
      ProfiniteGrp.limit (ProfiniteGrp.diagram P) where
  toFun x :=
    ⟨fun N => topologicalProfiniteCompletionFiniteProjection P f N x,
      by
        intro N M i
        exact topologicalProfiniteCompletionFiniteProjection_transition P f i x⟩
  map_one' := by
    apply Subtype.ext
    funext N
    exact (topologicalProfiniteCompletionFiniteProjection P f N).map_one
  map_mul' x y := by
    apply Subtype.ext
    funext N
    exact (topologicalProfiniteCompletionFiniteProjection P f N).map_mul x y
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro N
    exact (topologicalProfiniteCompletionFiniteProjection P f N).continuous_toFun

/-- A continuous homomorphism from `G` to a profinite group extends canonically
to the completion of `G` by its open finite quotients. -/
noncomputable def topologicalProfiniteCompletionLift
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) :
    TopologicalProfiniteCompletion G →ₜ* P :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P).symm).comp
    (topologicalProfiniteCompletionToFiniteQuotientLimit P f)

/-- The canonical lift agrees with the original homomorphism on the dense image of `G`. -/
@[simp]
theorem topologicalProfiniteCompletionLift_map
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) (g : G) :
    topologicalProfiniteCompletionLift P f
        (topologicalProfiniteCompletionMap G g) =
      f g := by
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  apply e.injective
  change e (e.symm (topologicalProfiniteCompletionToFiniteQuotientLimit P f
    (topologicalProfiniteCompletionMap G g))) = e (f g)
  rw [e.apply_symm_apply]
  apply Subtype.ext
  funext N
  rfl

/-- The canonical lift composed with the completion map is the original
continuous homomorphism. -/
@[simp]
theorem topologicalProfiniteCompletionLift_comp_map
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) :
    (topologicalProfiniteCompletionLift P f).comp
        (topologicalProfiniteCompletionMap G) = f := by
  ext g
  exact topologicalProfiniteCompletionLift_map P f g

/-- The canonical lift is the unique continuous homomorphism extending the
given map on the dense image of `G`. -/
theorem topologicalProfiniteCompletionLift_unique
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P)
    (h : TopologicalProfiniteCompletion G →ₜ* P)
    (hh : h.comp (topologicalProfiniteCompletionMap G) = f) :
    h = topologicalProfiniteCompletionLift P f := by
  let lhs : TopologicalProfiniteCompletion G → P := fun x => h x
  let rhs : TopologicalProfiniteCompletion G → P :=
    fun x => topologicalProfiniteCompletionLift P f x
  have heq : lhs = rhs :=
    (topologicalProfiniteCompletionMap_denseRange G).equalizer
      h.continuous_toFun
      (topologicalProfiniteCompletionLift P f).continuous_toFun <| by
        funext g
        change h (topologicalProfiniteCompletionMap G g) =
          topologicalProfiniteCompletionLift P f
            (topologicalProfiniteCompletionMap G g)
        rw [topologicalProfiniteCompletionLift_map]
        exact DFunLike.congr_fun hh g
  apply ContinuousMonoidHom.ext
  intro x
  exact congrFun heq x

/-! ### Functorial action -/

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A continuous homomorphism induces the canonical map between open-quotient
completions. -/
noncomputable def topologicalProfiniteCompletionMapHom (f : G →ₜ* H) :
    TopologicalProfiniteCompletion G →ₜ* TopologicalProfiniteCompletion H :=
  topologicalProfiniteCompletionLift (TopologicalProfiniteCompletion H)
    ((topologicalProfiniteCompletionMap H).comp f)

/-- The map induced on completions carries canonical images to canonical images. -/
@[simp]
theorem topologicalProfiniteCompletionMapHom_map
    (f : G →ₜ* H) (g : G) :
    topologicalProfiniteCompletionMapHom f
        (topologicalProfiniteCompletionMap G g) =
      topologicalProfiniteCompletionMap H (f g) :=
  topologicalProfiniteCompletionLift_map
    (TopologicalProfiniteCompletion H)
    ((topologicalProfiniteCompletionMap H).comp f) g

/-- The homomorphism induced by the identity is the identity on the completion. -/
@[simp]
theorem topologicalProfiniteCompletionMapHom_id :
    topologicalProfiniteCompletionMapHom
        (ContinuousMonoidHom.id G) =
      ContinuousMonoidHom.id (TopologicalProfiniteCompletion G) := by
  apply ContinuousMonoidHom.ext
  intro x
  let lhs : TopologicalProfiniteCompletion G →
      TopologicalProfiniteCompletion G :=
    fun y => topologicalProfiniteCompletionMapHom
      (ContinuousMonoidHom.id G) y
  let rhs : TopologicalProfiniteCompletion G →
      TopologicalProfiniteCompletion G := fun y => y
  have heq : lhs = rhs :=
    (topologicalProfiniteCompletionMap_denseRange G).equalizer
      (topologicalProfiniteCompletionMapHom
        (ContinuousMonoidHom.id G)).continuous_toFun
      continuous_id <| by
        funext g
        change topologicalProfiniteCompletionMapHom
            (ContinuousMonoidHom.id G)
              (topologicalProfiniteCompletionMap G g) =
          topologicalProfiniteCompletionMap G g
        rw [topologicalProfiniteCompletionMapHom_map]
        rfl
  exact congrFun heq x

variable {J : Type w} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]

/-- Passing to topological profinite completions preserves composition. -/
@[simp]
theorem topologicalProfiniteCompletionMapHom_comp
    (f : G →ₜ* H) (g : H →ₜ* J) :
    topologicalProfiniteCompletionMapHom (g.comp f) =
      (topologicalProfiniteCompletionMapHom g).comp
        (topologicalProfiniteCompletionMapHom f) := by
  apply ContinuousMonoidHom.ext
  intro x
  let lhs : TopologicalProfiniteCompletion G →
      TopologicalProfiniteCompletion J :=
    fun y => topologicalProfiniteCompletionMapHom (g.comp f) y
  let rhs : TopologicalProfiniteCompletion G →
      TopologicalProfiniteCompletion J :=
    fun y => topologicalProfiniteCompletionMapHom g
      (topologicalProfiniteCompletionMapHom f y)
  have heq : lhs = rhs :=
    (topologicalProfiniteCompletionMap_denseRange G).equalizer
      (topologicalProfiniteCompletionMapHom
        (g.comp f)).continuous_toFun
      ((topologicalProfiniteCompletionMapHom g).continuous_toFun.comp
        (topologicalProfiniteCompletionMapHom f).continuous_toFun) <| by
        funext x
        change topologicalProfiniteCompletionMapHom (g.comp f)
              (topologicalProfiniteCompletionMap G x) =
          topologicalProfiniteCompletionMapHom g
            (topologicalProfiniteCompletionMapHom f
              (topologicalProfiniteCompletionMap G x))
        rw [topologicalProfiniteCompletionMapHom_map,
          topologicalProfiniteCompletionMapHom_map,
          topologicalProfiniteCompletionMapHom_map]
        rfl
  exact congrFun heq x

/-- Bundled universal-arrow formulation of completion by open finite
quotients.  This is the adjunction data used by clients: maps from `G` to a
profinite group correspond to a unique continuous homomorphism out of its
completion.  The target universe is independent of the source universe. -/
structure ProfiniteCompletionUniversalProperty
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (C : ProfiniteGrp.{u}) (ι : G →ₜ* C) : Prop where
  /-- The image of the canonical map `ι` is dense in the profinite completion candidate `C`. -/
  denseRange : DenseRange ι
  /-- Every continuous homomorphism from `G` to a profinite group factors uniquely through `ι`. -/
  existsUniqueLift :
    ∀ (P : ProfiniteGrp.{v}) (f : G →ₜ* P),
      ∃! lift : C →ₜ* P, lift.comp ι = f

/-- The constructed completion satisfies the bundled universal property. -/
theorem topologicalProfiniteCompletion_universalProperty :
    ProfiniteCompletionUniversalProperty G
      (TopologicalProfiniteCompletion G)
      (topologicalProfiniteCompletionMap G) where
  denseRange := topologicalProfiniteCompletionMap_denseRange G
  existsUniqueLift := by
    intro P f
    refine ⟨topologicalProfiniteCompletionLift P f,
      topologicalProfiniteCompletionLift_comp_map P f, ?_⟩
    intro lift hlift
    exact topologicalProfiniteCompletionLift_unique P f lift hlift

end LocalClassFieldTheory
