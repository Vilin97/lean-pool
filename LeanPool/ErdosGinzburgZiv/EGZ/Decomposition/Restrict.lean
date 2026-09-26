/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Reduction
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Faces

/-!
# Restriction to reduced nodes

The reduced bases form a nonempty finite join-closed set.  Restriction to
this set preserves every local contribution, since a non-reduced base has
zero local weight.  The resulting flag has the same proper points, viewed
through the inclusion of its nodes in the original flag.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

open Classical in
theorem exists_isReducedElement (Φ : FlagDecomposition p d f) :
    ∃ x, Φ.IsReducedElement x := by
  obtain ⟨q, hq⟩ := Φ.faces_visible ⊤ (RationalPolytope.Face.top _)
  exact ⟨q.base, q, hq.1, rfl⟩

open Classical in
/-- The join-closed set of bases which occur among the proper points. -/
abbrev ReducedNode (Φ : FlagDecomposition p d f) :=
  {x : Φ.flag.Node // Φ.IsReducedElement x}

open Classical in
noncomputable instance (Φ : FlagDecomposition p d f) : Fintype Φ.ReducedNode :=
  Subtype.fintype _

open Classical in
instance (Φ : FlagDecomposition p d f) : Nonempty Φ.ReducedNode :=
  let ⟨x, hx⟩ := Φ.exists_isReducedElement
  ⟨⟨x, hx⟩⟩

open Classical in
instance (Φ : FlagDecomposition p d f) : SemilatticeSup Φ.ReducedNode :=
  Subtype.semilatticeSup fun _ _ hx hy ↦ Φ.isReducedElement_sup hx hy

open Classical in
noncomputable instance (Φ : FlagDecomposition p d f) : OrderTop Φ.ReducedNode where
  top := Finset.univ.sup' Finset.univ_nonempty id
  le_top x := Finset.le_sup' id (Finset.mem_univ x)

open Classical in
/-- The convex flag obtained by retaining just the reduced nodes. -/
noncomputable abbrev reducedFlag (Φ : FlagDecomposition p d f) : ConvexFlag where
  Node := Φ.ReducedNode
  rank x := Φ.flag.rank x.1
  polytope x := Φ.flag.polytope x.1
  lattice x := Φ.flag.lattice x.1
  transition h := Φ.flag.transition h
  transition_mem h := Φ.flag.transition_mem h
  transition_lattice h := Φ.flag.transition_lattice h
  transition_refl x := Φ.flag.transition_refl x.1
  transition_trans hxy hyz := Φ.flag.transition_trans hxy hyz

open Classical in
/-- The inclusion of points of the restricted flag in the original flag. -/
def reducedPointInclusion (Φ : FlagDecomposition p d f)
    (q : Φ.reducedFlag.Point) : Φ.flag.Point :=
  ⟨q.base.1, q.val, q.val_mem⟩

open Classical in
/-- A point whose base is reduced can be viewed in the restricted flag. -/
def toReducedPoint (Φ : FlagDecomposition p d f) (q : Φ.flag.Point)
    (hq : Φ.IsReducedElement q.base) : Φ.reducedFlag.Point :=
  ⟨⟨q.base, hq⟩, q.val, q.val_mem⟩

open Classical in
@[simp]
theorem reducedPointInclusion_toReducedPoint (Φ : FlagDecomposition p d f)
    (q : Φ.flag.Point) (hq : Φ.IsReducedElement q.base) :
    Φ.reducedPointInclusion (Φ.toReducedPoint q hq) = q := rfl

open Classical in
/-- Convex combinations in the original flag descend to the restricted
flag whenever all the displayed bases are reduced. -/
theorem convexCombination_toReducedPoint (Φ : FlagDecomposition p d f)
    {I : Type*} [Fintype I] (points : I → Φ.flag.Point)
    (weight : I → ℝ) (q : Φ.flag.Point)
    (hpoints : ∀ i, Φ.IsReducedElement (points i).base)
    (hq : Φ.IsReducedElement q.base)
    (hcomb : ConvexFlag.ConvexCombination points weight q) :
    ConvexFlag.ConvexCombination
      (fun i ↦ Φ.toReducedPoint (points i) (hpoints i)) weight
      (Φ.toReducedPoint q hq) := by
  refine ⟨hcomb.nonnegative, hcomb.sum_eq_one, ?_, hcomb.val_eq⟩
  constructor
  · intro i hi
    exact hcomb.base_isLUB.1 i hi
  · intro x hx
    exact hcomb.base_isLUB.2 hx

open Classical in
/-- Inclusion into the original flag preserves convex combinations.  The
finite join of the active bases is reduced, so it can be used to compare
the two least-upper-bound conditions. -/
theorem convexCombination_reducedPointInclusion (Φ : FlagDecomposition p d f)
    {I : Type*} [Fintype I] (points : I → Φ.reducedFlag.Point)
    (weight : I → ℝ) (q : Φ.reducedFlag.Point)
    (hcomb : ConvexFlag.ConvexCombination points weight q) :
    ConvexFlag.ConvexCombination (fun i ↦ Φ.reducedPointInclusion (points i))
      weight (Φ.reducedPointInclusion q) := by
  have hpos : ∃ i, 0 < weight i := by
    by_contra! h
    have hz : ∀ i, weight i = 0 := fun i ↦ le_antisymm (h i) (hcomb.nonnegative i)
    have hs := hcomb.sum_eq_one
    simp [hz] at hs
  let s := (Finset.univ.filter fun i ↦ 0 < weight i).image
    (fun i ↦ (points i).base.1)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨(points i).base.1, Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩⟩
  have hred : Φ.IsReducedElement (s.sup' hs id) := by
    apply Φ.isReducedElement_sup'
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (points i).base.2
  refine ⟨hcomb.nonnegative, hcomb.sum_eq_one, ?_, hcomb.val_eq⟩
  constructor
  · intro i hi
    exact hcomb.base_isLUB.1 i hi
  · intro x hx
    have hqle : q.base ≤ (⟨s.sup' hs id, hred⟩ : Φ.ReducedNode) := by
      apply hcomb.base_isLUB.2
      intro i hi
      exact Finset.le_sup' id (show (points i).base.1 ∈ s from
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, hi⟩, rfl⟩)
    apply le_trans (show q.base.1 ≤ s.sup' hs id from hqle)
    apply Finset.sup'_le
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact hx i (Finset.mem_filter.mp hi).2

open Classical in
/-- The original representation restricted to the reduced nodes. -/
noncomputable def reducedRepresentation (Φ : FlagDecomposition p d f) :
    FpRepresentation p d Φ.reducedFlag where
  space x := Φ.representation.space x.1
  map x := Φ.representation.map x.1
  space_mono h := Φ.representation.space_mono h
  map_surjective x := Φ.representation.map_surjective x.1
  compatible h := Φ.representation.compatible h
  lattice_eq_standard x := Φ.representation.lattice_eq_standard x.1

open Classical in
theorem sum_reducedNode_eq (Φ : FlagDecomposition p d f) (hp : Odd p)
    (v : FpCoord p d) :
    ∑ x : Φ.ReducedNode, Φ.localWeight x.1 v = ∑ x, Φ.localWeight x v := by
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun x ↦ Φ.IsReducedElement x) (fun x ↦ Φ.localWeight x v)
  have hz : (∑ x : {x // ¬ Φ.IsReducedElement x}, Φ.localWeight x.1 v) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact Φ.localWeight_eq_zero_of_not_isReducedElement hp x.2 v
  simpa only [hz, add_zero] using h

open Classical in
theorem cumulativeWeight_reducedNode (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (v : FpCoord p d) :
    FlagDecompositionRaw.cumulativeWeight (F := Φ.reducedFlag)
      (fun y ↦ Φ.localWeight y.1) x v = Φ.cumulativeWeight x.1 v := by
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun y ↦ Φ.IsReducedElement y) (fun y ↦ if y ≤ x.1 then Φ.localWeight y v else 0)
  have hz : (∑ y : {y // ¬ Φ.IsReducedElement y},
      if y.1 ≤ x.1 then Φ.localWeight y.1 v else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    simp [Φ.localWeight_eq_zero_of_not_isReducedElement hp y.2 v]
  simpa only [cumulativeWeight, FlagDecompositionRaw.cumulativeWeight,
    hz, add_zero, Subtype.coe_le_coe] using h

open Classical in
theorem hat_reducedNode (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (z : IntCoord (Φ.flag.rank x.1)) :
    FlagDecompositionRaw.hat Φ.reducedRepresentation
      (fun y ↦ Φ.localWeight y.1) x z = Φ.hat x.1 z := by
  unfold FlagDecompositionRaw.hat hat
  have hw : FlagDecompositionRaw.cumulativeWeight (F := Φ.reducedFlag)
      (fun y ↦ Φ.localWeight y.1) x = Φ.cumulativeWeight x.1 :=
    funext (Φ.cumulativeWeight_reducedNode hp x)
  rw [hw]
  rfl

open Classical in
theorem omegaZero_reducedPointInclusion_iff (Φ : FlagDecomposition p d f)
    (q : Φ.reducedFlag.Point) :
    q ∈ FlagDecompositionRaw.omegaZero Φ.reducedRepresentation
        (fun x ↦ Φ.localWeight x.1) ↔
      Φ.reducedPointInclusion q ∈ Φ.omegaZero := Iff.rfl

open Classical in
/-- Inclusion identifies the proper-point set of the restricted data with
the original proper points whose bases lie in the restriction. -/
theorem omega_reducedPointInclusion_iff (Φ : FlagDecomposition p d f)
    (q : Φ.reducedFlag.Point) :
    q ∈ FlagDecompositionRaw.omega Φ.reducedRepresentation
        (fun x ↦ Φ.localWeight x.1) ↔
      Φ.reducedPointInclusion q ∈ Φ.omega := by
  constructor
  · rintro ⟨n, points, weight, hpoints, hcomb⟩
    exact ⟨n, fun i ↦ Φ.reducedPointInclusion (points i), weight,
      fun i ↦ (Φ.omegaZero_reducedPointInclusion_iff _).mp (hpoints i),
      Φ.convexCombination_reducedPointInclusion points weight q hcomb⟩
  · rintro ⟨n, points, weight, hpoints, hcomb⟩
    have hred (i : Fin n) : Φ.IsReducedElement (points i).base :=
      ⟨points i, ConvexFlag.subset_convexHull Φ.flag Φ.omegaZero (hpoints i), rfl⟩
    refine ⟨n, fun i ↦ Φ.toReducedPoint (points i) (hred i), weight, ?_, ?_⟩
    · intro i
      exact hpoints i
    · exact Φ.convexCombination_toReducedPoint points weight
        (Φ.reducedPointInclusion q) hred q.base.2 hcomb

open Classical in
/-- Restrict a decomposition to its reduced nodes.  No local mass is lost.
The odd-modulus assumption ensures that zero local lifts detect exactly
zero local finite-field weights. -/
noncomputable abbrev reduced (Φ : FlagDecomposition p d f) (hp : Odd p) :
    FlagDecomposition p d f where
  flag := Φ.reducedFlag
  representation := Φ.reducedRepresentation
  localWeight x := Φ.localWeight x.1
  local_supported x := Φ.local_supported x.1
  retained_le v := by
    change (∑ x : Φ.ReducedNode, Φ.localWeight x.1 v) ≤ f v
    rw [Φ.sum_reducedNode_eq hp]
    exact Φ.retained_le v
  liftedSupport x := Φ.liftedSupport x.1
  liftedSupport_spec x z := by
    rw [Φ.hat_reducedNode hp]
    exact Φ.liftedSupport_spec x.1 z
  liftedSupport_nonempty x := Φ.liftedSupport_nonempty x.1
  polytope_eq_liftedSupport x := Φ.polytope_eq_liftedSupport x.1
  faces_visible x Γ := by
    obtain ⟨q, hq, hbase, hcoord⟩ := Φ.faces_visible x.1 Γ
    have hred : Φ.IsReducedElement q.base := ⟨q, hq, rfl⟩
    refine ⟨Φ.toReducedPoint q hred, ?_, hbase, hcoord⟩
    exact (Φ.omega_reducedPointInclusion_iff _).mpr hq

open Classical in
@[simp]
theorem reduced_localWeight (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) : (Φ.reduced hp).localWeight x = Φ.localWeight x.1 := rfl

open Classical in
@[simp]
theorem reduced_cumulativeWeight (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) :
    (Φ.reduced hp).cumulativeWeight x = Φ.cumulativeWeight x.1 :=
  funext (Φ.cumulativeWeight_reducedNode hp x)

open Classical in
@[simp]
theorem reduced_retainedWeight (Φ : FlagDecomposition p d f) (hp : Odd p) :
    (Φ.reduced hp).retainedWeight = Φ.retainedWeight :=
  funext (Φ.sum_reducedNode_eq hp)

open Classical in
@[simp]
theorem reduced_retainedMass (Φ : FlagDecomposition p d f) (hp : Odd p) :
    (Φ.reduced hp).retainedMass = Φ.retainedMass := by
  simp only [retainedMass, Φ.reduced_retainedWeight hp]

open Classical in
/-- Removing non-reduced nodes cannot increase the number of nodes. -/
theorem card_reduced_le (Φ : FlagDecomposition p d f) (hp : Odd p) :
    Fintype.card (Φ.reduced hp).flag.Node ≤ Fintype.card Φ.flag.Node :=
  Fintype.card_subtype_le _

open Classical in
@[simp]
theorem reduced_hat (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) : (Φ.reduced hp).hat x = Φ.hat x.1 :=
  funext (Φ.hat_reducedNode hp x)

open Classical in
@[simp]
theorem reduced_gap (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) : (Φ.reduced hp).gap x = Φ.gap x.1 := by
  simp only [gap, Φ.reduced_hat hp]

open Classical in
@[simp]
theorem reduced_omega_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (q : Φ.reducedFlag.Point) :
    q ∈ (Φ.reduced hp).omega ↔ Φ.reducedPointInclusion q ∈ Φ.omega :=
  Φ.omega_reducedPointInclusion_iff q

open Classical in
/-- Every original proper point is retained: its base is reduced by
definition.  Thus inclusion identifies the two full proper-point sets. -/
theorem image_reduced_omega (Φ : FlagDecomposition p d f) (hp : Odd p) :
    Φ.reducedPointInclusion '' (Φ.reduced hp).omega = Φ.omega := by
  ext q
  constructor
  · rintro ⟨q', hq', rfl⟩
    exact (Φ.reduced_omega_iff hp q').mp hq'
  · intro hq
    have hred : Φ.IsReducedElement q.base := ⟨q, hq, rfl⟩
    exact ⟨Φ.toReducedPoint q hred, (Φ.reduced_omega_iff hp _).mpr hq, rfl⟩

open Classical in
/-- Every retained node is reduced in the restricted decomposition. -/
theorem reduced_isReduced (Φ : FlagDecomposition p d f) (hp : Odd p) :
    (Φ.reduced hp).IsReduced := by
  intro x
  obtain ⟨q, hq, hbase⟩ := x.2
  have hred : Φ.IsReducedElement q.base := ⟨q, hq, rfl⟩
  refine ⟨Φ.toReducedPoint q hred, (Φ.reduced_omega_iff hp _).mpr hq, ?_⟩
  exact Subtype.ext hbase

open Classical in
/-- Restriction preserves the same coordinate bound at every retained node. -/
theorem reduced_isKBounded (Φ : FlagDecomposition p d f) (hp : Odd p)
    {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K) :
    (Φ.reduced hp).IsKBounded (fun x ↦ K x.1) :=
  fun x z hz ↦ hK x.1 z hz

open Classical in
@[simp]
theorem reduced_liftedMassOn (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (S : Set (RealCoord (Φ.flag.rank x.1))) :
    (Φ.reduced hp).liftedMassOn x S = Φ.liftedMassOn x.1 S := by
  unfold liftedMassOn
  rw [Φ.reduced_hat hp]

open Classical in
@[simp]
theorem reduced_isLargeElement_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (ε : ℝ) (x : Φ.ReducedNode) :
    (Φ.reduced hp).IsLargeElement ε x ↔ Φ.IsLargeElement ε x.1 := by
  simp only [IsLargeElement, Φ.reduced_liftedMassOn hp, Φ.reduced_retainedMass hp]

open Classical in
@[simp]
theorem reduced_isLargeFace_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (ε : ℝ) (x : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face) :
    (Φ.reduced hp).IsLargeFace ε x Γ ↔ Φ.IsLargeFace ε x.1 Γ := by
  simp only [IsLargeFace, Φ.reduced_liftedMassOn hp, Φ.reduced_retainedMass hp]

open Classical in
@[simp]
theorem reduced_isCompleteElement_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (t : ℕ) (δ : ℝ) :
    (Φ.reduced hp).IsCompleteElement x t δ ↔ Φ.IsCompleteElement x.1 t δ := by
  simp only [IsCompleteElement, Φ.reduced_cumulativeWeight hp]
  rfl

open Classical in
/-- The ambient affine spans and affine integer generating sets at retained
nodes are unchanged, so minimality is preserved. -/
theorem reduced_isMinimal (Φ : FlagDecomposition p d f) (hp : Odd p)
    (hmin : Φ.IsMinimal) : (Φ.reduced hp).IsMinimal := by
  intro x
  obtain ⟨hspace, hspan⟩ := hmin x.1
  refine ⟨?_, hspan⟩
  rw [Φ.reduced_cumulativeWeight hp]
  exact hspace

open Classical in
theorem reduced_pointsOnFace_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face)
    (q : Φ.reducedFlag.Point) :
    q ∈ (Φ.reduced hp).pointsOnFace x Γ ↔
      Φ.reducedPointInclusion q ∈ Φ.pointsOnFace x.1 Γ := by
  change (q ∈ (Φ.reduced hp).omega ∧
      ∃ h : q.base ≤ x, q.coord h ∈ Γ.carrier) ↔
    (Φ.reducedPointInclusion q ∈ Φ.omega ∧
      ∃ h : q.base.1 ≤ x.1, (Φ.reducedPointInclusion q).coord h ∈ Γ.carrier)
  rw [Φ.reduced_omega_iff hp]
  rfl

open Classical in
theorem reduced_faceBases_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x y : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face) :
    y ∈ (Φ.reduced hp).faceBases x Γ ↔ y.1 ∈ Φ.faceBases x.1 Γ := by
  simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, hbase⟩
    exact ⟨Φ.reducedPointInclusion q,
      (Φ.reduced_pointsOnFace_iff hp x Γ q).mp hq,
      congrArg Subtype.val hbase⟩
  · rintro ⟨q, hq, hbase⟩
    have hred : Φ.IsReducedElement q.base := ⟨q, hq.1, rfl⟩
    exact ⟨Φ.toReducedPoint q hred,
      (Φ.reduced_pointsOnFace_iff hp x Γ _).mpr hq,
      Subtype.ext hbase⟩

open Classical in
/-- The face index computed after restriction is the same original node.
Every face index is reduced, which makes it available in the restriction. -/
theorem reduced_faceIndex_val (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face) :
    ((Φ.reduced hp).faceIndex x Γ).1 = Φ.faceIndex x.1 Γ := by
  apply le_antisymm
  · have hle : (Φ.reduced hp).faceIndex x Γ ≤
        (⟨Φ.faceIndex x.1 Γ, Φ.isReducedElement_faceIndex x.1 Γ⟩ : Φ.ReducedNode) := by
      unfold faceIndex
      apply Finset.sup'_le
      intro y hy
      exact Finset.le_sup' id ((Φ.reduced_faceBases_iff hp x y Γ).mp hy)
    exact hle
  · unfold faceIndex
    apply Finset.sup'_le
    intro y hy
    have hyred : Φ.IsReducedElement y := by
      simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      exact ⟨q, hq.1, rfl⟩
    have hynew := (Φ.reduced_faceBases_iff hp x ⟨y, hyred⟩ Γ).mpr hy
    have hle : (⟨y, hyred⟩ : Φ.ReducedNode) ≤ (Φ.reduced hp).faceIndex x Γ :=
      Finset.le_sup' id hynew
    exact hle

open Classical in
theorem reduced_faceIndex (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face) :
    (Φ.reduced hp).faceIndex x Γ =
      (⟨Φ.faceIndex x.1 Γ, Φ.isReducedElement_faceIndex x.1 Γ⟩ : Φ.ReducedNode) :=
  Subtype.ext (Φ.reduced_faceIndex_val hp x Γ)

open Classical in
@[simp]
theorem reduced_isRealizedFace_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.ReducedNode) (Γ : (Φ.flag.polytope x.1).Face) :
    (Φ.reduced hp).IsRealizedFace x Γ ↔ Φ.IsRealizedFace x.1 Γ := by
  have hcongr (a b : Φ.flag.Node) (ha : a ≤ x.1) (hb : b ≤ x.1)
      (hab : a = b) :
      (∀ q ∈ (Φ.flag.polytope a).carrier, (Φ.flag.transition ha).real q ∈ Γ.carrier) ↔
      (∀ q ∈ (Φ.flag.polytope b).carrier, (Φ.flag.transition hb).real q ∈ Γ.carrier) := by
    subst b
    rfl
  exact hcongr _ _ ((Φ.reduced hp).faceIndex_le x Γ) (Φ.faceIndex_le x.1 Γ)
    (Φ.reduced_faceIndex_val hp x Γ)

open Classical in
/-- Restriction preserves completeness with the same thresholds at every
retained node and the same parameters. -/
theorem reduced_isComplete (Φ : FlagDecomposition p d f) (hp : Odd p)
    {T : Φ.flag.Node → ℕ} {ε δ : ℝ} (hcomplete : Φ.IsComplete T ε δ) :
    (Φ.reduced hp).IsComplete (fun x ↦ T x.1) ε δ := by
  refine ⟨Φ.reduced_isMinimal hp hcomplete.1, Φ.reduced_isReduced hp, ?_, ?_⟩
  · intro x hx
    exact (Φ.reduced_isCompleteElement_iff hp x (T x.1) δ).mpr
      (hcomplete.2.2.1 x.1 ((Φ.reduced_isLargeElement_iff hp ε x).mp hx))
  · intro x Γ hΓ
    exact (Φ.reduced_isRealizedFace_iff hp x Γ).mpr
      (hcomplete.2.2.2 x.1 Γ ((Φ.reduced_isLargeFace_iff hp ε x Γ).mp hΓ))

end EGZ.FlagDecomposition
