/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Restrict

/-!
# Preservation of realized faces

A subdivision map sends the nodes of a smaller decomposition to the old
nodes, preserves their finite joins, and commutes with the affine transition
maps. Its fibres map into the old polytopes and its proper points remain
proper. Under these concrete conditions every old realized face restricts to
a realized face whenever its pullback is nonempty. The key order inequality
compares the new face index with the old one.
-/

namespace EGZ

open scoped BigOperators

namespace ConvexFlag

/-- Map a flag point using a map on nodes and compatible affine fibre maps. -/
def Point.map {F G : ConvexFlag} (q : F.Point) (node : SupHom F.Node G.Node)
    (fibre : (x : F.Node) → RealCoord (F.rank x) →ᵃ[ℝ] RealCoord (G.rank (node x)))
    (hpolytope : ∀ x, Set.MapsTo (fibre x)
      (F.polytope x).carrier (G.polytope (node x)).carrier) : G.Point :=
  ⟨node q.base, fibre q.base q.val, hpolytope q.base q.val_mem⟩

/-- Affine maps commuting with transitions preserve flag convex combinations
when the node map preserves joins. The least-upper-bound condition is proved
from the finite join of the strictly positive support. -/
theorem ConvexCombination.map_on_polytope {F G : ConvexFlag}
    (node : SupHom F.Node G.Node)
    (fibre : (x : F.Node) → RealCoord (F.rank x) →ᵃ[ℝ] RealCoord (G.rank (node x)))
    (hpolytope : ∀ x, Set.MapsTo (fibre x)
      (F.polytope x).carrier (G.polytope (node x)).carrier)
    (hcomm : ∀ {x y : F.Node} (h : x ≤ y) (q : RealCoord (F.rank x)),
      q ∈ (F.polytope x).carrier →
      fibre y ((F.transition h).real q) =
        (G.transition (OrderHomClass.monotone node h)).real (fibre x q))
    {I : Type*} [Fintype I] {points : I → F.Point} {weight : I → ℝ}
    {result : F.Point} (c : ConvexCombination points weight result) :
    ConvexCombination (fun i ↦ (points i).map node fibre hpolytope) weight
      (result.map node fibre hpolytope) := by
  classical
  have hpos : ∃ i, 0 < weight i := by
    by_contra! h
    have hz : ∀ i, weight i = 0 := fun i ↦ le_antisymm (h i) (c.nonnegative i)
    have hs := c.sum_eq_one
    simp [hz] at hs
  let A := {i : I // 0 < weight i}
  let _ : Nonempty A := ⟨⟨hpos.choose, hpos.choose_spec⟩⟩
  have hbase : result.base = (Finset.univ : Finset A).sup' Finset.univ_nonempty
      (fun i ↦ (points i).base) := by
    apply le_antisymm
    · apply c.base_isLUB.2
      intro i hi
      exact Finset.le_sup' (fun j : A ↦ (points j).base)
        (Finset.mem_univ (⟨i, hi⟩ : A))
    · exact Finset.sup'_le _ _ fun i _ ↦ c.base_isLUB.1 i i.2
  have hbase' : IsLeast
      {x : G.Node | ∀ i, 0 < weight i → node (points i).base ≤ x}
      (node result.base) := by
    constructor
    · intro i hi
      exact OrderHomClass.monotone node (c.base_isLUB.1 i hi)
    · intro x hx
      rw [hbase, map_finset_sup']
      exact Finset.sup'_le _ _ fun i _ ↦ hx i i.2
  refine ⟨c.nonnegative, c.sum_eq_one, hbase', ?_⟩
  let z : A → RealCoord (F.rank result.base) :=
    fun i ↦ (points i).coord (c.base_isLUB.1 i i.2)
  have hs : (∑ i : A, weight i) = 1 := c.sum_active
  change fibre result.base result.val = _
  calc
    fibre result.base result.val = fibre result.base (∑ i : A, weight i • z i) := by
      rw [c.val_eq]
    _ = fibre result.base
        ((Finset.univ : Finset A).affineCombination ℝ z (fun i ↦ weight i)) := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hs)]
    _ = (Finset.univ : Finset A).affineCombination ℝ (fibre result.base ∘ z)
        (fun i ↦ weight i) :=
      (Finset.univ : Finset A).map_affineCombination z (fun i ↦ weight i) hs
        (fibre result.base)
    _ = ∑ i : A, weight i • fibre result.base (z i) := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hs)]
      rfl
    _ = ∑ i : {i // 0 < weight i}, weight i •
        ((points i).map node fibre hpolytope).coord (hbase'.1 i i.2) := by
      apply Fintype.sum_congr
      intro i
      congr 1
      exact hcomm (c.base_isLUB.1 i i.2) (points i).val (points i).val_mem

/-- Global commutation is a sufficient special case of commutation on the
source polytopes. -/
theorem ConvexCombination.map {F G : ConvexFlag}
    (node : SupHom F.Node G.Node)
    (fibre : (x : F.Node) → RealCoord (F.rank x) →ᵃ[ℝ] RealCoord (G.rank (node x)))
    (hpolytope : ∀ x, Set.MapsTo (fibre x)
      (F.polytope x).carrier (G.polytope (node x)).carrier)
    (hcomm : ∀ {x y : F.Node} (h : x ≤ y) (q : RealCoord (F.rank x)),
      fibre y ((F.transition h).real q) =
        (G.transition (OrderHomClass.monotone node h)).real (fibre x q))
    {I : Type*} [Fintype I] {points : I → F.Point} {weight : I → ℝ}
    {result : F.Point} (c : ConvexCombination points weight result) :
    ConvexCombination (fun i ↦ (points i).map node fibre hpolytope) weight
      (result.map node fibre hpolytope) :=
  c.map_on_polytope node fibre hpolytope (fun h q _ ↦ hcomm h q)

end ConvexFlag

namespace RationalPolytope.Face

/-- Pull back an exposed face along an affine map taking one polytope into
another. The pullback includes the source polytope constraint. -/
def preimage {m n : ℕ} {P : RationalPolytope m} {Q : RationalPolytope n}
    (Γ : P.Face) (A : RealCoord n →ᵃ[ℝ] RealCoord m)
    (hA : Set.MapsTo A Q.carrier P.carrier)
    (hne : (Q.carrier ∩ A ⁻¹' Γ.carrier).Nonempty) : Q.Face where
  carrier := Q.carrier ∩ A ⁻¹' Γ.carrier
  is_exposed := by
    obtain ⟨functional, level, hle, hcarrier⟩ := Γ.is_exposed
    refine ⟨functional.comp A, level, ?_, ?_⟩
    · intro q hq
      exact hle (A q) (hA hq)
    · ext q
      change (q ∈ Q.carrier ∧ A q ∈ Γ.carrier) ↔
        q ∈ Q.carrier ∧ functional (A q) = level
      rw [hcarrier]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hA h.1, h.2⟩⟩
  nonempty := hne

@[simp]
theorem preimage_carrier {m n : ℕ} {P : RationalPolytope m} {Q : RationalPolytope n}
    (Γ : P.Face) (A : RealCoord n →ᵃ[ℝ] RealCoord m)
    (hA : Set.MapsTo A Q.carrier P.carrier)
    (hne : (Q.carrier ∩ A ⁻¹' Γ.carrier).Nonempty) :
    (Γ.preimage A hA hne).carrier = Q.carrier ∩ A ⁻¹' Γ.carrier := rfl

end RationalPolytope.Face

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- Affine data comparing a smaller decomposition `Ψ` with `Φ`. Preserving
joins, transitions, and proper points suffices to preserve realized faces;
neither injectivity nor equal coordinate ranks are required. -/
structure SubdivisionMap (Φ Ψ : FlagDecomposition p d f) where
  /-- Supremum-preserving map from refined nodes to original nodes. -/
  node : SupHom Ψ.flag.Node Φ.flag.Node
  /-- Affine map from each refined polytope to its original-node coordinates. -/
  fibre : (x : Ψ.flag.Node) →
    RealCoord (Ψ.flag.rank x) →ᵃ[ℝ] RealCoord (Φ.flag.rank (node x))
  polytope_mem : ∀ x, Set.MapsTo (fibre x)
    (Ψ.flag.polytope x).carrier (Φ.flag.polytope (node x)).carrier
  transition_comm : ∀ {x y : Ψ.flag.Node} (h : x ≤ y) (q : RealCoord (Ψ.flag.rank x)),
    fibre y ((Ψ.flag.transition h).real q) =
      (Φ.flag.transition (OrderHomClass.monotone node h)).real (fibre x q)
  proper : ∀ q ∈ Ψ.omega,
    (⟨node q.base, fibre q.base q.val, polytope_mem q.base q.val_mem⟩ : Φ.flag.Point) ∈
      Φ.omega

namespace SubdivisionMap

variable {Φ Ψ : FlagDecomposition p d f} (M : SubdivisionMap Φ Ψ)

/-- To construct a subdivision map it suffices to send local generators to
old local generators. Convex-combination preservation then gives inclusion
of the entire proper-point sets. -/
def ofLocalGenerators
    (node : SupHom Ψ.flag.Node Φ.flag.Node)
    (fibre : (x : Ψ.flag.Node) →
      RealCoord (Ψ.flag.rank x) →ᵃ[ℝ] RealCoord (Φ.flag.rank (node x)))
    (polytope_mem : ∀ x, Set.MapsTo (fibre x)
      (Ψ.flag.polytope x).carrier (Φ.flag.polytope (node x)).carrier)
    (transition_comm : ∀ {x y : Ψ.flag.Node} (h : x ≤ y)
      (q : RealCoord (Ψ.flag.rank x)),
      fibre y ((Ψ.flag.transition h).real q) =
        (Φ.flag.transition (OrderHomClass.monotone node h)).real (fibre x q))
    (hgenerators : ∀ q ∈ Ψ.omegaZero,
      q.map node fibre polytope_mem ∈ Φ.omegaZero) : SubdivisionMap Φ Ψ where
  node := node
  fibre := fibre
  polytope_mem := polytope_mem
  transition_comm := transition_comm
  proper := by
    rintro q ⟨n, points, weight, hpoints, hcomb⟩
    exact ⟨n, fun i ↦ (points i).map node fibre polytope_mem, weight,
      fun i ↦ hgenerators (points i) (hpoints i),
      hcomb.map node fibre polytope_mem transition_comm⟩

/-- The induced map on flag points. -/
def point (q : Ψ.flag.Point) : Φ.flag.Point :=
  ⟨M.node q.base, M.fibre q.base q.val, M.polytope_mem q.base q.val_mem⟩

@[simp]
theorem point_base (q : Ψ.flag.Point) : (M.point q).base = M.node q.base := rfl

theorem point_coord (q : Ψ.flag.Point) {x : Ψ.flag.Node} (h : q.base ≤ x) :
    (M.point q).coord (OrderHomClass.monotone M.node h) = M.fibre x (q.coord h) :=
  (M.transition_comm h q.val).symm

theorem point_proper {q : Ψ.flag.Point} (hq : q ∈ Ψ.omega) : M.point q ∈ Φ.omega :=
  M.proper q hq

/-- Compose successive subdivisions, including their proper-point maps. -/
def comp {Θ : FlagDecomposition p d f} (N : SubdivisionMap Ψ Θ) :
    SubdivisionMap Φ Θ where
  node := M.node.comp N.node
  fibre x := (M.fibre (N.node x)).comp (N.fibre x)
  polytope_mem x := by
    intro q hq
    exact M.polytope_mem (N.node x) (N.polytope_mem x hq)
  transition_comm h q := by
    change M.fibre _ (N.fibre _ ((Θ.flag.transition h).real q)) = _
    rw [N.transition_comm, M.transition_comm]
    rfl
  proper q hq := M.point_proper (N.point_proper hq)

@[simp]
theorem comp_point {Θ : FlagDecomposition p d f} (N : SubdivisionMap Ψ Θ)
    (q : Θ.flag.Point) : (M.comp N).point q = M.point (N.point q) := rfl

/-- The part of an old face lying in the new fibre. -/
def face (x : Ψ.flag.Node) (Γ : (Φ.flag.polytope (M.node x)).Face)
    (hne : ((Ψ.flag.polytope x).carrier ∩ M.fibre x ⁻¹' Γ.carrier).Nonempty) :
    (Ψ.flag.polytope x).Face :=
  Γ.preimage (M.fibre x) (M.polytope_mem x) hne

@[simp]
theorem face_carrier (x : Ψ.flag.Node) (Γ : (Φ.flag.polytope (M.node x)).Face)
    (hne : ((Ψ.flag.polytope x).carrier ∩ M.fibre x ⁻¹' Γ.carrier).Nonempty) :
    (M.face x Γ hne).carrier =
      (Ψ.flag.polytope x).carrier ∩ M.fibre x ⁻¹' Γ.carrier := rfl

theorem point_mem_pointsOnFace {x : Ψ.flag.Node}
    {Γ : (Φ.flag.polytope (M.node x)).Face}
    {hne : ((Ψ.flag.polytope x).carrier ∩ M.fibre x ⁻¹' Γ.carrier).Nonempty}
    {q : Ψ.flag.Point} (hq : q ∈ Ψ.pointsOnFace x (M.face x Γ hne)) :
    M.point q ∈ Φ.pointsOnFace (M.node x) Γ := by
  obtain ⟨hqproper, h, hcoord⟩ := hq
  refine ⟨M.point_proper hqproper, OrderHomClass.monotone M.node h, ?_⟩
  rw [M.point_coord]
  exact hcoord.2

/-- Every new proper-point base over the restricted face lies below the old
face index. Join preservation gives the same inequality for their supremum. -/
theorem faceIndex_le (x : Ψ.flag.Node) (Γ : (Φ.flag.polytope (M.node x)).Face)
    (hne : ((Ψ.flag.polytope x).carrier ∩ M.fibre x ⁻¹' Γ.carrier).Nonempty) :
    M.node (Ψ.faceIndex x (M.face x Γ hne)) ≤ Φ.faceIndex (M.node x) Γ := by
  classical
  unfold FlagDecomposition.faceIndex
  rw [map_finset_sup']
  apply Finset.sup'_le
  intro y hy
  simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  apply Finset.le_sup' id
  simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨M.point q, M.point_mem_pointsOnFace hq, rfl⟩

/-- Realization survives restriction of the polytopes and proper-point set.
The new face index may move downwards; its old image still maps into the old
face index, whose whole polytope maps into the realized face. -/
theorem isRealizedFace (x : Ψ.flag.Node) (Γ : (Φ.flag.polytope (M.node x)).Face)
    (hne : ((Ψ.flag.polytope x).carrier ∩ M.fibre x ⁻¹' Γ.carrier).Nonempty)
    (hΓ : Φ.IsRealizedFace (M.node x) Γ) :
    Ψ.IsRealizedFace x (M.face x Γ hne) := by
  intro q hq
  refine ⟨Ψ.flag.transition_mem (Ψ.faceIndex_le x (M.face x Γ hne)) hq, ?_⟩
  change M.fibre x ((Ψ.flag.transition (Ψ.faceIndex_le x (M.face x Γ hne))).real q) ∈
    Γ.carrier
  rw [M.transition_comm]
  have hindex := M.faceIndex_le x Γ hne
  have hqold := M.polytope_mem (Ψ.faceIndex x (M.face x Γ hne)) hq
  have hqindex := Φ.flag.transition_mem hindex hqold
  have hreal := hΓ _ hqindex
  rwa [Φ.flag.transition_trans hindex (Φ.faceIndex_le (M.node x) Γ)]

end SubdivisionMap

/-- The inclusion of reduced nodes is a subdivision map. Its fibre maps are
identities and every original proper point survives the restriction. -/
noncomputable def reducedSubdivisionMap (Φ : FlagDecomposition p d f) (hp : Odd p) :
    SubdivisionMap Φ (Φ.reduced hp) where
  node := {
    toFun := Subtype.val
    map_sup' := fun _ _ ↦ rfl }
  fibre _ := AffineMap.id ℝ _
  polytope_mem _ := fun _ hq ↦ hq
  transition_comm _ _ := rfl
  proper q hq := (Φ.reduced_omega_iff hp q).mp hq

end FlagDecomposition
end EGZ
