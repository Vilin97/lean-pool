/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.AdaptiveOpenComplex
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceModel
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicGraphApproximation

/-!
# Finite marked-edge fans on intrinsic two-complexes

The relative Radó weld introduces finitely many vertices on the boundary of an intrinsic
subcomplex.  They must be ordered once on each global abstract edge: ordering independently in
the two incident face charts can introduce incompatible auxiliary points.  This file supplies
that global finite edge order and its consecutive intervals.
-/

open scoped BigOperators

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

/-- A finite set of intrinsic points containing both endpoints of every abstract edge. -/
structure EdgeMarking where
  /-- The `points` declaration. -/
  points : Finset K.realization
  first_mem : ∀ e : K.Edge, K.edgeFirstPoint e ∈ points
  second_mem : ∀ e : K.Edge, K.edgeSecondPoint e ∈ points

/-- Enlarge any prescribed finite point set by all abstract edge endpoints. -/
noncomputable def EdgeMarking.ofFinset (P : Finset K.realization) :
    K.EdgeMarking := by
  classical
  let first : Finset K.realization :=
    (Finset.univ : Finset K.Edge).image K.edgeFirstPoint
  let second : Finset K.realization :=
    (Finset.univ : Finset K.Edge).image K.edgeSecondPoint
  exact
    { points := P ∪ first ∪ second
      first_mem := by
        intro e
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
      second_mem := by
        intro e
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩ }

theorem EdgeMarking.subset_points_ofFinset (P : Finset K.realization) :
    P ⊆ (EdgeMarking.ofFinset (K := K) P).points := by
  intro p hp
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)

namespace EdgeMarking

variable {K : IntrinsicTwoComplex} (M : K.EdgeMarking)

/-- The marked points carried by one global abstract edge. -/
noncomputable def edgeMarks (e : K.Edge) : Finset K.realization := by
  classical
  exact M.points.filter fun p ↦ p ∈ K.faceCarrier e.1

theorem mem_edgeMarks_iff (e : K.Edge) (p : K.realization) :
    p ∈ M.edgeMarks e ↔ p ∈ M.points ∧ p ∈ K.faceCarrier e.1 := by
  classical
  exact Finset.mem_filter

theorem edgeFirstPoint_mem_edgeMarks (e : K.Edge) :
    K.edgeFirstPoint e ∈ M.edgeMarks e := by
  rw [M.mem_edgeMarks_iff e]
  refine ⟨M.first_mem e, ?_⟩
  rw [← K.range_edgePath e]
  exact ⟨⟨0, by simp⟩, K.edgePath_zero e⟩

theorem edgeSecondPoint_mem_edgeMarks (e : K.Edge) :
    K.edgeSecondPoint e ∈ M.edgeMarks e := by
  rw [M.mem_edgeMarks_iff e]
  refine ⟨M.second_mem e, ?_⟩
  rw [← K.range_edgePath e]
  exact ⟨⟨1, by simp⟩, K.edgePath_one e⟩

/-- A total real edge parameter.  Only its value on the edge carrier is used; totality avoids
dependent proof terms in the finite sorting relation. -/
noncomputable def edgeParameterValue (_ : K.EdgeMarking)
    (e : K.Edge) (p : K.realization) : ℝ := by
  classical
  exact if hp : p ∈ K.faceCarrier e.1 then (K.edgeParameter e p hp : ℝ) else 0

theorem edgeParameterValue_eq (e : K.Edge) {p : K.realization}
    (hp : p ∈ K.faceCarrier e.1) :
    M.edgeParameterValue e p = (K.edgeParameter e p hp : ℝ) := by
  simp only [edgeParameterValue, dif_pos hp]

/-- The total parameter remains injective when restricted to its intended edge carrier. -/
theorem edgeParameterValue_injOn (e : K.Edge) :
    Set.InjOn (M.edgeParameterValue e) (K.faceCarrier e.1) := by
  intro p hp q hq hpq
  have hparam :
      K.edgeParameter e p hp = K.edgeParameter e q hq := by
    apply Subtype.ext
    simpa only [M.edgeParameterValue_eq e hp,
      M.edgeParameterValue_eq e hq] using hpq
  calc
    p = K.edgePath e (K.edgeParameter e p hp) :=
      (K.edgePath_edgeParameter e p hp).symm
    _ = K.edgePath e (K.edgeParameter e q hq) := congrArg _ hparam
    _ = q := K.edgePath_edgeParameter e q hq

/-- A marked point on one edge. -/
abbrev EdgeMark (e : K.Edge) := {p // p ∈ M.edgeMarks e}

/-- The `edgeMarkParameter` declaration. -/
noncomputable def edgeMarkParameter (e : K.Edge) (p : M.EdgeMark e) : ℝ :=
  M.edgeParameterValue e p.1

theorem edgeMarkParameter_injective (e : K.Edge) :
    Function.Injective (M.edgeMarkParameter e) := by
  intro p q hpq
  have hp : p.1 ∈ K.faceCarrier e.1 :=
    ((M.mem_edgeMarks_iff e p.1).mp p.2).2
  have hq : q.1 ∈ K.faceCarrier e.1 :=
    ((M.mem_edgeMarks_iff e q.1).mp q.2).2
  have hparam :
      K.edgeParameter e p.1 hp = K.edgeParameter e q.1 hq := by
    apply Subtype.ext
    simpa only [edgeMarkParameter, M.edgeParameterValue_eq e hp,
      M.edgeParameterValue_eq e hq] using hpq
  apply Subtype.ext
  calc
    p.1 = K.edgePath e (K.edgeParameter e p.1 hp) :=
      (K.edgePath_edgeParameter e p.1 hp).symm
    _ = K.edgePath e (K.edgeParameter e q.1 hq) := congrArg _ hparam
    _ = q.1 := K.edgePath_edgeParameter e q.1 hq

/-- The `edgeMarkLE` declaration. -/
def edgeMarkLE (e : K.Edge) (p q : M.EdgeMark e) : Prop :=
  M.edgeMarkParameter e p ≤ M.edgeMarkParameter e q

noncomputable instance edgeMarkLEDecidable (e : K.Edge) :
    DecidableRel (M.edgeMarkLE e) :=
  fun p q ↦ inferInstanceAs
    (Decidable (M.edgeMarkParameter e p ≤ M.edgeMarkParameter e q))

instance edgeMarkLE_total (e : K.Edge) :
    Std.Total (M.edgeMarkLE e) :=
  ⟨fun p q ↦ le_total (M.edgeMarkParameter e p) (M.edgeMarkParameter e q)⟩

instance edgeMarkLE_antisymm (e : K.Edge) :
    Std.Antisymm (M.edgeMarkLE e) :=
  ⟨fun _ _ hpq hqp ↦ M.edgeMarkParameter_injective e (le_antisymm hpq hqp)⟩

instance edgeMarkLE_isTrans (e : K.Edge) :
    IsTrans (M.EdgeMark e) (M.edgeMarkLE e) :=
  ⟨fun _ _ _ hpq hqr ↦ hpq.trans hqr⟩

/-- The globally ordered marked points of one abstract edge. -/
noncomputable def edgeMarkList (e : K.Edge) : List K.realization := by
  classical
  exact ((M.edgeMarks e).attach.sort (M.edgeMarkLE e)).map Subtype.val

theorem mem_edgeMarkList_iff (e : K.Edge) (p : K.realization) :
    p ∈ M.edgeMarkList e ↔ p ∈ M.edgeMarks e := by
  classical
  simp only [edgeMarkList, List.mem_map, Finset.mem_sort,
    Finset.mem_attach]
  constructor
  · rintro ⟨q, -, rfl⟩
    exact q.2
  · intro hp
    exact ⟨⟨p, hp⟩, trivial, rfl⟩

theorem edgeMarkList_nodup (e : K.Edge) :
    (M.edgeMarkList e).Nodup := by
  classical
  unfold edgeMarkList
  exact (Finset.sort_nodup _ (M.edgeMarkLE e)).map Subtype.val_injective

theorem edgeMarkList_pairwise_parameter_le (e : K.Edge) :
    (M.edgeMarkList e).Pairwise fun p q ↦
      M.edgeParameterValue e p ≤ M.edgeParameterValue e q := by
  classical
  unfold edgeMarkList
  simp only [List.pairwise_map]
  apply (Finset.pairwise_sort (M.edgeMarks e).attach (M.edgeMarkLE e)).imp
  intro p q hpq
  exact hpq

theorem edgeFirstPoint_ne_edgeSecondPoint (e : K.Edge) :
    K.edgeFirstPoint e ≠ K.edgeSecondPoint e := by
  intro h
  have hcoord := congrArg
    (fun p : K.realization ↦ p.1 (K.edgeFirst e)) h
  simp [edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
    K.edgeFirst_ne_edgeSecond e] at hcoord

theorem two_le_edgeMarks_card (e : K.Edge) :
    2 ≤ (M.edgeMarks e).card := by
  rw [Nat.succ_le_iff]
  apply Finset.one_lt_card.mpr
  exact ⟨K.edgeFirstPoint e, M.edgeFirstPoint_mem_edgeMarks e,
    K.edgeSecondPoint e, M.edgeSecondPoint_mem_edgeMarks e,
    edgeFirstPoint_ne_edgeSecondPoint e⟩

theorem two_le_edgeMarkList_length (e : K.Edge) :
    2 ≤ (M.edgeMarkList e).length := by
  rw [← List.toFinset_card_of_nodup (M.edgeMarkList_nodup e)]
  rw [show (M.edgeMarkList e).toFinset = M.edgeMarks e by
    ext p
    simp only [List.mem_toFinset, M.mem_edgeMarkList_iff e]]
  exact M.two_le_edgeMarks_card e

@[simp] theorem edgeParameter_edgeFirstPoint (e : K.Edge) :
    M.edgeParameterValue e (K.edgeFirstPoint e) = 0 := by
  rw [M.edgeParameterValue_eq e
    ((M.mem_edgeMarks_iff e _).mp (M.edgeFirstPoint_mem_edgeMarks e)).2,
    K.edgeParameter_eq_secondCoordinate]
  simp [edgeFirstPoint, edgeVertexPoint, K.edgeFirst_ne_edgeSecond e]

@[simp] theorem edgeParameter_edgeSecondPoint (e : K.Edge) :
    M.edgeParameterValue e (K.edgeSecondPoint e) = 1 := by
  rw [M.edgeParameterValue_eq e
    ((M.mem_edgeMarks_iff e _).mp (M.edgeSecondPoint_mem_edgeMarks e)).2,
    K.edgeParameter_eq_secondCoordinate]
  simp [edgeSecondPoint, edgeVertexPoint]

theorem edgeParameterValue_mem_Icc (e : K.Edge) {p : K.realization}
    (hp : p ∈ K.faceCarrier e.1) :
    M.edgeParameterValue e p ∈ Set.Icc (0 : ℝ) 1 := by
  rw [M.edgeParameterValue_eq e hp]
  exact (K.edgeParameter e p hp).2

theorem edgeMarkList_first_parameter (e : K.Edge) :
    M.edgeParameterValue e
      ((M.edgeMarkList e).get ⟨0, by
        have := M.two_le_edgeMarkList_length e
        omega⟩) = 0 := by
  let L := M.edgeMarkList e
  let first : Fin L.length := ⟨0, by
    dsimp only [L]
    have := M.two_le_edgeMarkList_length e
    omega⟩
  have hfirstEdge : L.get first ∈ K.faceCarrier e.1 :=
    ((M.mem_edgeMarks_iff e _).mp
      ((M.mem_edgeMarkList_iff e _).mp (List.get_mem L first))).2
  have hnonneg := (M.edgeParameterValue_mem_Icc e hfirstEdge).1
  have hcornerL : K.edgeFirstPoint e ∈ L :=
    (M.mem_edgeMarkList_iff e _).mpr (M.edgeFirstPoint_mem_edgeMarks e)
  obtain ⟨k, hk⟩ := List.get_of_mem hcornerL
  have hle : M.edgeParameterValue e (L.get first) ≤ 0 := by
    by_cases hkfirst : k = first
    · subst k
      simpa only [L, first, hk] using
        M.edgeParameter_edgeFirstPoint e |>.le
    · have hlt : first < k := by
        have hk0 : k.1 ≠ 0 := by
          intro hk0
          apply hkfirst
          apply Fin.ext
          simpa only [first] using hk0
        change 0 < k.1
        omega
      have h := (M.edgeMarkList_pairwise_parameter_le e).rel_get_of_lt hlt
      rw [hk, M.edgeParameter_edgeFirstPoint e] at h
      exact h
  exact le_antisymm hle hnonneg

theorem edgeMarkList_last_parameter (e : K.Edge) :
    M.edgeParameterValue e
      ((M.edgeMarkList e).get
        ⟨(M.edgeMarkList e).length - 1, by
          have := M.two_le_edgeMarkList_length e
          omega⟩) = 1 := by
  let L := M.edgeMarkList e
  let last : Fin L.length := ⟨L.length - 1, by
    dsimp only [L]
    have := M.two_le_edgeMarkList_length e
    omega⟩
  have hlastEdge : L.get last ∈ K.faceCarrier e.1 :=
    ((M.mem_edgeMarks_iff e _).mp
      ((M.mem_edgeMarkList_iff e _).mp (List.get_mem L last))).2
  have hupper := (M.edgeParameterValue_mem_Icc e hlastEdge).2
  have hcornerL : K.edgeSecondPoint e ∈ L :=
    (M.mem_edgeMarkList_iff e _).mpr (M.edgeSecondPoint_mem_edgeMarks e)
  obtain ⟨k, hk⟩ := List.get_of_mem hcornerL
  have hle : 1 ≤ M.edgeParameterValue e (L.get last) := by
    by_cases hklast : k = last
    · subst k
      simpa only [L, last, hk] using
        M.edgeParameter_edgeSecondPoint e |>.ge
    · have hlt : k < last := by
        have hkne : k.1 ≠ L.length - 1 := by
          intro hkne
          apply hklast
          apply Fin.ext
          simpa only [last] using hkne
        change k.1 < L.length - 1
        omega
      have h := (M.edgeMarkList_pairwise_parameter_le e).rel_get_of_lt hlt
      rw [hk, M.edgeParameter_edgeSecondPoint e] at h
      exact h
  exact le_antisymm hupper hle

/-- Consecutive intervals in the globally ordered mark list. -/
abbrev EdgeInterval (e : K.Edge) := Fin ((M.edgeMarkList e).length - 1)

/-- The `edgeIntervalFirst` declaration. -/
noncomputable def edgeIntervalFirst (e : K.Edge) (j : M.EdgeInterval e) :
    K.realization :=
  (M.edgeMarkList e).get ⟨j.1, by
    have := j.2
    omega⟩

/-- The `edgeIntervalSecond` declaration. -/
noncomputable def edgeIntervalSecond (e : K.Edge) (j : M.EdgeInterval e) :
    K.realization :=
  (M.edgeMarkList e).get ⟨j.1 + 1, by
    have := j.2
    omega⟩

theorem edgeIntervalFirst_mem_edgeMarks (e : K.Edge)
    (j : M.EdgeInterval e) :
    M.edgeIntervalFirst e j ∈ M.edgeMarks e := by
  rw [← M.mem_edgeMarkList_iff e]
  exact List.get_mem _ _

theorem edgeIntervalSecond_mem_edgeMarks (e : K.Edge)
    (j : M.EdgeInterval e) :
    M.edgeIntervalSecond e j ∈ M.edgeMarks e := by
  rw [← M.mem_edgeMarkList_iff e]
  exact List.get_mem _ _

/-- The first endpoint of a marked edge interval lies on the underlying geometric edge. -/
theorem edgeIntervalFirst_mem_faceCarrier (e : K.Edge)
    (j : M.EdgeInterval e) :
    M.edgeIntervalFirst e j ∈ K.faceCarrier e.1 :=
  ((M.mem_edgeMarks_iff e _).mp
    (M.edgeIntervalFirst_mem_edgeMarks e j)).2

/-- The second endpoint of a marked edge interval lies on the underlying geometric edge. -/
theorem edgeIntervalSecond_mem_faceCarrier (e : K.Edge)
    (j : M.EdgeInterval e) :
    M.edgeIntervalSecond e j ∈ K.faceCarrier e.1 :=
  ((M.mem_edgeMarks_iff e _).mp
    (M.edgeIntervalSecond_mem_edgeMarks e j)).2

theorem edgeIntervalFirst_ne_second (e : K.Edge)
    (j : M.EdgeInterval e) :
    M.edgeIntervalFirst e j ≠ M.edgeIntervalSecond e j := by
  intro h
  have hn := M.edgeMarkList_nodup e
  have hij := hn.injective_get h
  have hval := congrArg Fin.val hij
  simp only at hval
  omega

/-- The first marked endpoint determines a consecutive interval uniquely. -/
theorem edgeInterval_eq_of_first_eq (e : K.Edge)
    {a b : M.EdgeInterval e}
    (h : M.edgeIntervalFirst e a = M.edgeIntervalFirst e b) :
    a = b := by
  apply Fin.ext
  have hindex := (M.edgeMarkList_nodup e).injective_get h
  exact congrArg
    (fun i : Fin (M.edgeMarkList e).length ↦ i.1) hindex

/-- The second marked endpoint determines a consecutive interval uniquely. -/
theorem edgeInterval_eq_of_second_eq (e : K.Edge)
    {a b : M.EdgeInterval e}
    (h : M.edgeIntervalSecond e a = M.edgeIntervalSecond e b) :
    a = b := by
  apply Fin.ext
  have hindex := (M.edgeMarkList_nodup e).injective_get h
  have hval : a.1 + 1 = b.1 + 1 :=
    congrArg
      (fun i : Fin (M.edgeMarkList e).length ↦ i.1) hindex
  omega

/-- Three consecutive intervals on one ordered marked edge which all meet at the same marked
point cannot be pairwise distinct. -/
theorem edgeInterval_pair_eq_of_three_common_endpoint (e : K.Edge)
    (a b c : M.EdgeInterval e) (p : K.realization)
    (ha : p = M.edgeIntervalFirst e a ∨
      p = M.edgeIntervalSecond e a)
    (hb : p = M.edgeIntervalFirst e b ∨
      p = M.edgeIntervalSecond e b)
    (hc : p = M.edgeIntervalFirst e c ∨
      p = M.edgeIntervalSecond e c) :
    a = b ∨ a = c ∨ b = c := by
  rcases ha with ha | ha <;>
    rcases hb with hb | hb <;>
      rcases hc with hc | hc
  · exact Or.inl (M.edgeInterval_eq_of_first_eq e (ha.symm.trans hb))
  · exact Or.inl (M.edgeInterval_eq_of_first_eq e (ha.symm.trans hb))
  · exact Or.inr (Or.inl
      (M.edgeInterval_eq_of_first_eq e (ha.symm.trans hc)))
  · exact Or.inr (Or.inr
      (M.edgeInterval_eq_of_second_eq e (hb.symm.trans hc)))
  · exact Or.inr (Or.inr
      (M.edgeInterval_eq_of_first_eq e (hb.symm.trans hc)))
  · exact Or.inr (Or.inl
      (M.edgeInterval_eq_of_second_eq e (ha.symm.trans hc)))
  · exact Or.inl (M.edgeInterval_eq_of_second_eq e (ha.symm.trans hb))
  · exact Or.inl (M.edgeInterval_eq_of_second_eq e (ha.symm.trans hb))

theorem edgeInterval_parameter_lt (e : K.Edge)
    (j : M.EdgeInterval e) :
    M.edgeParameterValue e (M.edgeIntervalFirst e j) <
      M.edgeParameterValue e (M.edgeIntervalSecond e j) := by
  have hle :
      M.edgeParameterValue e (M.edgeIntervalFirst e j) ≤
        M.edgeParameterValue e (M.edgeIntervalSecond e j) := by
    let a : Fin (M.edgeMarkList e).length := ⟨j.1, by omega⟩
    let b : Fin (M.edgeMarkList e).length := ⟨j.1 + 1, by omega⟩
    exact (M.edgeMarkList_pairwise_parameter_le e).rel_get_of_lt
      (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j.1))
  exact lt_of_le_of_ne hle fun hEq ↦
    M.edgeIntervalFirst_ne_second e j
      (M.edgeParameterValue_injOn e
        ((M.mem_edgeMarks_iff e _).mp
          (M.edgeIntervalFirst_mem_edgeMarks e j)).2
        ((M.mem_edgeMarks_iff e _).mp
          (M.edgeIntervalSecond_mem_edgeMarks e j)).2 hEq)

/-- At an abstract endpoint of an old edge there is only one incident consecutive interval on
that edge. -/
theorem edgeInterval_eq_of_common_vertex_endpoint (e : K.Edge)
    (a b : M.EdgeInterval e) (v : K.UsedVertex) (hve : v.1 ∈ e.1)
    (ha : K.vertexPoint v = M.edgeIntervalFirst e a ∨
      K.vertexPoint v = M.edgeIntervalSecond e a)
    (hb : K.vertexPoint v = M.edgeIntervalFirst e b ∨
      K.vertexPoint v = M.edgeIntervalSecond e b) :
    a = b := by
  have hfirstNonneg (j : M.EdgeInterval e) :
      0 ≤ M.edgeParameterValue e (M.edgeIntervalFirst e j) :=
    (M.edgeParameterValue_mem_Icc e
      (((M.mem_edgeMarks_iff e _).mp
        (M.edgeIntervalFirst_mem_edgeMarks e j)).2)).1
  have hsecondLe (j : M.EdgeInterval e) :
      M.edgeParameterValue e (M.edgeIntervalSecond e j) ≤ 1 :=
    (M.edgeParameterValue_mem_Icc e
      (((M.mem_edgeMarks_iff e _).mp
        (M.edgeIntervalSecond_mem_edgeMarks e j)).2)).2
  rw [K.edge_eq_pair e] at hve
  simp only [Finset.mem_insert, Finset.mem_singleton] at hve
  rcases hve with hvFirst | hvSecond
  · have hp : K.vertexPoint v = K.edgeFirstPoint e := by
      rw [← K.vertexPoint_edgeFirstUsed e]
      congr 1
      exact Subtype.ext hvFirst
    have hpZero :
        M.edgeParameterValue e (K.vertexPoint v) = 0 := by
      rw [hp, M.edgeParameter_edgeFirstPoint]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact M.edgeInterval_eq_of_first_eq e (ha.symm.trans hb)
    · have hlt := M.edgeInterval_parameter_lt e b
      rw [← hb, hpZero] at hlt
      exact False.elim ((not_lt_of_ge (hfirstNonneg b)) hlt)
    · have hlt := M.edgeInterval_parameter_lt e a
      rw [← ha, hpZero] at hlt
      exact False.elim ((not_lt_of_ge (hfirstNonneg a)) hlt)
    · exact M.edgeInterval_eq_of_second_eq e (ha.symm.trans hb)
  · have hp : K.vertexPoint v = K.edgeSecondPoint e := by
      rw [← K.vertexPoint_edgeSecondUsed e]
      congr 1
      exact Subtype.ext hvSecond
    have hpOne :
        M.edgeParameterValue e (K.vertexPoint v) = 1 := by
      rw [hp, M.edgeParameter_edgeSecondPoint]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact M.edgeInterval_eq_of_first_eq e (ha.symm.trans hb)
    · have hlt := M.edgeInterval_parameter_lt e a
      rw [← ha, hpOne] at hlt
      exact False.elim ((not_lt_of_ge (hsecondLe a)) hlt)
    · have hlt := M.edgeInterval_parameter_lt e b
      rw [← hb, hpOne] at hlt
      exact False.elim ((not_lt_of_ge (hsecondLe b)) hlt)
    · exact M.edgeInterval_eq_of_second_eq e (ha.symm.trans hb)

/-- Earlier consecutive intervals on one globally ordered edge end no later than later intervals
begin. -/
theorem edgeIntervalSecond_parameter_le_first_of_lt (e : K.Edge)
    (a b : M.EdgeInterval e) (hab : a.1 < b.1) :
    M.edgeParameterValue e (M.edgeIntervalSecond e a) ≤
      M.edgeParameterValue e (M.edgeIntervalFirst e b) := by
  let L := M.edgeMarkList e
  let ka : Fin L.length := ⟨a.1 + 1, by
    have ha := a.2
    dsimp only [L]
    omega⟩
  let kb : Fin L.length := ⟨b.1, by
    have hb := b.2
    dsimp only [L]
    omega⟩
  have hle : ka ≤ kb := by
    change a.1 + 1 ≤ b.1
    omega
  rcases hle.eq_or_lt with heq | hlt
  · change M.edgeParameterValue e (L.get ka) ≤
      M.edgeParameterValue e (L.get kb)
    rw [heq]
  · have hp := (M.edgeMarkList_pairwise_parameter_le e).rel_get_of_lt hlt
    simpa only [edgeIntervalSecond, edgeIntervalFirst, L, ka, kb] using hp

/-- Two open consecutive parameter intervals on the same marked edge can overlap only when their
indices agree. -/
theorem edgeInterval_eq_of_parameter_mem_Ioo (e : K.Edge)
    (a b : M.EdgeInterval e) {z : ℝ}
    (ha : z ∈ Set.Ioo
      (M.edgeParameterValue e (M.edgeIntervalFirst e a))
      (M.edgeParameterValue e (M.edgeIntervalSecond e a)))
    (hb : z ∈ Set.Ioo
      (M.edgeParameterValue e (M.edgeIntervalFirst e b))
      (M.edgeParameterValue e (M.edgeIntervalSecond e b))) :
    a = b := by
  apply Fin.ext
  rcases lt_trichotomy a.1 b.1 with hab | hab | hba
  · have hsep := M.edgeIntervalSecond_parameter_le_first_of_lt e a b hab
    exact False.elim ((not_lt_of_ge (ha.2.trans_le hsep).le) hb.1)
  · exact hab
  · have hsep := M.edgeIntervalSecond_parameter_le_first_of_lt e b a hba
    exact False.elim ((not_lt_of_ge (hb.2.trans_le hsep).le) ha.1)

/-- Open consecutive intervals on propositionally equal abstract edges have the same two
geometric endpoints whenever their parameter interiors overlap. -/
theorem edgeInterval_endpoints_eq_of_edge_eq_of_parameter_mem_Ioo
    {e d : K.Edge} (hed : e = d)
    (a : M.EdgeInterval e) (b : M.EdgeInterval d) {z : ℝ}
    (ha : z ∈ Set.Ioo
      (M.edgeParameterValue e (M.edgeIntervalFirst e a))
      (M.edgeParameterValue e (M.edgeIntervalSecond e a)))
    (hb : z ∈ Set.Ioo
      (M.edgeParameterValue d (M.edgeIntervalFirst d b))
      (M.edgeParameterValue d (M.edgeIntervalSecond d b))) :
    M.edgeIntervalFirst e a = M.edgeIntervalFirst d b ∧
      M.edgeIntervalSecond e a = M.edgeIntervalSecond d b := by
  subst d
  have hab := M.edgeInterval_eq_of_parameter_mem_Ioo e a b ha hb
  subst b
  exact ⟨rfl, rfl⟩

/-- Every point of an abstract edge lies between two consecutive global marks. -/
theorem exists_edgeInterval_containing (e : K.Edge) (p : K.realization)
    (hp : p ∈ K.faceCarrier e.1) :
    ∃ j : M.EdgeInterval e,
      M.edgeParameterValue e (M.edgeIntervalFirst e j) ≤
        M.edgeParameterValue e p ∧
      M.edgeParameterValue e p ≤
        M.edgeParameterValue e (M.edgeIntervalSecond e j) := by
  let L := M.edgeMarkList e
  have hlength : 2 ≤ L.length := M.two_le_edgeMarkList_length e
  have hfirst :
      M.edgeParameterValue e (L.get ⟨0, by omega⟩) ≤
        M.edgeParameterValue e p := by
    rw [M.edgeMarkList_first_parameter e]
    exact (M.edgeParameterValue_mem_Icc e hp).1
  have hlast :
      M.edgeParameterValue e p ≤
        M.edgeParameterValue e (L.get ⟨L.length - 1, by omega⟩) := by
    rw [M.edgeMarkList_last_parameter e]
    exact (M.edgeParameterValue_mem_Icc e hp).2
  exact exists_adjacent_get_of_pairwise_le
    (r := M.edgeParameterValue e p) L (M.edgeParameterValue e)
    hlength (M.edgeMarkList_pairwise_parameter_le e) hfirst hlast

/-- No marked point lies strictly between the endpoints of a consecutive interval. -/
theorem not_edgeMark_parameter_mem_Ioo (e : K.Edge)
    (j : M.EdgeInterval e) {p : K.realization} (hp : p ∈ M.edgeMarks e) :
    ¬M.edgeParameterValue e p ∈ Set.Ioo
      (M.edgeParameterValue e (M.edgeIntervalFirst e j))
      (M.edgeParameterValue e (M.edgeIntervalSecond e j)) := by
  intro hpOpen
  have hpList : p ∈ M.edgeMarkList e :=
    (M.mem_edgeMarkList_iff e p).mpr hp
  obtain ⟨k, hk⟩ := List.get_of_mem hpList
  by_cases hkLeft : k.1 ≤ j.1
  · let a : Fin (M.edgeMarkList e).length := ⟨j.1, by omega⟩
    have hka : k ≤ a := hkLeft
    have hparam :
        M.edgeParameterValue e (M.edgeMarkList e |>.get k) ≤
          M.edgeParameterValue e (M.edgeMarkList e |>.get a) := by
      rcases hka.eq_or_lt with hEq | hLt
      · exact le_of_eq
          (congrArg
            (fun i : Fin (M.edgeMarkList e).length ↦
              M.edgeParameterValue e ((M.edgeMarkList e).get i)) hEq)
      · exact (M.edgeMarkList_pairwise_parameter_le e).rel_get_of_lt hLt
    rw [hk] at hparam
    exact (not_lt_of_ge hparam) hpOpen.1
  · have hjk : j.1 + 1 ≤ k.1 := by omega
    let b : Fin (M.edgeMarkList e).length := ⟨j.1 + 1, by omega⟩
    have hbk : b ≤ k := hjk
    have hparam :
        M.edgeParameterValue e (M.edgeMarkList e |>.get b) ≤
          M.edgeParameterValue e (M.edgeMarkList e |>.get k) := by
      rcases hbk.eq_or_lt with hEq | hLt
      · exact le_of_eq
          (congrArg
            (fun i : Fin (M.edgeMarkList e).length ↦
              M.edgeParameterValue e ((M.edgeMarkList e).get i)) hEq)
      · exact (M.edgeMarkList_pairwise_parameter_le e).rel_get_of_lt hLt
    rw [hk] at hparam
    exact (not_lt_of_ge hparam) hpOpen.2

end EdgeMarking

/-- The barycentric center of an intrinsic maximal face. -/
noncomputable def faceCenter (t : K.Face) : K.realization :=
  K.faceStandardMap t (K.faceCenterSimplex t)

theorem faceCenter_mem_faceCarrier (t : K.Face) :
    K.faceCenter t ∈ K.faceCarrier t.1 := by
  intro v hv
  rw [faceCenter, K.faceStandardMap_val,
    extendFaceCoordinates_of_notMem t.1 _ hv]

theorem faceCenter_coordinate (t : K.Face) {v : K.Vertex} (hv : v ∈ t.1) :
    (K.faceCenter t).1 v = 1 / 3 := by
  rw [faceCenter, K.faceStandardMap_val,
    extendFaceCoordinates_of_mem t.1 _ hv]
  rfl

/-- A barycentric face center is not a vertex point. -/
theorem faceCenter_ne_vertexPoint (t : K.Face) (v : K.UsedVertex) :
    K.faceCenter t ≠ K.vertexPoint v := by
  intro h
  have hcoord := congrArg (fun x : K.realization ↦ x.1 v.1) h
  by_cases hvt : v.1 ∈ t.1
  · rw [K.faceCenter_coordinate t hvt] at hcoord
    norm_num [vertexPoint] at hcoord
  · have hzero : (K.faceCenter t).1 v.1 = 0 :=
      K.faceCenter_mem_faceCarrier t v.1 hvt
    rw [hzero] at hcoord
    norm_num [vertexPoint] at hcoord

/-- Distinct maximal intrinsic faces have distinct barycentric centers. -/
theorem faceCenter_injective : Function.Injective K.faceCenter := by
  intro t u htu
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro v hvt
    by_contra hvu
    have huZero : (K.faceCenter u).1 v = 0 :=
      K.faceCenter_mem_faceCarrier u v hvu
    have hcoord := congrArg
      (fun p : K.realization ↦ p.1 v) htu
    rw [K.faceCenter_coordinate t hvt, huZero] at hcoord
    norm_num at hcoord
  · rw [K.faces_card t.1 t.2, K.faces_card u.1 u.2]

/-- A barycentric face center cannot lie on any abstract edge of the intrinsic complex. -/
theorem faceCenter_ne_mem_edgeCarrier (t : K.Face) (e : K.Edge)
    {p : K.realization} (hp : p ∈ K.faceCarrier e.1) :
    K.faceCenter t ≠ p := by
  intro htp
  have hsub : t.1 ⊆ e.1 := by
    intro v hvt
    by_contra hve
    have hpZero : p.1 v = 0 := hp v hve
    have hcoord := congrArg
      (fun q : K.realization ↦ q.1 v) htp
    rw [K.faceCenter_coordinate t hvt, hpZero] at hcoord
    norm_num at hcoord
  have hcard :=
    Finset.card_le_card hsub
  rw [K.faces_card t.1 t.2, K.card_of_mem_edges e.2] at hcard
  omega

/-- Two abstract edges which contain the same two distinct intrinsic points are equal. -/
theorem edge_eq_of_two_distinct_common_points (e d : K.Edge)
    {p q : K.realization} (hpE : p ∈ K.faceCarrier e.1)
    (hpD : p ∈ K.faceCarrier d.1) (hqE : q ∈ K.faceCarrier e.1)
    (hqD : q ∈ K.faceCarrier d.1) (hpq : p ≠ q) :
    e = d := by
  by_contra hed
  have hinterLe : (e.1 ∩ d.1).card ≤ 1 := by
    by_contra hle
    have hinterTwo : (e.1 ∩ d.1).card = 2 := by
      have hupper :=
        Finset.card_le_card
          (Finset.inter_subset_left : e.1 ∩ d.1 ⊆ e.1)
      rw [K.card_of_mem_edges e.2] at hupper
      omega
    have heqE : e.1 ∩ d.1 = e.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [K.card_of_mem_edges e.2, hinterTwo])
    have heqD : e.1 ∩ d.1 = d.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [K.card_of_mem_edges d.2, hinterTwo])
    exact hed (Subtype.ext (heqE.symm.trans heqD))
  have hpInter : p ∈ K.faceCarrier (e.1 ∩ d.1) := by
    rw [← K.faceCarrier_inter]
    exact ⟨hpE, hpD⟩
  have hnonempty : (e.1 ∩ d.1).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, K.faceCarrier_empty] at hpInter
    exact hpInter
  have hinterOne : (e.1 ∩ d.1).card = 1 := by
    have hpos := Finset.card_pos.mpr hnonempty
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hinterOne
  let t : K.Face := ⟨K.edgeParent e, K.edgeParent_mem e⟩
  have hvt : v ∈ t.1 := by
    apply K.edge_subset_parent e
    apply Finset.inter_subset_left
    rw [hv]
    exact Finset.mem_singleton_self v
  let vt : t.1 := ⟨v, hvt⟩
  have hpSingle : p ∈ K.faceCarrier ({v} : Finset K.Vertex) := by
    rwa [hv] at hpInter
  have hqInter : q ∈ K.faceCarrier (e.1 ∩ d.1) := by
    rw [← K.faceCarrier_inter]
    exact ⟨hqE, hqD⟩
  have hqSingle : q ∈ K.faceCarrier ({v} : Finset K.Vertex) := by
    rwa [hv] at hqInter
  apply hpq
  exact
    (K.eq_facePoint_of_mem_faceCarrier_singleton t vt p hpSingle).trans
      (K.eq_facePoint_of_mem_faceCarrier_singleton t vt q hqSingle).symm

theorem intrinsicFaceVertex_add_two_not_mem_faceEdge (t : K.Face) (i : ZMod 3) :
    K.faceVertex t (i + 2) ∉ (K.faceEdge t i).1 := by
  rw [K.faceEdge_val]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · exact (K.faceVertex_ne_add_two t i).symm
  · have h := K.faceVertex_ne_next t (i + 1)
    simpa only [add_assoc, show (1 : ZMod 3) + 1 = 2 by decide] using h.symm

theorem faceCenter_ne_mem_faceEdge (t : K.Face) (i : ZMod 3)
    {p : K.realization} (hp : p ∈ K.faceCarrier (K.faceEdge t i).1) :
    K.faceCenter t ≠ p := by
  intro h
  have hcoord := congrArg
    (fun q : K.realization ↦ q.1 (K.faceVertex t (i + 2))) h
  have hzero :
      p.1 (K.faceVertex t (i + 2)) = 0 :=
    hp _ (K.intrinsicFaceVertex_add_two_not_mem_faceEdge t i)
  rw [K.faceCenter_coordinate t (K.faceVertex_mem t (i + 2)), hzero] at hcoord
  norm_num at hcoord

namespace EdgeMarking

variable {K : IntrinsicTwoComplex} (M : K.EdgeMarking)

/-- One fan triangle is indexed by an old face, one of its cyclic edges, and one consecutive
interval in the global mark order on that edge. -/
abbrev FanFace :=
  Σ t : K.Face, Σ i : ZMod 3, M.EdgeInterval (K.faceEdge t i)

/-- The `fanFaceVertices` declaration. -/
noncomputable def fanFaceVertices (f : M.FanFace) : Finset K.realization :=
  {K.faceCenter f.1,
    M.edgeIntervalFirst (K.faceEdge f.1 f.2.1) f.2.2,
    M.edgeIntervalSecond (K.faceEdge f.1 f.2.1) f.2.2}

theorem fanFaceVertices_card (f : M.FanFace) :
    (M.fanFaceVertices f).card = 3 := by
  let e := K.faceEdge f.1 f.2.1
  have hfirstEdge :
      M.edgeIntervalFirst e f.2.2 ∈ K.faceCarrier e.1 :=
    ((M.mem_edgeMarks_iff e _).mp
      (M.edgeIntervalFirst_mem_edgeMarks e f.2.2)).2
  have hsecondEdge :
      M.edgeIntervalSecond e f.2.2 ∈ K.faceCarrier e.1 :=
    ((M.mem_edgeMarks_iff e _).mp
      (M.edgeIntervalSecond_mem_edgeMarks e f.2.2)).2
  have hcfirst :
      K.faceCenter f.1 ≠ M.edgeIntervalFirst e f.2.2 :=
    K.faceCenter_ne_mem_faceEdge f.1 f.2.1 hfirstEdge
  have hcsecond :
      K.faceCenter f.1 ≠ M.edgeIntervalSecond e f.2.2 :=
    K.faceCenter_ne_mem_faceEdge f.1 f.2.1 hsecondEdge
  have hfirstSecond :
      M.edgeIntervalFirst e f.2.2 ≠ M.edgeIntervalSecond e f.2.2 :=
    M.edgeIntervalFirst_ne_second e f.2.2
  simp [fanFaceVertices, e, hcfirst, hcsecond, hfirstSecond]

/-- A fan center is never one of the marked base vertices of any fan triangle. -/
theorem fanCenter_ne_fanFirst (f g : M.FanFace) :
    K.faceCenter f.1 ≠
      M.edgeIntervalFirst (K.faceEdge g.1 g.2.1) g.2.2 := by
  apply K.faceCenter_ne_mem_edgeCarrier f.1
    (K.faceEdge g.1 g.2.1)
  exact ((M.mem_edgeMarks_iff (K.faceEdge g.1 g.2.1) _).mp
    (M.edgeIntervalFirst_mem_edgeMarks
      (K.faceEdge g.1 g.2.1) g.2.2)).2

/-- A fan center is never the other marked base vertex of any fan triangle. -/
theorem fanCenter_ne_fanSecond (f g : M.FanFace) :
    K.faceCenter f.1 ≠
      M.edgeIntervalSecond (K.faceEdge g.1 g.2.1) g.2.2 := by
  apply K.faceCenter_ne_mem_edgeCarrier f.1
    (K.faceEdge g.1 g.2.1)
  exact ((M.mem_edgeMarks_iff (K.faceEdge g.1 g.2.1) _).mp
    (M.edgeIntervalSecond_mem_edgeMarks
      (K.faceEdge g.1 g.2.1) g.2.2)).2

/-- The center of one fan triangle occurs among the vertices of another exactly when their old
parent faces agree. -/
theorem faceCenter_mem_fanFaceVertices_iff (f g : M.FanFace) :
    K.faceCenter f.1 ∈ M.fanFaceVertices g ↔ f.1 = g.1 := by
  constructor
  · intro h
    simp only [fanFaceVertices, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact K.faceCenter_injective h
    · exact False.elim (M.fanCenter_ne_fanFirst f g h)
    · exact False.elim (M.fanCenter_ne_fanSecond f g h)
  · intro h
    rw [h]
    simp [fanFaceVertices]

/-- Removing the center from a two-element subface of a fan triangle leaves exactly its marked
base pair. -/
theorem eq_fanBase_of_card_two_of_subset_of_center_notMem
    (f : M.FanFace) {e : Finset K.realization}
    (hecard : e.card = 2) (hef : e ⊆ M.fanFaceVertices f)
    (hcenter : K.faceCenter f.1 ∉ e) :
    e =
      {M.edgeIntervalFirst (K.faceEdge f.1 f.2.1) f.2.2,
        M.edgeIntervalSecond (K.faceEdge f.1 f.2.1) f.2.2} := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    have hp' := hef hp
    simp only [fanFaceVertices, Finset.mem_insert, Finset.mem_singleton] at hp'
    rcases hp' with hp' | hp' | hp'
    · exact False.elim (hcenter (hp' ▸ hp))
    · simp [hp']
    · simp [hp']
  · rw [hecard]
    simp [M.edgeIntervalFirst_ne_second
      (K.faceEdge f.1 f.2.1) f.2.2]

/-- Three fan triangles with one old parent which all contain the same radial edge cannot be
pairwise distinct.  Away from an old vertex all three bases lie on one globally ordered old
edge; at an old vertex there are only the two cyclic sides of the parent triangle. -/
theorem fanFaceVertices_pair_eq_of_three_same_parent_endpoint
    (f g h : M.FanFace) (p : K.realization)
    (hfg : f.1 = g.1) (hfh : f.1 = h.1)
    (hf : p =
        M.edgeIntervalFirst (K.faceEdge f.1 f.2.1) f.2.2 ∨
      p = M.edgeIntervalSecond (K.faceEdge f.1 f.2.1) f.2.2)
    (hg : p =
        M.edgeIntervalFirst (K.faceEdge g.1 g.2.1) g.2.2 ∨
      p = M.edgeIntervalSecond (K.faceEdge g.1 g.2.1) g.2.2)
    (hh : p =
        M.edgeIntervalFirst (K.faceEdge h.1 h.2.1) h.2.2 ∨
      p = M.edgeIntervalSecond (K.faceEdge h.1 h.2.1) h.2.2) :
    M.fanFaceVertices f = M.fanFaceVertices g ∨
      M.fanFaceVertices f = M.fanFaceVertices h ∨
      M.fanFaceVertices g = M.fanFaceVertices h := by
  rcases f with ⟨t, i, a⟩
  rcases g with ⟨u, j, b⟩
  rcases h with ⟨w, k, d⟩
  change t = u at hfg
  change t = w at hfh
  subst u
  subst w
  have hpEdgeI : p ∈ K.faceCarrier (K.faceEdge t i).1 := by
    rcases hf with hf | hf
    · rw [hf]
      exact ((M.mem_edgeMarks_iff (K.faceEdge t i) _).mp
        (M.edgeIntervalFirst_mem_edgeMarks (K.faceEdge t i) a)).2
    · rw [hf]
      exact ((M.mem_edgeMarks_iff (K.faceEdge t i) _).mp
        (M.edgeIntervalSecond_mem_edgeMarks (K.faceEdge t i) a)).2
  have hpEdgeJ : p ∈ K.faceCarrier (K.faceEdge t j).1 := by
    rcases hg with hg | hg
    · rw [hg]
      exact ((M.mem_edgeMarks_iff (K.faceEdge t j) _).mp
        (M.edgeIntervalFirst_mem_edgeMarks (K.faceEdge t j) b)).2
    · rw [hg]
      exact ((M.mem_edgeMarks_iff (K.faceEdge t j) _).mp
        (M.edgeIntervalSecond_mem_edgeMarks (K.faceEdge t j) b)).2
  have hpEdgeK : p ∈ K.faceCarrier (K.faceEdge t k).1 := by
    rcases hh with hh | hh
    · rw [hh]
      exact ((M.mem_edgeMarks_iff (K.faceEdge t k) _).mp
        (M.edgeIntervalFirst_mem_edgeMarks (K.faceEdge t k) d)).2
    · rw [hh]
      exact ((M.mem_edgeMarks_iff (K.faceEdge t k) _).mp
        (M.edgeIntervalSecond_mem_edgeMarks (K.faceEdge t k) d)).2
  by_cases hpVertex : K.IsGraphVertexPoint p
  · obtain ⟨v, hpv⟩ := hpVertex
    have hvi : v.1 ∈ (K.faceEdge t i).1 := by
      apply (K.vertexPoint_mem_faceCarrier_iff v _).mp
      rwa [← hpv]
    have hvj : v.1 ∈ (K.faceEdge t j).1 := by
      apply (K.vertexPoint_mem_faceCarrier_iff v _).mp
      rwa [← hpv]
    have hvk : v.1 ∈ (K.faceEdge t k).1 := by
      apply (K.vertexPoint_mem_faceCarrier_iff v _).mp
      rwa [← hpv]
    have hvt : v.1 ∈ t.1 :=
      K.faceEdge_subset_face t i hvi
    obtain ⟨l, hl⟩ := K.exists_faceVertex_eq_of_mem t hvt
    have sideCases (r : ZMod 3) (hvr : v.1 ∈ (K.faceEdge t r).1) :
        r = l ∨ r = l + 2 := by
      have hmem : K.faceVertex t l ∈ (K.faceEdge t r).1 := by
        rwa [hl]
      simp only [K.faceEdge_val, Finset.mem_insert,
        Finset.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · exact Or.inl (K.faceVertex_injective t hmem).symm
      · apply Or.inr
        exact
          (by decide :
            ∀ l r : ZMod 3, l = r + 1 → r = l + 2)
            l r (K.faceVertex_injective t hmem)
    have hindices : i = j ∨ i = k ∨ j = k := by
      rcases sideCases i hvi with hi | hi <;>
        rcases sideCases j hvj with hj | hj <;>
          rcases sideCases k hvk with hk | hk
      · exact Or.inl (hi.trans hj.symm)
      · exact Or.inl (hi.trans hj.symm)
      · exact Or.inr (Or.inl (hi.trans hk.symm))
      · exact Or.inr (Or.inr (hj.trans hk.symm))
      · exact Or.inr (Or.inr (hj.trans hk.symm))
      · exact Or.inr (Or.inl (hi.trans hk.symm))
      · exact Or.inl (hi.trans hj.symm)
      · exact Or.inl (hi.trans hj.symm)
    have hf' :
        K.vertexPoint v = M.edgeIntervalFirst (K.faceEdge t i) a ∨
          K.vertexPoint v = M.edgeIntervalSecond (K.faceEdge t i) a :=
      hf.imp (hpv.symm.trans ·) (hpv.symm.trans ·)
    have hg' :
        K.vertexPoint v = M.edgeIntervalFirst (K.faceEdge t j) b ∨
          K.vertexPoint v = M.edgeIntervalSecond (K.faceEdge t j) b :=
      hg.imp (hpv.symm.trans ·) (hpv.symm.trans ·)
    have hh' :
        K.vertexPoint v = M.edgeIntervalFirst (K.faceEdge t k) d ∨
          K.vertexPoint v = M.edgeIntervalSecond (K.faceEdge t k) d :=
      hh.imp (hpv.symm.trans ·) (hpv.symm.trans ·)
    rcases hindices with hij | hik | hjk
    · subst j
      have hab :=
        M.edgeInterval_eq_of_common_vertex_endpoint
          (K.faceEdge t i) a b v hvi hf' hg'
      subst b
      exact Or.inl rfl
    · subst k
      have had :=
        M.edgeInterval_eq_of_common_vertex_endpoint
          (K.faceEdge t i) a d v hvi hf' hh'
      subst d
      exact Or.inr (Or.inl rfl)
    · subst k
      have hbd :=
        M.edgeInterval_eq_of_common_vertex_endpoint
          (K.faceEdge t j) b d v hvj hg' hh'
      subst d
      exact Or.inr (Or.inr rfl)
  · have hpNot :
        ∀ v : {v // v ∈ t.1}, p ≠ K.facePoint t v := by
      intro v hp
      apply hpVertex
      refine ⟨⟨v.1, t.1, t.2, v.2⟩, ?_⟩
      exact hp
    have hijEdge :
        K.faceEdge t i = K.faceEdge t j := by
      apply Subtype.ext
      exact K.eq_of_card_two_of_mem_faceCarriers_not_vertex t
        (K.faceEdge_subset_face t i) (K.faceEdge_subset_face t j)
        (K.card_of_mem_edges (K.faceEdge t i).2)
        (K.card_of_mem_edges (K.faceEdge t j).2)
        hpEdgeI hpEdgeJ hpNot
    have hikEdge :
        K.faceEdge t i = K.faceEdge t k := by
      apply Subtype.ext
      exact K.eq_of_card_two_of_mem_faceCarriers_not_vertex t
        (K.faceEdge_subset_face t i) (K.faceEdge_subset_face t k)
        (K.card_of_mem_edges (K.faceEdge t i).2)
        (K.card_of_mem_edges (K.faceEdge t k).2)
        hpEdgeI hpEdgeK hpNot
    have hij : i = j := K.faceEdge_injective t hijEdge
    have hik : i = k := K.faceEdge_injective t hikEdge
    subst j
    subst k
    rcases M.edgeInterval_pair_eq_of_three_common_endpoint
        (K.faceEdge t i) a b d p hf hg hh with hab | had | hbd
    · subst b
      exact Or.inl rfl
    · subst d
      exact Or.inr (Or.inl rfl)
    · subst d
      exact Or.inr (Or.inr rfl)

/-- Every geometric vertex of a marked fan triangle lies in its parent old face. -/
theorem fanVertex_mem_faceCarrier (f : M.FanFace) {p : K.realization}
    (hp : p ∈ M.fanFaceVertices f) :
    p ∈ K.faceCarrier f.1.1 := by
  simp only [fanFaceVertices, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact K.faceCenter_mem_faceCarrier f.1
  · have hpEdge :
        M.edgeIntervalFirst (K.faceEdge f.1 f.2.1) f.2.2 ∈
          K.faceCarrier (K.faceEdge f.1 f.2.1).1 :=
      ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
        (M.edgeIntervalFirst_mem_edgeMarks
          (K.faceEdge f.1 f.2.1) f.2.2)).2
    intro v hvt
    exact hpEdge v fun hve ↦
      hvt (K.faceEdge_subset_face f.1 f.2.1 hve)
  · have hpEdge :
        M.edgeIntervalSecond (K.faceEdge f.1 f.2.1) f.2.2 ∈
          K.faceCarrier (K.faceEdge f.1 f.2.1).1 :=
      ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
        (M.edgeIntervalSecond_mem_edgeMarks
          (K.faceEdge f.1 f.2.1) f.2.2)).2
    intro v hvt
    exact hpEdge v fun hve ↦
      hvt (K.faceEdge_subset_face f.1 f.2.1 hve)

/-- The distinguished cone-center vertex of a marked fan triangle. -/
noncomputable def fanCenterVertex (f : M.FanFace) :
    {p // p ∈ M.fanFaceVertices f} :=
  ⟨K.faceCenter f.1, by simp [fanFaceVertices]⟩

/-- The first base vertex of a marked fan triangle. -/
noncomputable def fanFirstVertex (f : M.FanFace) :
    {p // p ∈ M.fanFaceVertices f} :=
  ⟨M.edgeIntervalFirst (K.faceEdge f.1 f.2.1) f.2.2, by
    simp [fanFaceVertices]⟩

/-- The second base vertex of a marked fan triangle. -/
noncomputable def fanSecondVertex (f : M.FanFace) :
    {p // p ∈ M.fanFaceVertices f} :=
  ⟨M.edgeIntervalSecond (K.faceEdge f.1 f.2.1) f.2.2, by
    simp [fanFaceVertices]⟩

theorem fanVertex_univ (f : M.FanFace) :
    (Finset.univ : Finset {p // p ∈ M.fanFaceVertices f}) =
      {M.fanCenterVertex f, M.fanFirstVertex f, M.fanSecondVertex f} := by
  classical
  ext p
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  have hp := p.2
  simp only [fanFaceVertices, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hp | hp | hp
  · exact Or.inl (Subtype.ext hp)
  · exact Or.inr (Or.inl (Subtype.ext hp))
  · exact Or.inr (Or.inr (Subtype.ext hp))

theorem fanCenterVertex_ne_first (f : M.FanFace) :
    M.fanCenterVertex f ≠ M.fanFirstVertex f := by
  intro h
  have hpEdge :
      M.edgeIntervalFirst (K.faceEdge f.1 f.2.1) f.2.2 ∈
        K.faceCarrier (K.faceEdge f.1 f.2.1).1 :=
    ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
      (M.edgeIntervalFirst_mem_edgeMarks
        (K.faceEdge f.1 f.2.1) f.2.2)).2
  exact K.faceCenter_ne_mem_faceEdge f.1 f.2.1 hpEdge
    (congrArg Subtype.val h)

theorem fanCenterVertex_ne_second (f : M.FanFace) :
    M.fanCenterVertex f ≠ M.fanSecondVertex f := by
  intro h
  have hpEdge :
      M.edgeIntervalSecond (K.faceEdge f.1 f.2.1) f.2.2 ∈
        K.faceCarrier (K.faceEdge f.1 f.2.1).1 :=
    ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
      (M.edgeIntervalSecond_mem_edgeMarks
        (K.faceEdge f.1 f.2.1) f.2.2)).2
  exact K.faceCenter_ne_mem_faceEdge f.1 f.2.1 hpEdge
    (congrArg Subtype.val h)

theorem fanFirstVertex_ne_second (f : M.FanFace) :
    M.fanFirstVertex f ≠ M.fanSecondVertex f := by
  intro h
  exact M.edgeIntervalFirst_ne_second
    (K.faceEdge f.1 f.2.1) f.2.2 (congrArg Subtype.val h)

/-- The affine barycentric realization of one marked fan triangle inside its parent face. -/
noncomputable def fanFaceMap (f : M.FanFace) :
    stdSimplex ℝ {p // p ∈ M.fanFaceVertices f} → K.realization := by
  classical
  intro x
  let z : K.Vertex → ℝ := fun v ↦
    ∑ p, x p * p.1.1 v
  refine ⟨z, ⟨?_, ?_⟩, ⟨f.1.1, f.1.2, ?_⟩⟩
  · intro v
    dsimp only [z]
    exact Finset.sum_nonneg fun p _ ↦
      mul_nonneg (x.2.1 p) (p.1.2.1.1 v)
  · dsimp only [z]
    calc
      ∑ v, ∑ p, x p * p.1.1 v =
          ∑ p, ∑ v, x p * p.1.1 v := Finset.sum_comm
      _ = ∑ p, x p * ∑ v, p.1.1 v := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
      _ = ∑ p, x p := by
        apply Finset.sum_congr rfl
        intro p _
        rw [p.1.2.1.2, mul_one]
      _ = 1 := x.2.2
  · intro v hv
    dsimp only [z]
    apply Finset.sum_eq_zero
    intro p _
    rw [M.fanVertex_mem_faceCarrier f p.2 v hv, mul_zero]

theorem fanFaceMap_mem_faceCarrier (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f}) :
    M.fanFaceMap f x ∈ K.faceCarrier f.1.1 := by
  classical
  intro v hv
  change (∑ p, x p * p.1.1 v) = 0
  apply Finset.sum_eq_zero
  intro p _
  rw [M.fanVertex_mem_faceCarrier f p.2 v hv, mul_zero]

theorem fanFaceMap_vertex (f : M.FanFace)
    (p : {p // p ∈ M.fanFaceVertices f}) :
    M.fanFaceMap f (stdSimplex.vertex p) = p.1 := by
  classical
  apply Subtype.ext
  funext v
  change (∑ q, (stdSimplex.vertex p :
      stdSimplex ℝ {p // p ∈ M.fanFaceVertices f}) q * q.1.1 v) = p.1.1 v
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    simp [hqp]
  · simp

theorem fanVertex_val_injective (f : M.FanFace) :
    Function.Injective
      (fun p : {p // p ∈ M.fanFaceVertices f} ↦ p.1.1) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  exact hpq

/-- The three geometric vertices of a marked fan triangle are affinely independent. -/
theorem affineIndependent_fanVertex_val (f : M.FanFace) :
    AffineIndependent ℝ
      (fun p : {p // p ∈ M.fanFaceVertices f} ↦ p.1.1) := by
  classical
  let c := M.fanCenterVertex f
  let p := M.fanFirstVertex f
  let q := M.fanSecondVertex f
  let opposite := K.faceVertex f.1 (f.2.1 + 2)
  let H : AffineSubspace ℝ (K.Vertex → ℝ) :=
    (LinearMap.ker (LinearMap.proj opposite)).toAffineSubspace
  have hpEdge :
      p.1 ∈ K.faceCarrier (K.faceEdge f.1 f.2.1).1 := by
    exact ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
      (M.edgeIntervalFirst_mem_edgeMarks
        (K.faceEdge f.1 f.2.1) f.2.2)).2
  have hqEdge :
      q.1 ∈ K.faceCarrier (K.faceEdge f.1 f.2.1).1 := by
    exact ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
      (M.edgeIntervalSecond_mem_edgeMarks
        (K.faceEdge f.1 f.2.1) f.2.2)).2
  have hpH : p.1.1 ∈ H := by
    change p.1.1 opposite = 0
    exact hpEdge opposite
      (K.intrinsicFaceVertex_add_two_not_mem_faceEdge f.1 f.2.1)
  have hqH : q.1.1 ∈ H := by
    change q.1.1 opposite = 0
    exact hqEdge opposite
      (K.intrinsicFaceVertex_add_two_not_mem_faceEdge f.1 f.2.1)
  have hcH : c.1.1 ∉ H := by
    intro hc
    have hzero : c.1.1 opposite = 0 := hc
    have hone : c.1.1 opposite = 1 / 3 := by
      simpa only [c, fanCenterVertex, opposite] using
        K.faceCenter_coordinate f.1 (K.faceVertex_mem f.1 (f.2.1 + 2))
    linarith
  have hpq : p.1.1 ≠ q.1.1 := by
    intro hpq
    exact M.fanFirstVertex_ne_second f
      (M.fanVertex_val_injective f hpq)
  have hthree : AffineIndependent ℝ ![p.1.1, q.1.1, c.1.1] :=
    affineIndependent_of_ne_of_mem_of_mem_of_notMem hpq hpH hqH hcH
  let source :=
    fun r : {r // r ∈ M.fanFaceVertices f} ↦ r.1.1
  have hrange : Set.range source = Set.range ![source p, source q, source c] := by
    ext z
    constructor
    · rintro ⟨r, rfl⟩
      have hr := r.2
      simp only [fanFaceVertices, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with hr | hr | hr
      · have hrc : r = c := Subtype.ext hr
        subst r
        exact ⟨2, by simp⟩
      · have hrp : r = p := Subtype.ext hr
        subst r
        exact ⟨0, by simp⟩
      · have hrq : r = q := Subtype.ext hr
        subst r
        exact ⟨1, by simp⟩
    · rintro ⟨r, rfl⟩
      fin_cases r
      · exact ⟨p, by simp⟩
      · exact ⟨q, by simp⟩
      · exact ⟨c, by simp⟩
  apply AffineIndependent.of_set_of_injective
  · rw [hrange]
    exact hthree.range
  · exact M.fanVertex_val_injective f

theorem fanFaceMap_injective (f : M.FanFace) :
    Function.Injective (M.fanFaceMap f) := by
  classical
  intro x y hxy
  have hval : (M.fanFaceMap f x).1 = (M.fanFaceMap f y).1 :=
    congrArg Subtype.val hxy
  change (fun v ↦ ∑ p, x p * p.1.1 v) =
    (fun v ↦ ∑ p, y p * p.1.1 v) at hval
  let source :=
    fun p : {p // p ∈ M.fanFaceVertices f} ↦ p.1.1
  have hcomb : Finset.univ.affineCombination ℝ source x =
      Finset.univ.affineCombination ℝ source y := by
    rw [Finset.univ.affineCombination_eq_linear_combination source x x.2.2,
      Finset.univ.affineCombination_eq_linear_combination source y y.2.2]
    funext v
    simpa only [source, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun hval v
  have hweights :=
    ((M.affineIndependent_fanVertex_val f).affineCombination_eq_iff_eq
      x.2.2 y.2.2).mp hcomb
  apply Subtype.ext
  funext p
  exact hweights p (Finset.mem_univ p)

theorem continuous_fanFaceMap (f : M.FanFace) :
    Continuous (M.fanFaceMap f) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  apply continuous_finsetSum
  intro p _
  exact ((continuous_apply p).comp continuous_subtype_val).mul continuous_const

/-- Each marked fan face is embedded in the intrinsic realization. -/
theorem isEmbedding_fanFaceMap (f : M.FanFace) :
    _root_.Topology.IsEmbedding (M.fanFaceMap f) :=
  (M.continuous_fanFaceMap f).isClosedEmbedding
    (M.fanFaceMap_injective f) |>.isEmbedding

/-- The three distinguished fan weights sum to one. -/
theorem fanWeights_sum (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f}) :
    x.1 (M.fanCenterVertex f) +
        x.1 (M.fanFirstVertex f) +
      x.1 (M.fanSecondVertex f) = 1 := by
  classical
  let c := M.fanCenterVertex f
  let p := M.fanFirstVertex f
  let q := M.fanSecondVertex f
  have hcNot : c ∉ ({p, q} : Finset _) := by
    simp [c, p, q, M.fanCenterVertex_ne_first f,
      M.fanCenterVertex_ne_second f]
  have hpNot : p ∉ ({q} : Finset _) := by
    simp [p, q, M.fanFirstVertex_ne_second f]
  have hsum := x.2.2
  rw [M.fanVertex_univ f, Finset.sum_insert hcNot,
    Finset.sum_insert hpNot, Finset.sum_singleton] at hsum
  simpa only [add_assoc] using hsum

/-- The canonical simplex path along the base of a marked fan triangle. -/
noncomputable def fanBaseSimplexPath (f : M.FanFace)
    (r : Set.Icc (0 : ℝ) 1) :
    stdSimplex ℝ {p // p ∈ M.fanFaceVertices f} := by
  let a := M.fanFirstVertex f
  let b := M.fanSecondVertex f
  let x := AffineMap.lineMap
    (stdSimplex.vertex a :
      {p // p ∈ M.fanFaceVertices f} → ℝ)
    (stdSimplex.vertex b :
      {p // p ∈ M.fanFaceVertices f} → ℝ) r.1
  exact ⟨x, (convex_stdSimplex ℝ _).lineMap_mem
    (stdSimplex.vertex a).2 (stdSimplex.vertex b).2 r.2⟩

@[simp] theorem fanBaseSimplexPath_apply_first (f : M.FanFace)
    (r : Set.Icc (0 : ℝ) 1) :
    M.fanBaseSimplexPath f r (M.fanFirstVertex f) = 1 - r.1 := by
  let a := M.fanFirstVertex f
  let b := M.fanSecondVertex f
  have hab : a ≠ b := M.fanFirstVertex_ne_second f
  change (M.fanBaseSimplexPath f r).1 a = 1 - r.1
  dsimp only [fanBaseSimplexPath]
  rw [AffineMap.lineMap_apply_module]
  simp [a, b, hab]

@[simp] theorem fanBaseSimplexPath_apply_second (f : M.FanFace)
    (r : Set.Icc (0 : ℝ) 1) :
    M.fanBaseSimplexPath f r (M.fanSecondVertex f) = r.1 := by
  let a := M.fanFirstVertex f
  let b := M.fanSecondVertex f
  have hab : a ≠ b := M.fanFirstVertex_ne_second f
  change (M.fanBaseSimplexPath f r).1 b = r.1
  dsimp only [fanBaseSimplexPath]
  rw [AffineMap.lineMap_apply_module]
  simp [a, b, hab]

@[simp] theorem fanBaseSimplexPath_apply_center (f : M.FanFace)
    (r : Set.Icc (0 : ℝ) 1) :
    M.fanBaseSimplexPath f r (M.fanCenterVertex f) = 0 := by
  let a := M.fanFirstVertex f
  let b := M.fanSecondVertex f
  let c := M.fanCenterVertex f
  have hca : c ≠ a := M.fanCenterVertex_ne_first f
  have hcb : c ≠ b := M.fanCenterVertex_ne_second f
  change (M.fanBaseSimplexPath f r).1 c = 0
  dsimp only [fanBaseSimplexPath]
  rw [AffineMap.lineMap_apply_module]
  simp [a, b, c, hca, hcb]

/-- The canonical affine segment between two points of one fan simplex. -/
noncomputable def fanSimplexLineMap (f : M.FanFace)
    (x y : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (r : Set.Icc (0 : ℝ) 1) :
    stdSimplex ℝ {p // p ∈ M.fanFaceVertices f} :=
  ⟨AffineMap.lineMap x.1 y.1 r.1,
    (convex_stdSimplex ℝ _).lineMap_mem x.2 y.2 r.2⟩

theorem fanFaceMap_simplexLineMap (f : M.FanFace)
    (x y : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (r : Set.Icc (0 : ℝ) 1) :
    (M.fanFaceMap f (M.fanSimplexLineMap f x y r)).1 =
      AffineMap.lineMap (M.fanFaceMap f x).1
        (M.fanFaceMap f y).1 r.1 := by
  classical
  funext v
  simp only [fanFaceMap, fanSimplexLineMap,
    AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ p, (((1 - r.1) • x.1 + r.1 • y.1) p) * p.1.1 v) =
    (1 - r.1) * ∑ p, x p * p.1.1 v +
      r.1 * ∑ p, y p * p.1.1 v
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ p, ((1 - r.1) * x p + r.1 * y p) * p.1.1 v) =
        ∑ p, ((1 - r.1) * (x p * p.1.1 v) +
          r.1 * (y p * p.1.1 v)) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- The geometric path along the base interval of one marked fan triangle. -/
noncomputable def fanBasePath (f : M.FanFace) :
    Set.Icc (0 : ℝ) 1 → K.realization :=
  M.fanFaceMap f ∘ M.fanBaseSimplexPath f

theorem fanBaseWeights_sum (f : M.FanFace) (r : Set.Icc (0 : ℝ) 1) :
    M.fanBaseSimplexPath f r (M.fanFirstVertex f) +
      M.fanBaseSimplexPath f r (M.fanSecondVertex f) = 1 := by
  rw [M.fanBaseSimplexPath_apply_first f r,
    M.fanBaseSimplexPath_apply_second f r]
  ring

/-- A zero center weight puts a fan point on its declared base edge. -/
theorem fanFaceMap_mem_baseEdge_of_center_eq_zero
    (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) = 0) :
    M.fanFaceMap f x ∈ K.faceCarrier (K.faceEdge f.1 f.2.1).1 := by
  classical
  let c := M.fanCenterVertex f
  let p := M.fanFirstVertex f
  let q := M.fanSecondVertex f
  have hcNot : c ∉ ({p, q} : Finset _) := by
    simp [c, p, q, M.fanCenterVertex_ne_first f,
      M.fanCenterVertex_ne_second f]
  have hpNot : p ∉ ({q} : Finset _) := by
    simp [p, q, M.fanFirstVertex_ne_second f]
  have hpEdge :
      p.1 ∈ K.faceCarrier (K.faceEdge f.1 f.2.1).1 := by
    exact ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
      (M.edgeIntervalFirst_mem_edgeMarks
        (K.faceEdge f.1 f.2.1) f.2.2)).2
  have hqEdge :
      q.1 ∈ K.faceCarrier (K.faceEdge f.1 f.2.1).1 := by
    exact ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
      (M.edgeIntervalSecond_mem_edgeMarks
        (K.faceEdge f.1 f.2.1) f.2.2)).2
  intro v hv
  change (∑ z, x z * z.1.1 v) = 0
  rw [M.fanVertex_univ f, Finset.sum_insert hcNot,
    Finset.sum_insert hpNot, Finset.sum_singleton]
  change x c * c.1.1 v + (x p * p.1.1 v + x q * q.1.1 v) = 0
  rw [show x c = 0 from hxCenter, hpEdge v hv, hqEdge v hv]
  ring

theorem fanBasePath_mem_baseEdge (f : M.FanFace)
    (r : Set.Icc (0 : ℝ) 1) :
    M.fanBasePath f r ∈ K.faceCarrier (K.faceEdge f.1 f.2.1).1 := by
  apply M.fanFaceMap_mem_baseEdge_of_center_eq_zero f
  exact M.fanBaseSimplexPath_apply_center f r

/-- On a fan base, the global edge parameter is the affine combination of its endpoints. -/
theorem edgeParameterValue_fanFaceMap_of_center_eq_zero
    (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) = 0) :
    M.edgeParameterValue (K.faceEdge f.1 f.2.1) (M.fanFaceMap f x) =
      x (M.fanFirstVertex f) *
          M.edgeParameterValue (K.faceEdge f.1 f.2.1)
            (M.fanFirstVertex f).1 +
        x (M.fanSecondVertex f) *
          M.edgeParameterValue (K.faceEdge f.1 f.2.1)
            (M.fanSecondVertex f).1 := by
  classical
  let e := K.faceEdge f.1 f.2.1
  let c := M.fanCenterVertex f
  let p := M.fanFirstVertex f
  let q := M.fanSecondVertex f
  have hcNot : c ∉ ({p, q} : Finset _) := by
    simp [c, p, q, M.fanCenterVertex_ne_first f,
      M.fanCenterVertex_ne_second f]
  have hpNot : p ∉ ({q} : Finset _) := by
    simp [p, q, M.fanFirstVertex_ne_second f]
  have hpEdge : p.1 ∈ K.faceCarrier e.1 := by
    exact ((M.mem_edgeMarks_iff e _).mp
      (M.edgeIntervalFirst_mem_edgeMarks e f.2.2)).2
  have hqEdge : q.1 ∈ K.faceCarrier e.1 := by
    exact ((M.mem_edgeMarks_iff e _).mp
      (M.edgeIntervalSecond_mem_edgeMarks e f.2.2)).2
  have hmapEdge : M.fanFaceMap f x ∈ K.faceCarrier e.1 :=
    M.fanFaceMap_mem_baseEdge_of_center_eq_zero f x hxCenter
  rw [M.edgeParameterValue_eq e hmapEdge,
    K.edgeParameter_eq_secondCoordinate]
  change (∑ z, x z * z.1.1 (K.edgeSecond e)) =
    x p * M.edgeParameterValue e p.1 +
      x q * M.edgeParameterValue e q.1
  rw [M.fanVertex_univ f, Finset.sum_insert hcNot,
    Finset.sum_insert hpNot, Finset.sum_singleton]
  rw [show x c = 0 from hxCenter, zero_mul, zero_add,
    M.edgeParameterValue_eq e hpEdge,
    M.edgeParameterValue_eq e hqEdge,
    K.edgeParameter_eq_secondCoordinate,
    K.edgeParameter_eq_secondCoordinate]

/-- Every point of a globally marked edge lies on one consecutive fan base. -/
theorem exists_fanBasePath_eq_of_mem_faceEdge
    (t : K.Face) (i : ZMod 3) {p : K.realization}
    (hp : p ∈ K.faceCarrier (K.faceEdge t i).1) :
    ∃ j : M.EdgeInterval (K.faceEdge t i),
      ∃ r : Set.Icc (0 : ℝ) 1,
        M.fanBasePath ⟨t, i, j⟩ r = p := by
  let e := K.faceEdge t i
  let z := M.edgeParameterValue e p
  obtain ⟨j, hj⟩ := M.exists_edgeInterval_containing e p hp
  let a := M.edgeParameterValue e (M.edgeIntervalFirst e j)
  let b := M.edgeParameterValue e (M.edgeIntervalSecond e j)
  have hab : 0 < b - a := sub_pos.mpr
    (M.edgeInterval_parameter_lt e j)
  let r : Set.Icc (0 : ℝ) 1 :=
    ⟨(z - a) / (b - a),
      div_nonneg (sub_nonneg.mpr hj.1) hab.le,
      (div_le_one hab).mpr (by linarith [hj.2])⟩
  refine ⟨j, r, ?_⟩
  apply M.edgeParameterValue_injOn e
  · exact M.fanBasePath_mem_baseEdge ⟨t, i, j⟩ r
  · exact hp
  have hformula :=
    M.edgeParameterValue_fanFaceMap_of_center_eq_zero
      ⟨t, i, j⟩ (M.fanBaseSimplexPath ⟨t, i, j⟩ r)
      (M.fanBaseSimplexPath_apply_center ⟨t, i, j⟩ r)
  rw [M.fanBaseSimplexPath_apply_first ⟨t, i, j⟩ r,
    M.fanBaseSimplexPath_apply_second ⟨t, i, j⟩ r] at hformula
  change M.edgeParameterValue e (M.fanBasePath ⟨t, i, j⟩ r) = z
  rw [show M.edgeParameterValue e (M.fanBasePath ⟨t, i, j⟩ r) =
      (1 - r.1) * a + r.1 * b by
    simpa only [fanBasePath, Function.comp_apply, fanFirstVertex,
      fanSecondVertex, e, a, b] using hformula]
  dsimp only [r]
  field_simp [hab.ne']
  ring

end EdgeMarking

/-- The standard face chart detects membership in each cyclic intrinsic edge. -/
theorem facePlaneHomeomorph_mem_edge_iff
    (t : K.Face) (i : ZMod 3) {p : K.realization}
    (hp : p ∈ K.faceCarrier t.1) :
    (K.facePlaneHomeomorph t ⟨p, hp⟩).1 ∈
        standardTriangleCircle.edgeSegment i ↔
      p ∈ K.faceCarrier (K.faceEdge t i).1 := by
  constructor
  · intro hchart
    rw [← K.facePlaneHomeomorph_image_edge t i] at hchart
    obtain ⟨x, hxEdge, hxchart⟩ := hchart
    have hpx : (⟨p, hp⟩ : K.ClosedFace t) = x := by
      apply (K.facePlaneHomeomorph t).injective
      apply Subtype.ext
      exact hxchart.symm
    have hval : p = x.1 := congrArg Subtype.val hpx
    rw [hval]
    exact hxEdge
  · intro hpEdge
    rw [← K.facePlaneHomeomorph_image_edge t i]
    exact ⟨⟨p, hp⟩, hpEdge, rfl⟩

/-- The barycentric center maps to the interior of the standard triangle. -/
theorem facePlaneCenter_mem_interior (t : K.Face) :
    (K.facePlaneHomeomorph t
      ⟨K.faceCenter t, K.faceCenter_mem_faceCarrier t⟩).1 ∈
        interior standardTrianglePlaneComplex.support := by
  let c := K.facePlaneHomeomorph t
    ⟨K.faceCenter t, K.faceCenter_mem_faceCarrier t⟩
  have hclosed : IsClosed standardTrianglePlaneComplex.support :=
    standardTrianglePlaneComplex_isTriangle.isCompact.isClosed
  by_contra hc
  have hcFrontier : c.1 ∈ frontier standardTrianglePlaneComplex.support := by
    rw [hclosed.frontier_eq]
    exact ⟨c.2, hc⟩
  have hcCircle : c.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier, ← standardTrianglePlaneComplex_support]
    exact hcFrontier
  obtain ⟨i, hci⟩ := Set.mem_iUnion.mp hcCircle
  change ZMod 3 at i
  have hcEdge : K.faceCenter t ∈ K.faceCarrier (K.faceEdge t i).1 :=
    (K.facePlaneHomeomorph_mem_edge_iff t i
      (K.faceCenter_mem_faceCarrier t)).mp hci
  exact (K.faceCenter_ne_mem_faceEdge t i hcEdge) rfl

/-- A radial segment in the standard face chart pulls back to the same affine segment in
intrinsic barycentric coordinates. -/
theorem face_val_eq_lineMap_of_plane_eq
    (t : K.Face) (p q : K.ClosedFace t) (r : ℝ)
    (hplane : (K.facePlaneHomeomorph t p).1 =
      AffineMap.lineMap
        (K.facePlaneHomeomorph t
          ⟨K.faceCenter t, K.faceCenter_mem_faceCarrier t⟩).1
        (K.facePlaneHomeomorph t q).1 r) :
    p.1.1 =
      AffineMap.lineMap (K.faceCenter t).1 q.1.1 r := by
  let c : K.ClosedFace t :=
    ⟨K.faceCenter t, K.faceCenter_mem_faceCarrier t⟩
  have hpInv := K.facePlaneHomeomorph_symm_val t
    (K.facePlaneHomeomorph t p)
  have hcInv := K.facePlaneHomeomorph_symm_val t
    (K.facePlaneHomeomorph t c)
  have hqInv := K.facePlaneHomeomorph_symm_val t
    (K.facePlaneHomeomorph t q)
  rw [(K.facePlaneHomeomorph t).symm_apply_apply] at hpInv hcInv hqInv
  calc
    p.1.1 = K.facePlaneInverseAffine t
        (K.facePlaneHomeomorph t p).1 := hpInv
    _ = K.facePlaneInverseAffine t
        (AffineMap.lineMap
          (K.facePlaneHomeomorph t c).1
          (K.facePlaneHomeomorph t q).1 r) := by rw [hplane]
    _ = AffineMap.lineMap
        (K.facePlaneInverseAffine t
          (K.facePlaneHomeomorph t c).1)
        (K.facePlaneInverseAffine t
          (K.facePlaneHomeomorph t q).1) r := by
      rw [AffineMap.apply_lineMap]
    _ = AffineMap.lineMap (K.faceCenter t).1 q.1.1 r := by
      rw [← hcInv, ← hqInv]

namespace EdgeMarking

variable {K : IntrinsicTwoComplex} (M : K.EdgeMarking)

/-- The marked fan triangles over one old face cover that entire closed face. -/
theorem exists_fanFaceMap_eq_of_mem_faceCarrier
    (t : K.Face) {p : K.realization} (hp : p ∈ K.faceCarrier t.1) :
    ∃ i : ZMod 3, ∃ j : M.EdgeInterval (K.faceEdge t i),
      ∃ x : stdSimplex ℝ {q // q ∈ M.fanFaceVertices ⟨t, i, j⟩},
        M.fanFaceMap ⟨t, i, j⟩ x = p := by
  let pClosed : K.ClosedFace t := ⟨p, hp⟩
  let cClosed : K.ClosedFace t :=
    ⟨K.faceCenter t, K.faceCenter_mem_faceCarrier t⟩
  let pPlane := K.facePlaneHomeomorph t pClosed
  let cPlane := K.facePlaneHomeomorph t cClosed
  obtain ⟨y, hyFrontier, hpSegment⟩ := exists_frontier_endpoint
    standardTrianglePlaneComplex_isTriangle.convex
    standardTrianglePlaneComplex_isTriangle.isCompact
    (K.facePlaneCenter_mem_interior t) pPlane.2
    standardTrianglePlaneComplex_isTriangle.frontier_nonempty
  have hclosed : IsClosed standardTrianglePlaneComplex.support :=
    standardTrianglePlaneComplex_isTriangle.isCompact.isClosed
  have hySupport : y ∈ standardTrianglePlaneComplex.support :=
    hclosed.frontier_subset hyFrontier
  let ySupport : standardTrianglePlaneComplex.support := ⟨y, hySupport⟩
  let qClosed : K.ClosedFace t :=
    (K.facePlaneHomeomorph t).symm ySupport
  have hqPlane : K.facePlaneHomeomorph t qClosed = ySupport :=
    (K.facePlaneHomeomorph t).apply_symm_apply ySupport
  have hyCircle : y ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier, ← standardTrianglePlaneComplex_support]
    exact hyFrontier
  obtain ⟨i, hyEdge⟩ := Set.mem_iUnion.mp hyCircle
  change ZMod 3 at i
  have hqEdge : qClosed.1 ∈ K.faceCarrier (K.faceEdge t i).1 := by
    apply (K.facePlaneHomeomorph_mem_edge_iff t i qClosed.2).mp
    rw [hqPlane]
    exact hyEdge
  obtain ⟨j, s, hbase⟩ :=
    M.exists_fanBasePath_eq_of_mem_faceEdge t i hqEdge
  rw [segment_eq_image_lineMap] at hpSegment
  obtain ⟨r, hr, hrPlane⟩ := hpSegment
  let rIcc : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
  let f : M.FanFace := ⟨t, i, j⟩
  let center : stdSimplex ℝ {q // q ∈ M.fanFaceVertices f} :=
    stdSimplex.vertex (M.fanCenterVertex f)
  let base := M.fanBaseSimplexPath f s
  let x := M.fanSimplexLineMap f center base rIcc
  refine ⟨i, j, x, ?_⟩
  have hplane : (K.facePlaneHomeomorph t pClosed).1 =
      AffineMap.lineMap
        (K.facePlaneHomeomorph t cClosed).1
        (K.facePlaneHomeomorph t qClosed).1 r := by
    calc
      (K.facePlaneHomeomorph t pClosed).1 = pPlane.1 := rfl
      _ = AffineMap.lineMap cPlane.1 y r := hrPlane.symm
      _ = AffineMap.lineMap
          (K.facePlaneHomeomorph t cClosed).1
          (K.facePlaneHomeomorph t qClosed).1 r := by
        rw [hqPlane]
  have hpVal := K.face_val_eq_lineMap_of_plane_eq t
    pClosed qClosed r hplane
  have hbaseMap : M.fanFaceMap f base = qClosed.1 := by
    simpa only [fanBasePath, Function.comp_apply, f, base] using hbase
  apply Subtype.ext
  calc
    (M.fanFaceMap f x).1 =
        AffineMap.lineMap
          (M.fanFaceMap f center).1
          (M.fanFaceMap f base).1 r :=
      M.fanFaceMap_simplexLineMap f center base rIcc
    _ = AffineMap.lineMap (K.faceCenter t).1 qClosed.1.1 r := by
      rw [M.fanFaceMap_vertex f (M.fanCenterVertex f), hbaseMap]
      rfl
    _ = p.1 := hpVal.symm

/-- The normalized parameter of the base point obtained by projecting away from the cone
center. -/
noncomputable def fanNormalizedBaseParameter (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) < 1) :
    Set.Icc (0 : ℝ) 1 := by
  let d := 1 - x (M.fanCenterVertex f)
  have hd : 0 < d := sub_pos.mpr hxCenter
  have hsum := M.fanWeights_sum f x
  change x (M.fanCenterVertex f) +
      x (M.fanFirstVertex f) +
    x (M.fanSecondVertex f) = 1 at hsum
  have hsecondNonneg := x.2.1 (M.fanSecondVertex f)
  have hfirstNonneg := x.2.1 (M.fanFirstVertex f)
  refine ⟨x (M.fanSecondVertex f) / d, ?_, ?_⟩
  · exact div_nonneg hsecondNonneg hd.le
  · apply (div_le_one hd).mpr
    dsimp only [d]
    change x (M.fanSecondVertex f) ≤
      1 - x (M.fanCenterVertex f)
    calc
      x (M.fanSecondVertex f) ≤
          x (M.fanFirstVertex f) + x (M.fanSecondVertex f) :=
        le_add_of_nonneg_left hfirstNonneg
      _ = 1 - x (M.fanCenterVertex f) := by
        rw [← hsum]
        ring

/-- Radial projection of a noncenter fan point to its base simplex. -/
noncomputable def fanNormalizedBasePoint (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) < 1) :
    stdSimplex ℝ {p // p ∈ M.fanFaceVertices f} :=
  M.fanBaseSimplexPath f (M.fanNormalizedBaseParameter f x hxCenter)

@[simp] theorem fanNormalizedBasePoint_apply_center (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) < 1) :
    M.fanNormalizedBasePoint f x hxCenter (M.fanCenterVertex f) = 0 :=
  M.fanBaseSimplexPath_apply_center f _

@[simp] theorem fanNormalizedBasePoint_apply_second (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) < 1) :
    M.fanNormalizedBasePoint f x hxCenter (M.fanSecondVertex f) =
      x (M.fanSecondVertex f) / (1 - x (M.fanCenterVertex f)) := by
  rw [fanNormalizedBasePoint, M.fanBaseSimplexPath_apply_second]
  rfl

@[simp] theorem fanNormalizedBasePoint_apply_first (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) < 1) :
    M.fanNormalizedBasePoint f x hxCenter (M.fanFirstVertex f) =
      x (M.fanFirstVertex f) / (1 - x (M.fanCenterVertex f)) := by
  rw [fanNormalizedBasePoint, M.fanBaseSimplexPath_apply_first]
  change 1 - x (M.fanSecondVertex f) /
      (1 - x (M.fanCenterVertex f)) =
    x (M.fanFirstVertex f) / (1 - x (M.fanCenterVertex f))
  have hsum := M.fanWeights_sum f x
  change x (M.fanCenterVertex f) +
      x (M.fanFirstVertex f) +
    x (M.fanSecondVertex f) = 1 at hsum
  have hden : 1 - x (M.fanCenterVertex f) ≠ 0 :=
    (sub_pos.mpr hxCenter).ne'
  have hnum :
      (1 - x (M.fanCenterVertex f)) -
          x (M.fanSecondVertex f) =
        x (M.fanFirstVertex f) := by
    rw [← hsum]
    ring
  field_simp [hden]
  linarith [hnum]

/-- A noncenter fan point is the affine combination of the cone center and its normalized
base projection. -/
theorem fanFaceMap_eq_lineMap_normalizedBase (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) < 1) :
    (M.fanFaceMap f x).1 =
      AffineMap.lineMap (K.faceCenter f.1).1
        (M.fanFaceMap f (M.fanNormalizedBasePoint f x hxCenter)).1
        (1 - x (M.fanCenterVertex f)) := by
  classical
  let c := M.fanCenterVertex f
  let p := M.fanFirstVertex f
  let q := M.fanSecondVertex f
  let d := 1 - x c
  have hd : d ≠ 0 := (sub_pos.mpr hxCenter).ne'
  have hcNot : c ∉ ({p, q} : Finset _) := by
    simp [c, p, q, M.fanCenterVertex_ne_first f,
      M.fanCenterVertex_ne_second f]
  have hpNot : p ∉ ({q} : Finset _) := by
    simp [p, q, M.fanFirstVertex_ne_second f]
  funext v
  change (∑ r, x r * r.1.1 v) = _
  rw [M.fanVertex_univ f, Finset.sum_insert hcNot,
    Finset.sum_insert hpNot, Finset.sum_singleton,
    AffineMap.lineMap_apply_module]
  change x c * c.1.1 v + (x p * p.1.1 v + x q * q.1.1 v) =
    (1 - d) * (K.faceCenter f.1).1 v +
      d * (∑ r, M.fanNormalizedBasePoint f x hxCenter r * r.1.1 v)
  rw [M.fanVertex_univ f, Finset.sum_insert hcNot,
    Finset.sum_insert hpNot, Finset.sum_singleton,
    M.fanNormalizedBasePoint_apply_center f x hxCenter,
    M.fanNormalizedBasePoint_apply_first f x hxCenter,
    M.fanNormalizedBasePoint_apply_second f x hxCenter]
  change x c * c.1.1 v + (x p * p.1.1 v + x q * q.1.1 v) =
    (1 - d) * (K.faceCenter f.1).1 v +
      d * (0 * c.1.1 v +
        (x p / d * p.1.1 v + x q / d * q.1.1 v))
  have hcval : c.1.1 = (K.faceCenter f.1).1 := rfl
  rw [hcval]
  dsimp only [d, c] at hd ⊢
  field_simp [hd]
  ring

/-- The coordinate opposite a fan base is exactly one third of the cone-center weight. -/
theorem fanFaceMap_opposite (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f}) :
    (M.fanFaceMap f x).1 (K.faceVertex f.1 (f.2.1 + 2)) =
      x (M.fanCenterVertex f) / 3 := by
  classical
  let c := M.fanCenterVertex f
  let opposite := K.faceVertex f.1 (f.2.1 + 2)
  change (∑ p, x p * p.1.1 opposite) = x c / 3
  rw [Finset.sum_eq_single c]
  · have hc : c.1.1 opposite = 1 / 3 := by
      simpa only [c, fanCenterVertex, opposite] using
        K.faceCenter_coordinate f.1
          (K.faceVertex_mem f.1 (f.2.1 + 2))
    rw [hc]
    ring
  · intro p _ hpc
    have hp := p.2
    simp only [fanFaceVertices, Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with hp | hp | hp
    · exact False.elim (hpc (Subtype.ext hp))
    · rw [mul_eq_zero]
      apply Or.inr
      have hpEdge :
          p.1 ∈ K.faceCarrier (K.faceEdge f.1 f.2.1).1 := by
        simpa only [hp] using
          ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
            (M.edgeIntervalFirst_mem_edgeMarks
              (K.faceEdge f.1 f.2.1) f.2.2)).2
      exact hpEdge opposite
        (K.intrinsicFaceVertex_add_two_not_mem_faceEdge f.1 f.2.1)
    · rw [mul_eq_zero]
      apply Or.inr
      have hpEdge :
          p.1 ∈ K.faceCarrier (K.faceEdge f.1 f.2.1).1 := by
        simpa only [hp] using
          ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
            (M.edgeIntervalSecond_mem_edgeMarks
              (K.faceEdge f.1 f.2.1) f.2.2)).2
      exact hpEdge opposite
        (K.intrinsicFaceVertex_add_two_not_mem_faceEdge f.1 f.2.1)
  · intro hcNot
    simp at hcNot

/-- A fan point lies on its declared base edge only if its cone-center weight vanishes. -/
theorem fanCenterWeight_eq_zero_of_mem_baseEdge
    (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hx :
      M.fanFaceMap f x ∈
        K.faceCarrier (K.faceEdge f.1 f.2.1).1) :
    x (M.fanCenterVertex f) = 0 := by
  have hopposite :
      (M.fanFaceMap f x).1 (K.faceVertex f.1 (f.2.1 + 2)) = 0 :=
    hx _ (K.intrinsicFaceVertex_add_two_not_mem_faceEdge f.1 f.2.1)
  rw [M.fanFaceMap_opposite] at hopposite
  linarith

/-- The center contribution is a lower bound for every parent-face barycentric coordinate. -/
theorem fanFaceMap_faceVertex_lower_bound (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (i : ZMod 3) :
    x (M.fanCenterVertex f) / 3 ≤
      (M.fanFaceMap f x).1 (K.faceVertex f.1 i) := by
  classical
  let c := M.fanCenterVertex f
  have hcValue : c.1.1 (K.faceVertex f.1 i) = 1 / 3 := by
    simpa only [c, fanCenterVertex] using
      K.faceCenter_coordinate f.1 (K.faceVertex_mem f.1 i)
  have hterm :
      x c * c.1.1 (K.faceVertex f.1 i) ≤
        ∑ p, x p * p.1.1 (K.faceVertex f.1 i) :=
    Finset.single_le_sum
      (fun p _ ↦ mul_nonneg (x.2.1 p) (p.1.2.1.1 _))
      (Finset.mem_univ c)
  change x c / 3 ≤
    ∑ p, x p * p.1.1 (K.faceVertex f.1 i)
  rw [hcValue] at hterm
  simpa only [c, div_eq_mul_inv, one_mul] using hterm

/-- Within one old parent face, a common geometric point determines its cone-center weight. -/
theorem fanCenterWeight_eq_of_faceMap_eq_of_parent_eq
    (t : K.Face) (i j : ZMod 3)
    (a : M.EdgeInterval (K.faceEdge t i))
    (b : M.EdgeInterval (K.faceEdge t j))
    {x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices ⟨t, i, a⟩}}
    {y : stdSimplex ℝ {p // p ∈ M.fanFaceVertices ⟨t, j, b⟩}}
    (hxy : M.fanFaceMap ⟨t, i, a⟩ x =
      M.fanFaceMap ⟨t, j, b⟩ y) :
    x (M.fanCenterVertex ⟨t, i, a⟩) =
      y (M.fanCenterVertex ⟨t, j, b⟩) := by
  have hval := congrArg Subtype.val hxy
  have hxOpp := M.fanFaceMap_opposite ⟨t, i, a⟩ x
  have hyAtX := M.fanFaceMap_faceVertex_lower_bound
    ⟨t, j, b⟩ y (i + 2)
  have hyOpp := M.fanFaceMap_opposite ⟨t, j, b⟩ y
  have hxAtY := M.fanFaceMap_faceVertex_lower_bound
    ⟨t, i, a⟩ x (j + 2)
  have hleYX :
      y (M.fanCenterVertex ⟨t, j, b⟩) ≤
        x (M.fanCenterVertex ⟨t, i, a⟩) := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).mp
    calc
      y (M.fanCenterVertex ⟨t, j, b⟩) / 3 ≤
          (M.fanFaceMap ⟨t, j, b⟩ y).1
            (K.faceVertex t (i + 2)) := hyAtX
      _ = (M.fanFaceMap ⟨t, i, a⟩ x).1
            (K.faceVertex t (i + 2)) := congrFun hval (K.faceVertex t (i + 2)) |>.symm
      _ = x (M.fanCenterVertex ⟨t, i, a⟩) / 3 := hxOpp
  have hleXY :
      x (M.fanCenterVertex ⟨t, i, a⟩) ≤
        y (M.fanCenterVertex ⟨t, j, b⟩) := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).mp
    calc
      x (M.fanCenterVertex ⟨t, i, a⟩) / 3 ≤
          (M.fanFaceMap ⟨t, i, a⟩ x).1
            (K.faceVertex t (j + 2)) := hxAtY
      _ = (M.fanFaceMap ⟨t, j, b⟩ y).1
            (K.faceVertex t (j + 2)) := congrFun hval (K.faceVertex t (j + 2))
      _ = y (M.fanCenterVertex ⟨t, j, b⟩) / 3 := hyOpp
  exact le_antisymm hleXY hleYX

/-- When the cone-center weight vanishes, the two base weights sum to one. -/
theorem fanBaseWeights_sum_of_center_eq_zero (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) = 0) :
    x (M.fanFirstVertex f) + x (M.fanSecondVertex f) = 1 := by
  have hsum := M.fanWeights_sum f x
  change x (M.fanCenterVertex f) +
      x (M.fanFirstVertex f) +
    x (M.fanSecondVertex f) = 1 at hsum
  rw [hxCenter, zero_add] at hsum
  exact hsum

/-- Positive weights at both base vertices put the edge parameter strictly between the two
consecutive marked parameters. -/
theorem edgeParameterValue_fanFaceMap_mem_Ioo_of_center_eq_zero
    (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) = 0)
    (hxFirst : 0 < x (M.fanFirstVertex f))
    (hxSecond : 0 < x (M.fanSecondVertex f)) :
    M.edgeParameterValue (K.faceEdge f.1 f.2.1) (M.fanFaceMap f x) ∈
      Set.Ioo
        (M.edgeParameterValue (K.faceEdge f.1 f.2.1)
          (M.fanFirstVertex f).1)
        (M.edgeParameterValue (K.faceEdge f.1 f.2.1)
          (M.fanSecondVertex f).1) := by
  have hformula :=
    M.edgeParameterValue_fanFaceMap_of_center_eq_zero f x hxCenter
  have hsum := M.fanBaseWeights_sum_of_center_eq_zero f x hxCenter
  have hfirst := M.edgeInterval_parameter_lt
    (K.faceEdge f.1 f.2.1) f.2.2
  let z := M.edgeParameterValue (K.faceEdge f.1 f.2.1)
    (M.fanFaceMap f x)
  let a := M.edgeParameterValue (K.faceEdge f.1 f.2.1)
    (M.fanFirstVertex f).1
  let b := M.edgeParameterValue (K.faceEdge f.1 f.2.1)
    (M.fanSecondVertex f).1
  let α := x (M.fanFirstVertex f)
  let β := x (M.fanSecondVertex f)
  have hzLeft : z = a + β * (b - a) := by
    calc
      z = α * a + β * b := hformula
      _ = (α + β) * a + β * (b - a) := by ring
      _ = a + β * (b - a) := by rw [hsum, one_mul]
  have hzRight : z = b - α * (b - a) := by
    calc
      z = α * a + β * b := hformula
      _ = (α + β) * b - α * (b - a) := by ring
      _ = b - α * (b - a) := by rw [hsum, one_mul]
  constructor
  · change a < z
    rw [hzLeft]
    exact lt_add_of_pos_right _ (mul_pos hxSecond (sub_pos.mpr hfirst))
  · change z < b
    rw [hzRight]
    exact sub_lt_self _ (mul_pos hxFirst (sub_pos.mpr hfirst))

/-- A relative-interior point of a marked fan base is not one of the global marked points. -/
theorem fanFaceMap_not_mem_points_of_center_zero_of_base_weights_pos
    (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) = 0)
    (hxFirst : 0 < x (M.fanFirstVertex f))
    (hxSecond : 0 < x (M.fanSecondVertex f)) :
    M.fanFaceMap f x ∉ M.points := by
  intro hxMarked
  let e := K.faceEdge f.1 f.2.1
  have hxEdge : M.fanFaceMap f x ∈ K.faceCarrier e.1 :=
    M.fanFaceMap_mem_baseEdge_of_center_eq_zero f x hxCenter
  have hxEdgeMark : M.fanFaceMap f x ∈ M.edgeMarks e :=
    (M.mem_edgeMarks_iff e _).mpr ⟨hxMarked, hxEdge⟩
  exact M.not_edgeMark_parameter_mem_Ioo e f.2.2 hxEdgeMark
    (M.edgeParameterValue_fanFaceMap_mem_Ioo_of_center_eq_zero
      f x hxCenter hxFirst hxSecond)

/-- A relative-interior point of a fan base lies in the open barycentric carrier of its old
abstract edge. -/
theorem fanFaceMap_mem_edgePath_image_Ioo_of_center_zero_of_base_weights_pos
    (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) = 0)
    (hxFirst : 0 < x (M.fanFirstVertex f))
    (hxSecond : 0 < x (M.fanSecondVertex f)) :
    M.fanFaceMap f x ∈
      K.edgePath (K.faceEdge f.1 f.2.1) ''
        {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1} := by
  let e := K.faceEdge f.1 f.2.1
  have hxEdge : M.fanFaceMap f x ∈ K.faceCarrier e.1 :=
    M.fanFaceMap_mem_baseEdge_of_center_eq_zero f x hxCenter
  let r := K.edgeParameter e (M.fanFaceMap f x) hxEdge
  refine ⟨r, ?_, K.edgePath_edgeParameter e _ hxEdge⟩
  have hxIoo :=
    M.edgeParameterValue_fanFaceMap_mem_Ioo_of_center_eq_zero
      f x hxCenter hxFirst hxSecond
  have hfirstEdge :
      (M.fanFirstVertex f).1 ∈ K.faceCarrier e.1 :=
    ((M.mem_edgeMarks_iff e _).mp
      (M.edgeIntervalFirst_mem_edgeMarks e f.2.2)).2
  have hsecondEdge :
      (M.fanSecondVertex f).1 ∈ K.faceCarrier e.1 :=
    ((M.mem_edgeMarks_iff e _).mp
      (M.edgeIntervalSecond_mem_edgeMarks e f.2.2)).2
  have hfirstIcc :=
    M.edgeParameterValue_mem_Icc e hfirstEdge
  have hsecondIcc :=
    M.edgeParameterValue_mem_Icc e hsecondEdge
  change 0 < (r : ℝ) ∧ (r : ℝ) < 1
  rw [show (r : ℝ) =
      M.edgeParameterValue e (M.fanFaceMap f x) by
    exact (M.edgeParameterValue_eq e hxEdge).symm]
  exact ⟨hfirstIcc.1.trans_lt hxIoo.1, hxIoo.2.trans_le hsecondIcc.2⟩

/-- A point common to fan triangles from distinct old parent faces has zero cone-center weight
in the first triangle. -/
theorem fanCenterWeight_eq_zero_of_faceMap_eq_of_parent_ne
    {f g : M.FanFace} (hfg : f.1 ≠ g.1)
    {x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f}}
    {y : stdSimplex ℝ {p // p ∈ M.fanFaceVertices g}}
    (hxy : M.fanFaceMap f x = M.fanFaceMap g y) :
    x (M.fanCenterVertex f) = 0 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hxCenter
    have hsubset : f.1.1 ⊆ g.1.1 := by
      intro v hvf
      by_contra hvg
      let vf : f.1.1 := ⟨v, hvf⟩
      let k : Fin 3 := (K.faceVertexEquiv f.1).symm vf
      let i : ZMod 3 := (ZMod.finEquiv 3) k
      have hi : K.faceVertex f.1 i = v := by
        change ((K.faceVertexEquiv f.1)
          ((ZMod.finEquiv 3).symm ((ZMod.finEquiv 3) k))).1 = v
        rw [(ZMod.finEquiv 3).symm_apply_apply,
          (K.faceVertexEquiv f.1).apply_symm_apply]
      have hlower := M.fanFaceMap_faceVertex_lower_bound f x i
      have hzero :
          (M.fanFaceMap g y).1 (K.faceVertex f.1 i) = 0 :=
        M.fanFaceMap_mem_faceCarrier g y _ (by simpa only [hi] using hvg)
      have hcoord := congrArg
        (fun z : K.realization ↦ z.1 (K.faceVertex f.1 i)) hxy
      rw [hcoord, hzero] at hlower
      nlinarith
    have hval : f.1.1 = g.1.1 :=
      Finset.eq_of_subset_of_card_le hsubset (by
        rw [K.faces_card f.1.1 f.1.2, K.faces_card g.1.1 g.1.2])
    exact hfg (Subtype.ext hval)
  · exact x.2.1 _

/-- A fan point lying in a distinct old parent face has zero cone-center weight. -/
theorem fanCenterWeight_eq_zero_of_mem_faceCarrier_of_parent_ne
    (f : M.FanFace) (g : K.Face) (hfg : f.1 ≠ g)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxg : M.fanFaceMap f x ∈ K.faceCarrier g.1) :
    x (M.fanCenterVertex f) = 0 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hxCenter
    have hsubset : f.1.1 ⊆ g.1 := by
      intro v hvf
      by_contra hvg
      let vf : f.1.1 := ⟨v, hvf⟩
      let k : Fin 3 := (K.faceVertexEquiv f.1).symm vf
      let i : ZMod 3 := (ZMod.finEquiv 3) k
      have hi : K.faceVertex f.1 i = v := by
        change ((K.faceVertexEquiv f.1)
          ((ZMod.finEquiv 3).symm ((ZMod.finEquiv 3) k))).1 = v
        rw [(ZMod.finEquiv 3).symm_apply_apply,
          (K.faceVertexEquiv f.1).apply_symm_apply]
      have hlower := M.fanFaceMap_faceVertex_lower_bound f x i
      have hzero :
          (M.fanFaceMap f x).1 (K.faceVertex f.1 i) = 0 :=
        hxg _ (by simpa only [hi] using hvg)
      rw [hzero] at hlower
      nlinarith
    have hval : f.1.1 = g.1 :=
      Finset.eq_of_subset_of_card_le hsubset (by
        rw [K.faces_card f.1.1 f.1.2, K.faces_card g.1 g.2])
    exact hfg (Subtype.ext hval)
  · exact x.2.1 _

/-- Extended coordinates of a marked fan triangle are the sum of its three vertex-weight
spikes. -/
theorem extendFaceCoordinates_fanFace (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f}) :
    extendFaceCoordinates (M.fanFaceVertices f) x =
      Pi.single (M.fanCenterVertex f).1
          (x (M.fanCenterVertex f)) +
        Pi.single (M.fanFirstVertex f).1
          (x (M.fanFirstVertex f)) +
        Pi.single (M.fanSecondVertex f).1
          (x (M.fanSecondVertex f)) := by
  classical
  let c := M.fanCenterVertex f
  let p := M.fanFirstVertex f
  let q := M.fanSecondVertex f
  have hcp : c.1 ≠ p.1 := fun h ↦
    M.fanCenterVertex_ne_first f (Subtype.ext h)
  have hcq : c.1 ≠ q.1 := fun h ↦
    M.fanCenterVertex_ne_second f (Subtype.ext h)
  have hpq : p.1 ≠ q.1 := fun h ↦
    M.fanFirstVertex_ne_second f (Subtype.ext h)
  funext v
  by_cases hvc : v = c.1
  · subst v
    have hcMem : c.1 ∈ M.fanFaceVertices f := c.2
    rw [extendFaceCoordinates_of_mem _ _ hcMem]
    have hcEq : (⟨c.1, hcMem⟩ :
        {z // z ∈ M.fanFaceVertices f}) = c := Subtype.ext rfl
    rw [hcEq]
    simp [c, p, q, hcp, hcq]
  by_cases hvp : v = p.1
  · subst v
    have hpMem : p.1 ∈ M.fanFaceVertices f := p.2
    rw [extendFaceCoordinates_of_mem _ _ hpMem]
    have hpEq : (⟨p.1, hpMem⟩ :
        {z // z ∈ M.fanFaceVertices f}) = p := Subtype.ext rfl
    rw [hpEq]
    simp [c, p, q, hcp, hpq]
  by_cases hvq : v = q.1
  · subst v
    have hqMem : q.1 ∈ M.fanFaceVertices f := q.2
    rw [extendFaceCoordinates_of_mem _ _ hqMem]
    have hqEq : (⟨q.1, hqMem⟩ :
        {z // z ∈ M.fanFaceVertices f}) = q := Subtype.ext rfl
    rw [hqEq]
    simp [c, p, q, hcq, hpq]
  · have hvNot : v ∉ M.fanFaceVertices f := by
      intro hv
      simp only [fanFaceVertices, Finset.mem_insert,
        Finset.mem_singleton] at hv
      exact hv.elim hvc (fun h ↦ h.elim hvp hvq)
    rw [extendFaceCoordinates_of_notMem _ _ hvNot]
    simp [c, p, q, hvc, hvp, hvq]

/-- A zero-center fan point outside the relative interior of its base is one of the declared
base vertices, both geometrically and in zero-extended barycentric coordinates. -/
theorem fanEndpointData_of_center_eq_zero_of_not_base_weights_pos
    (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) = 0)
    (hxNot : ¬(0 < x (M.fanFirstVertex f) ∧
      0 < x (M.fanSecondVertex f))) :
    ((M.fanFaceMap f x).1 = (M.fanFirstVertex f).1 ∧
      extendFaceCoordinates (M.fanFaceVertices f) x =
        Pi.single (M.fanFirstVertex f).1 1) ∨
    ((M.fanFaceMap f x).1 = (M.fanSecondVertex f).1 ∧
      extendFaceCoordinates (M.fanFaceVertices f) x =
        Pi.single (M.fanSecondVertex f).1 1) := by
  classical
  have hsum := M.fanBaseWeights_sum_of_center_eq_zero f x hxCenter
  have hxFirstNonneg := x.2.1 (M.fanFirstVertex f)
  have hxSecondNonneg := x.2.1 (M.fanSecondVertex f)
  by_cases hxFirst : x (M.fanFirstVertex f) = 0
  · right
    have hxSecond : x (M.fanSecondVertex f) = 1 := by
      rw [hxFirst, zero_add] at hsum
      exact hsum
    have hxCenter' : x.1 (M.fanCenterVertex f) = 0 := hxCenter
    have hxFirst' : x.1 (M.fanFirstVertex f) = 0 := hxFirst
    have hxSecond' : x.1 (M.fanSecondVertex f) = 1 := hxSecond
    have hxVertex : x = stdSimplex.vertex (M.fanSecondVertex f) := by
      apply Subtype.ext
      funext v
      have hv : v = M.fanCenterVertex f ∨
          v = M.fanFirstVertex f ∨ v = M.fanSecondVertex f := by
        have := Finset.mem_univ v
        rw [M.fanVertex_univ f] at this
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      rcases hv with rfl | rfl | rfl
      · simp only [ne_eq, M.fanCenterVertex_ne_second f, not_false_eq_true, Pi.single_eq_of_ne]
        exact hxCenter'
      · simp only [ne_eq, M.fanFirstVertex_ne_second f, not_false_eq_true, Pi.single_eq_of_ne]
        exact hxFirst'
      · simp only [Pi.single_eq_same]
        exact hxSecond'
    constructor
    · rw [hxVertex, M.fanFaceMap_vertex f]
    · rw [M.extendFaceCoordinates_fanFace f x,
        hxCenter, hxFirst, hxSecond]
      simp
  · left
    have hxFirstPos : 0 < x (M.fanFirstVertex f) :=
      lt_of_le_of_ne hxFirstNonneg (Ne.symm hxFirst)
    have hxSecond : x (M.fanSecondVertex f) = 0 := by
      apply le_antisymm
      · apply le_of_not_gt
        intro hxSecondPos
        exact hxNot ⟨hxFirstPos, hxSecondPos⟩
      · exact hxSecondNonneg
    have hxFirstOne : x (M.fanFirstVertex f) = 1 := by
      rw [hxSecond, add_zero] at hsum
      exact hsum
    have hxCenter' : x.1 (M.fanCenterVertex f) = 0 := hxCenter
    have hxFirstOne' : x.1 (M.fanFirstVertex f) = 1 := hxFirstOne
    have hxSecond' : x.1 (M.fanSecondVertex f) = 0 := hxSecond
    have hxVertex : x = stdSimplex.vertex (M.fanFirstVertex f) := by
      apply Subtype.ext
      funext v
      have hv : v = M.fanCenterVertex f ∨
          v = M.fanFirstVertex f ∨ v = M.fanSecondVertex f := by
        have := Finset.mem_univ v
        rw [M.fanVertex_univ f] at this
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      rcases hv with rfl | rfl | rfl
      · simp only [ne_eq, M.fanCenterVertex_ne_first f, not_false_eq_true, Pi.single_eq_of_ne]
        exact hxCenter'
      · simp only [Pi.single_eq_same]
        exact hxFirstOne'
      · simp only [ne_eq, M.fanFirstVertex_ne_second f, not_false_eq_true, Pi.single_eq_of_ne']
        exact hxSecond'
    constructor
    · rw [hxVertex, M.fanFaceMap_vertex f]
    · rw [M.extendFaceCoordinates_fanFace f x,
        hxCenter, hxFirstOne, hxSecond]
      simp

/-- Relative-interior points of fan bases use the same zero-extended coordinates in every fan
triangle that contains them.  Distinct old edges have disjoint open barycentric carriers, while
on one old edge the global mark order determines a unique consecutive interval. -/
theorem fanExtendedCoordinates_eq_of_faceMap_eq_of_center_zero_of_base_weights_pos
    {f g : M.FanFace}
    {x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f}}
    {y : stdSimplex ℝ {p // p ∈ M.fanFaceVertices g}}
    (hxy : M.fanFaceMap f x = M.fanFaceMap g y)
    (hxCenter : x (M.fanCenterVertex f) = 0)
    (hyCenter : y (M.fanCenterVertex g) = 0)
    (hxFirst : 0 < x (M.fanFirstVertex f))
    (hxSecond : 0 < x (M.fanSecondVertex f))
    (hyFirst : 0 < y (M.fanFirstVertex g))
    (hySecond : 0 < y (M.fanSecondVertex g)) :
    extendFaceCoordinates (M.fanFaceVertices f) x =
      extendFaceCoordinates (M.fanFaceVertices g) y := by
  let e := K.faceEdge f.1 f.2.1
  let d := K.faceEdge g.1 g.2.1
  have hxOpen :=
    M.fanFaceMap_mem_edgePath_image_Ioo_of_center_zero_of_base_weights_pos
      f x hxCenter hxFirst hxSecond
  have hyOpen :=
    M.fanFaceMap_mem_edgePath_image_Ioo_of_center_zero_of_base_weights_pos
      g y hyCenter hyFirst hySecond
  have hedge : e = d := by
    by_contra hed
    have hdisjoint := K.disjoint_edgePath_image_Ioo hed
    exact Set.disjoint_left.mp hdisjoint hxOpen (by
      rw [hxy]
      exact hyOpen)
  have hxIoo :=
    M.edgeParameterValue_fanFaceMap_mem_Ioo_of_center_eq_zero
      f x hxCenter hxFirst hxSecond
  have hyIoo :=
    M.edgeParameterValue_fanFaceMap_mem_Ioo_of_center_eq_zero
      g y hyCenter hyFirst hySecond
  have hparameter :
      M.edgeParameterValue e (M.fanFaceMap f x) =
        M.edgeParameterValue d (M.fanFaceMap g y) := by
    rw [hedge, hxy]
  have hyIoo' :
      M.edgeParameterValue e (M.fanFaceMap f x) ∈
        Set.Ioo
          (M.edgeParameterValue d (M.edgeIntervalFirst d g.2.2))
          (M.edgeParameterValue d (M.edgeIntervalSecond d g.2.2)) := by
    rw [hparameter]
    simpa only [fanFirstVertex, fanSecondVertex, d] using hyIoo
  have hends :=
    M.edgeInterval_endpoints_eq_of_edge_eq_of_parameter_mem_Ioo
      hedge f.2.2 g.2.2
      (by simpa only [fanFirstVertex, fanSecondVertex, e] using hxIoo)
      hyIoo'
  have hfirstVal : (M.fanFirstVertex f).1 = (M.fanFirstVertex g).1 := by
    simpa only [fanFirstVertex, e, d] using hends.1
  have hsecondVal : (M.fanSecondVertex f).1 = (M.fanSecondVertex g).1 := by
    simpa only [fanSecondVertex, e, d] using hends.2
  have hfirstParameter :
      M.edgeParameterValue e (M.fanFirstVertex f).1 =
        M.edgeParameterValue d (M.fanFirstVertex g).1 := by
    rw [hedge, hfirstVal]
  have hsecondParameter :
      M.edgeParameterValue e (M.fanSecondVertex f).1 =
        M.edgeParameterValue d (M.fanSecondVertex g).1 := by
    rw [hedge, hsecondVal]
  have hxSum := M.fanBaseWeights_sum_of_center_eq_zero f x hxCenter
  have hySum := M.fanBaseWeights_sum_of_center_eq_zero g y hyCenter
  have hxFormula :=
    M.edgeParameterValue_fanFaceMap_of_center_eq_zero f x hxCenter
  have hyFormula :=
    M.edgeParameterValue_fanFaceMap_of_center_eq_zero g y hyCenter
  change M.edgeParameterValue e (M.fanFaceMap f x) =
      x (M.fanFirstVertex f) *
          M.edgeParameterValue e (M.fanFirstVertex f).1 +
        x (M.fanSecondVertex f) *
          M.edgeParameterValue e (M.fanSecondVertex f).1 at hxFormula
  change M.edgeParameterValue d (M.fanFaceMap g y) =
      y (M.fanFirstVertex g) *
          M.edgeParameterValue d (M.fanFirstVertex g).1 +
        y (M.fanSecondVertex g) *
          M.edgeParameterValue d (M.fanSecondVertex g).1 at hyFormula
  have hstrict := M.edgeInterval_parameter_lt e f.2.2
  change M.edgeParameterValue e (M.fanFirstVertex f).1 <
    M.edgeParameterValue e (M.fanSecondVertex f).1 at hstrict
  have hxNormalized :
      M.edgeParameterValue e (M.fanFaceMap f x) =
        M.edgeParameterValue e (M.fanFirstVertex f).1 +
          x (M.fanSecondVertex f) *
            (M.edgeParameterValue e (M.fanSecondVertex f).1 -
              M.edgeParameterValue e (M.fanFirstVertex f).1) := by
    calc
      M.edgeParameterValue e (M.fanFaceMap f x) =
          x (M.fanFirstVertex f) *
              M.edgeParameterValue e (M.fanFirstVertex f).1 +
            x (M.fanSecondVertex f) *
              M.edgeParameterValue e (M.fanSecondVertex f).1 := hxFormula
      _ = (x (M.fanFirstVertex f) + x (M.fanSecondVertex f)) *
              M.edgeParameterValue e (M.fanFirstVertex f).1 +
            x (M.fanSecondVertex f) *
              (M.edgeParameterValue e (M.fanSecondVertex f).1 -
                M.edgeParameterValue e (M.fanFirstVertex f).1) := by ring
      _ = _ := by rw [hxSum, one_mul]
  have hyNormalized :
      M.edgeParameterValue d (M.fanFaceMap g y) =
        M.edgeParameterValue d (M.fanFirstVertex g).1 +
          y (M.fanSecondVertex g) *
            (M.edgeParameterValue d (M.fanSecondVertex g).1 -
              M.edgeParameterValue d (M.fanFirstVertex g).1) := by
    calc
      M.edgeParameterValue d (M.fanFaceMap g y) =
          y (M.fanFirstVertex g) *
              M.edgeParameterValue d (M.fanFirstVertex g).1 +
            y (M.fanSecondVertex g) *
              M.edgeParameterValue d (M.fanSecondVertex g).1 := hyFormula
      _ = (y (M.fanFirstVertex g) + y (M.fanSecondVertex g)) *
              M.edgeParameterValue d (M.fanFirstVertex g).1 +
            y (M.fanSecondVertex g) *
              (M.edgeParameterValue d (M.fanSecondVertex g).1 -
                M.edgeParameterValue d (M.fanFirstVertex g).1) := by ring
      _ = _ := by rw [hySum, one_mul]
  have hyNormalized' :
      M.edgeParameterValue e (M.fanFaceMap f x) =
        M.edgeParameterValue e (M.fanFirstVertex f).1 +
          y (M.fanSecondVertex g) *
            (M.edgeParameterValue e (M.fanSecondVertex f).1 -
              M.edgeParameterValue e (M.fanFirstVertex f).1) := by
    calc
      M.edgeParameterValue e (M.fanFaceMap f x) =
          M.edgeParameterValue d (M.fanFaceMap g y) := hparameter
      _ = M.edgeParameterValue d (M.fanFirstVertex g).1 +
          y (M.fanSecondVertex g) *
            (M.edgeParameterValue d (M.fanSecondVertex g).1 -
              M.edgeParameterValue d (M.fanFirstVertex g).1) := hyNormalized
      _ = _ := by rw [← hfirstParameter, ← hsecondParameter]
  have hsecondWeight :
      x (M.fanSecondVertex f) = y (M.fanSecondVertex g) := by
    have hmul :
        x (M.fanSecondVertex f) *
            (M.edgeParameterValue e (M.fanSecondVertex f).1 -
              M.edgeParameterValue e (M.fanFirstVertex f).1) =
          y (M.fanSecondVertex g) *
            (M.edgeParameterValue e (M.fanSecondVertex f).1 -
              M.edgeParameterValue e (M.fanFirstVertex f).1) := by
      linarith [hxNormalized, hyNormalized']
    exact mul_right_cancel₀ (sub_ne_zero.mpr (ne_of_gt hstrict)) hmul
  have hfirstWeight :
      x (M.fanFirstVertex f) = y (M.fanFirstVertex g) := by
    linarith [hxSum, hySum, hsecondWeight]
  rw [M.extendFaceCoordinates_fanFace f x,
    M.extendFaceCoordinates_fanFace g y, hxCenter, hyCenter]
  simp only [Pi.single_zero, zero_add]
  rw [hfirstVal, hsecondVal, hfirstWeight, hsecondWeight]

/-- A zero-center fan point outside the relative interior of its base is a global marked point. -/
theorem fanFaceMap_mem_points_of_center_zero_of_not_base_weights_pos
    (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) = 0)
    (hxNot : ¬(0 < x (M.fanFirstVertex f) ∧
      0 < x (M.fanSecondVertex f))) :
    M.fanFaceMap f x ∈ M.points := by
  rcases M.fanEndpointData_of_center_eq_zero_of_not_base_weights_pos
      f x hxCenter hxNot with hxEnd | hxEnd
  · have hmap : M.fanFaceMap f x = (M.fanFirstVertex f).1 :=
      Subtype.ext hxEnd.1
    rw [hmap]
    exact ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
      (M.edgeIntervalFirst_mem_edgeMarks
        (K.faceEdge f.1 f.2.1) f.2.2)).1
  · have hmap : M.fanFaceMap f x = (M.fanSecondVertex f).1 :=
      Subtype.ext hxEnd.1
    rw [hmap]
    exact ((M.mem_edgeMarks_iff (K.faceEdge f.1 f.2.1) _).mp
      (M.edgeIntervalSecond_mem_edgeMarks
        (K.faceEdge f.1 f.2.1) f.2.2)).1

/-- Zero-center points in any two marked fan triangles have compatible global barycentric
coordinates. -/
theorem fanExtendedCoordinates_eq_of_faceMap_eq_of_center_zero
    {f g : M.FanFace}
    {x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f}}
    {y : stdSimplex ℝ {p // p ∈ M.fanFaceVertices g}}
    (hxy : M.fanFaceMap f x = M.fanFaceMap g y)
    (hxCenter : x (M.fanCenterVertex f) = 0)
    (hyCenter : y (M.fanCenterVertex g) = 0) :
    extendFaceCoordinates (M.fanFaceVertices f) x =
      extendFaceCoordinates (M.fanFaceVertices g) y := by
  let xPos := 0 < x (M.fanFirstVertex f) ∧
    0 < x (M.fanSecondVertex f)
  let yPos := 0 < y (M.fanFirstVertex g) ∧
    0 < y (M.fanSecondVertex g)
  by_cases hxPos : xPos
  · by_cases hyPos : yPos
    · exact
        M.fanExtendedCoordinates_eq_of_faceMap_eq_of_center_zero_of_base_weights_pos
          hxy hxCenter hyCenter hxPos.1 hxPos.2 hyPos.1 hyPos.2
    · have hyMarked :=
        M.fanFaceMap_mem_points_of_center_zero_of_not_base_weights_pos
          g y hyCenter hyPos
      have hxMarked : M.fanFaceMap f x ∈ M.points := by
        rw [hxy]
        exact hyMarked
      exact False.elim
        (M.fanFaceMap_not_mem_points_of_center_zero_of_base_weights_pos
          f x hxCenter hxPos.1 hxPos.2 hxMarked)
  · have hxMarked :=
      M.fanFaceMap_mem_points_of_center_zero_of_not_base_weights_pos
        f x hxCenter hxPos
    have hyNot : ¬yPos := by
      intro hyPos
      have hyMarked : M.fanFaceMap g y ∈ M.points := by
        rw [← hxy]
        exact hxMarked
      exact M.fanFaceMap_not_mem_points_of_center_zero_of_base_weights_pos
        g y hyCenter hyPos.1 hyPos.2 hyMarked
    rcases M.fanEndpointData_of_center_eq_zero_of_not_base_weights_pos
        f x hxCenter hxPos with hxEnd | hxEnd
    · rcases M.fanEndpointData_of_center_eq_zero_of_not_base_weights_pos
          g y hyCenter hyNot with hyEnd | hyEnd
      · have hvFun :
            (M.fanFirstVertex f).1.1 = (M.fanFirstVertex g).1.1 :=
          hxEnd.1.symm.trans ((congrArg Subtype.val hxy).trans hyEnd.1)
        have hv : (M.fanFirstVertex f).1 = (M.fanFirstVertex g).1 :=
          Subtype.ext hvFun
        rw [hxEnd.2, hyEnd.2, hv]
      · have hvFun :
            (M.fanFirstVertex f).1.1 = (M.fanSecondVertex g).1.1 :=
          hxEnd.1.symm.trans ((congrArg Subtype.val hxy).trans hyEnd.1)
        have hv : (M.fanFirstVertex f).1 = (M.fanSecondVertex g).1 :=
          Subtype.ext hvFun
        rw [hxEnd.2, hyEnd.2, hv]
    · rcases M.fanEndpointData_of_center_eq_zero_of_not_base_weights_pos
          g y hyCenter hyNot with hyEnd | hyEnd
      · have hvFun :
            (M.fanSecondVertex f).1.1 = (M.fanFirstVertex g).1.1 :=
          hxEnd.1.symm.trans ((congrArg Subtype.val hxy).trans hyEnd.1)
        have hv : (M.fanSecondVertex f).1 = (M.fanFirstVertex g).1 :=
          Subtype.ext hvFun
        rw [hxEnd.2, hyEnd.2, hv]
      · have hvFun :
            (M.fanSecondVertex f).1.1 = (M.fanSecondVertex g).1.1 :=
          hxEnd.1.symm.trans ((congrArg Subtype.val hxy).trans hyEnd.1)
        have hv : (M.fanSecondVertex f).1 = (M.fanSecondVertex g).1 :=
          Subtype.ext hvFun
        rw [hxEnd.2, hyEnd.2, hv]

/-- After removing the common center contribution, equal points in one old parent face have
equal radial projections to its marked boundary. -/
theorem fanNormalizedBaseFaceMap_eq_of_same_parent
    (t : K.Face) (i j : ZMod 3)
    (a : M.EdgeInterval (K.faceEdge t i))
    (b : M.EdgeInterval (K.faceEdge t j))
    {x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices ⟨t, i, a⟩}}
    {y : stdSimplex ℝ {p // p ∈ M.fanFaceVertices ⟨t, j, b⟩}}
    (hxy : M.fanFaceMap ⟨t, i, a⟩ x =
      M.fanFaceMap ⟨t, j, b⟩ y)
    (hxCenter : x (M.fanCenterVertex ⟨t, i, a⟩) < 1)
    (hyCenter : y (M.fanCenterVertex ⟨t, j, b⟩) < 1) :
    M.fanFaceMap ⟨t, i, a⟩
        (M.fanNormalizedBasePoint ⟨t, i, a⟩ x hxCenter) =
      M.fanFaceMap ⟨t, j, b⟩
        (M.fanNormalizedBasePoint ⟨t, j, b⟩ y hyCenter) := by
  let cx := x (M.fanCenterVertex ⟨t, i, a⟩)
  let cy := y (M.fanCenterVertex ⟨t, j, b⟩)
  have hc : cx = cy :=
    M.fanCenterWeight_eq_of_faceMap_eq_of_parent_eq t i j a b hxy
  have hxLine :=
    M.fanFaceMap_eq_lineMap_normalizedBase ⟨t, i, a⟩ x hxCenter
  have hyLine :=
    M.fanFaceMap_eq_lineMap_normalizedBase ⟨t, j, b⟩ y hyCenter
  apply Subtype.ext
  funext v
  have hline :
      AffineMap.lineMap (K.faceCenter t).1
          (M.fanFaceMap ⟨t, i, a⟩
            (M.fanNormalizedBasePoint ⟨t, i, a⟩ x hxCenter)).1
          (1 - cx) =
        AffineMap.lineMap (K.faceCenter t).1
          (M.fanFaceMap ⟨t, j, b⟩
            (M.fanNormalizedBasePoint ⟨t, j, b⟩ y hyCenter)).1
          (1 - cy) := by
    rw [← hxLine, ← hyLine]
    exact congrArg Subtype.val hxy
  have hcoord := congrFun hline v
  rw [AffineMap.lineMap_apply_module,
    AffineMap.lineMap_apply_module, ← hc] at hcoord
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  have hd : 1 - cx ≠ 0 := (sub_pos.mpr hxCenter).ne'
  apply mul_left_cancel₀ hd
  nlinarith

/-- Restoring the center weight after radial projection recovers the original zero-extended
coordinates. -/
theorem extendFaceCoordinates_eq_center_add_smul_normalizedBase
    (f : M.FanFace)
    (x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f})
    (hxCenter : x (M.fanCenterVertex f) < 1) :
    extendFaceCoordinates (M.fanFaceVertices f) x =
      Pi.single (M.fanCenterVertex f).1
          (x (M.fanCenterVertex f)) +
        (1 - x (M.fanCenterVertex f)) •
          extendFaceCoordinates (M.fanFaceVertices f)
            (M.fanNormalizedBasePoint f x hxCenter) := by
  classical
  let d := 1 - x (M.fanCenterVertex f)
  have hd : d ≠ 0 := (sub_pos.mpr hxCenter).ne'
  have hfirst : d • Pi.single (M.fanFirstVertex f).1
        (x (M.fanFirstVertex f) / d) =
      Pi.single (M.fanFirstVertex f).1
        (x (M.fanFirstVertex f)) := by
    funext v
    by_cases hv : (M.fanFirstVertex f).1 = v
    · simp only [hv, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      exact mul_div_cancel₀ _ hd
    · simp only [Pi.smul_apply, ne_eq, hv, not_false_eq_true, Pi.single_eq_of_ne', smul_eq_mul,
        mul_zero]
  have hsecond : d • Pi.single (M.fanSecondVertex f).1
        (x (M.fanSecondVertex f) / d) =
      Pi.single (M.fanSecondVertex f).1
        (x (M.fanSecondVertex f)) := by
    funext v
    by_cases hv : (M.fanSecondVertex f).1 = v
    · simp only [hv, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      exact mul_div_cancel₀ _ hd
    · simp [hv]
  rw [M.extendFaceCoordinates_fanFace f x,
    M.extendFaceCoordinates_fanFace f
      (M.fanNormalizedBasePoint f x hxCenter),
    M.fanNormalizedBasePoint_apply_center f x hxCenter,
    M.fanNormalizedBasePoint_apply_first f x hxCenter,
    M.fanNormalizedBasePoint_apply_second f x hxCenter]
  dsimp only [d] at hfirst hsecond
  rw [smul_add, smul_add, Pi.single_zero, smul_zero, zero_add]
  change
    Pi.single (M.fanCenterVertex f).1
          (x (M.fanCenterVertex f)) +
        Pi.single (M.fanFirstVertex f).1
          (x (M.fanFirstVertex f)) +
      Pi.single (M.fanSecondVertex f).1
          (x (M.fanSecondVertex f)) =
      Pi.single (M.fanCenterVertex f).1
          (x (M.fanCenterVertex f)) +
        ((1 - x (M.fanCenterVertex f)) •
            Pi.single (M.fanFirstVertex f).1
              (x (M.fanFirstVertex f) /
                (1 - x (M.fanCenterVertex f))) +
          (1 - x (M.fanCenterVertex f)) •
            Pi.single (M.fanSecondVertex f).1
              (x (M.fanSecondVertex f) /
                (1 - x (M.fanCenterVertex f))))
  rw [hfirst, hsecond, add_assoc]

/-- Marked fan triangles in one old parent face assign the same global barycentric coordinates
to every common point. -/
theorem fanExtendedCoordinates_eq_of_faceMap_eq_of_same_parent
    (t : K.Face) (i j : ZMod 3)
    (a : M.EdgeInterval (K.faceEdge t i))
    (b : M.EdgeInterval (K.faceEdge t j))
    {x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices ⟨t, i, a⟩}}
    {y : stdSimplex ℝ {p // p ∈ M.fanFaceVertices ⟨t, j, b⟩}}
    (hxy : M.fanFaceMap ⟨t, i, a⟩ x =
      M.fanFaceMap ⟨t, j, b⟩ y) :
    extendFaceCoordinates (M.fanFaceVertices ⟨t, i, a⟩) x =
      extendFaceCoordinates (M.fanFaceVertices ⟨t, j, b⟩) y := by
  have hc := M.fanCenterWeight_eq_of_faceMap_eq_of_parent_eq
    t i j a b hxy
  have hxSum := M.fanWeights_sum ⟨t, i, a⟩ x
  have hySum := M.fanWeights_sum ⟨t, j, b⟩ y
  change x (M.fanCenterVertex ⟨t, i, a⟩) +
      x (M.fanFirstVertex ⟨t, i, a⟩) +
    x (M.fanSecondVertex ⟨t, i, a⟩) = 1 at hxSum
  change y (M.fanCenterVertex ⟨t, j, b⟩) +
      y (M.fanFirstVertex ⟨t, j, b⟩) +
    y (M.fanSecondVertex ⟨t, j, b⟩) = 1 at hySum
  have hxFirstNonneg := x.2.1 (M.fanFirstVertex ⟨t, i, a⟩)
  have hxSecondNonneg := x.2.1 (M.fanSecondVertex ⟨t, i, a⟩)
  have hyFirstNonneg := y.2.1 (M.fanFirstVertex ⟨t, j, b⟩)
  have hySecondNonneg := y.2.1 (M.fanSecondVertex ⟨t, j, b⟩)
  change 0 ≤ x (M.fanFirstVertex ⟨t, i, a⟩) at hxFirstNonneg
  change 0 ≤ x (M.fanSecondVertex ⟨t, i, a⟩) at hxSecondNonneg
  change 0 ≤ y (M.fanFirstVertex ⟨t, j, b⟩) at hyFirstNonneg
  change 0 ≤ y (M.fanSecondVertex ⟨t, j, b⟩) at hySecondNonneg
  have hxCenterLe : x (M.fanCenterVertex ⟨t, i, a⟩) ≤ 1 := by
    linarith
  have hyCenterLe : y (M.fanCenterVertex ⟨t, j, b⟩) ≤ 1 := by
    linarith
  by_cases hxOne : x (M.fanCenterVertex ⟨t, i, a⟩) = 1
  · have hyOne : y (M.fanCenterVertex ⟨t, j, b⟩) = 1 :=
      hc.symm.trans hxOne
    have hxFirstZero : x (M.fanFirstVertex ⟨t, i, a⟩) = 0 := by
      linarith
    have hxSecondZero : x (M.fanSecondVertex ⟨t, i, a⟩) = 0 := by
      linarith
    have hyFirstZero : y (M.fanFirstVertex ⟨t, j, b⟩) = 0 := by
      linarith
    have hySecondZero : y (M.fanSecondVertex ⟨t, j, b⟩) = 0 := by
      linarith
    rw [M.extendFaceCoordinates_fanFace ⟨t, i, a⟩ x,
      M.extendFaceCoordinates_fanFace ⟨t, j, b⟩ y,
      hxOne, hyOne, hxFirstZero, hxSecondZero,
      hyFirstZero, hySecondZero]
    simp only [Pi.single_zero, add_zero]
    rfl
  · have hxCenter : x (M.fanCenterVertex ⟨t, i, a⟩) < 1 :=
      lt_of_le_of_ne hxCenterLe hxOne
    have hyOne : y (M.fanCenterVertex ⟨t, j, b⟩) ≠ 1 := by
      intro h
      exact hxOne (hc.trans h)
    have hyCenter : y (M.fanCenterVertex ⟨t, j, b⟩) < 1 :=
      lt_of_le_of_ne hyCenterLe hyOne
    have hbaseMap :=
      M.fanNormalizedBaseFaceMap_eq_of_same_parent
        t i j a b hxy hxCenter hyCenter
    have hbaseCoords :=
      M.fanExtendedCoordinates_eq_of_faceMap_eq_of_center_zero hbaseMap
        (M.fanNormalizedBasePoint_apply_center ⟨t, i, a⟩ x hxCenter)
        (M.fanNormalizedBasePoint_apply_center ⟨t, j, b⟩ y hyCenter)
    calc
      extendFaceCoordinates (M.fanFaceVertices ⟨t, i, a⟩) x =
          Pi.single (M.fanCenterVertex ⟨t, i, a⟩).1
              (x (M.fanCenterVertex ⟨t, i, a⟩)) +
            (1 - x (M.fanCenterVertex ⟨t, i, a⟩)) •
              extendFaceCoordinates (M.fanFaceVertices ⟨t, i, a⟩)
                (M.fanNormalizedBasePoint ⟨t, i, a⟩ x hxCenter) :=
        M.extendFaceCoordinates_eq_center_add_smul_normalizedBase
          ⟨t, i, a⟩ x hxCenter
      _ = Pi.single (M.fanCenterVertex ⟨t, j, b⟩).1
              (y (M.fanCenterVertex ⟨t, j, b⟩)) +
            (1 - y (M.fanCenterVertex ⟨t, j, b⟩)) •
              extendFaceCoordinates (M.fanFaceVertices ⟨t, j, b⟩)
                (M.fanNormalizedBasePoint ⟨t, j, b⟩ y hyCenter) := by
        change Pi.single (K.faceCenter t)
              (x (M.fanCenterVertex ⟨t, i, a⟩)) +
            (1 - x (M.fanCenterVertex ⟨t, i, a⟩)) •
              extendFaceCoordinates (M.fanFaceVertices ⟨t, i, a⟩)
                (M.fanNormalizedBasePoint ⟨t, i, a⟩ x hxCenter) =
          Pi.single (K.faceCenter t)
              (y (M.fanCenterVertex ⟨t, j, b⟩)) +
            (1 - y (M.fanCenterVertex ⟨t, j, b⟩)) •
              extendFaceCoordinates (M.fanFaceVertices ⟨t, j, b⟩)
                (M.fanNormalizedBasePoint ⟨t, j, b⟩ y hyCenter)
        rw [hc, hbaseCoords]
      _ = extendFaceCoordinates (M.fanFaceVertices ⟨t, j, b⟩) y :=
        (M.extendFaceCoordinates_eq_center_add_smul_normalizedBase
          ⟨t, j, b⟩ y hyCenter).symm

/-- All marked fan faces use one global barycentric coordinate system on overlaps. -/
theorem fanExtendedCoordinates_eq_of_faceMap_eq
    {f g : M.FanFace}
    {x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f}}
    {y : stdSimplex ℝ {p // p ∈ M.fanFaceVertices g}}
    (hxy : M.fanFaceMap f x = M.fanFaceMap g y) :
    extendFaceCoordinates (M.fanFaceVertices f) x =
      extendFaceCoordinates (M.fanFaceVertices g) y := by
  by_cases hfg : f.1 = g.1
  · rcases f with ⟨t, i, a⟩
    rcases g with ⟨s, j, b⟩
    dsimp only at hfg
    subst s
    exact M.fanExtendedCoordinates_eq_of_faceMap_eq_of_same_parent
      t i j a b hxy
  · have hxCenter :=
      M.fanCenterWeight_eq_zero_of_faceMap_eq_of_parent_ne hfg hxy
    have hyCenter :=
      M.fanCenterWeight_eq_zero_of_faceMap_eq_of_parent_ne
        (Ne.symm hfg) hxy.symm
    exact M.fanExtendedCoordinates_eq_of_faceMap_eq_of_center_zero
      hxy hxCenter hyCenter

/-- The finite set of every geometric point used as a marked fan vertex. -/
noncomputable def fanVertices : Finset K.realization :=
  (Finset.univ : Finset M.FanFace).biUnion M.fanFaceVertices

/-- Geometric vertices occurring in the global marked fan family. -/
abbrev FanVertex := {p : K.realization // p ∈ M.fanVertices}

/-- Include the three local vertices of one fan face in the global used-vertex type. -/
noncomputable def fanVertexEmbedding (f : M.FanFace) :
    {p // p ∈ M.fanFaceVertices f} ↪ M.FanVertex where
  toFun p := ⟨p.1, Finset.mem_biUnion.mpr
    ⟨f, Finset.mem_univ f, p.2⟩⟩
  inj' := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : M.FanVertex ↦ z.1) hpq

/-- The three vertices of a marked fan face, regarded as global used vertices. -/
noncomputable def globalFanFaceVertices (f : M.FanFace) :
    Finset M.FanVertex :=
  (M.fanFaceVertices f).attach.map (M.fanVertexEmbedding f)

theorem mem_globalFanFaceVertices_iff (f : M.FanFace) (v : M.FanVertex) :
    v ∈ M.globalFanFaceVertices f ↔
      v.1 ∈ M.fanFaceVertices f := by
  constructor
  · intro hv
    obtain ⟨p, -, hp⟩ := Finset.mem_map.mp hv
    have hval : p.1 = v.1 := congrArg Subtype.val hp
    rw [← hval]
    exact p.2
  · intro hv
    let p : {p // p ∈ M.fanFaceVertices f} := ⟨v.1, hv⟩
    apply Finset.mem_map.mpr
    refine ⟨p, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

/-- The center vertex of a fan face, included in the global fan-vertex type. -/
noncomputable def globalFanCenter (f : M.FanFace) : M.FanVertex :=
  M.fanVertexEmbedding f (M.fanCenterVertex f)

/-- The first base vertex of a fan face, included in the global fan-vertex type. -/
noncomputable def globalFanFirst (f : M.FanFace) : M.FanVertex :=
  M.fanVertexEmbedding f (M.fanFirstVertex f)

/-- The second base vertex of a fan face, included in the global fan-vertex type. -/
noncomputable def globalFanSecond (f : M.FanFace) : M.FanVertex :=
  M.fanVertexEmbedding f (M.fanSecondVertex f)

@[simp] theorem globalFanCenter_val (f : M.FanFace) :
    (M.globalFanCenter f).1 = K.faceCenter f.1 := rfl

@[simp] theorem globalFanFirst_val (f : M.FanFace) :
    (M.globalFanFirst f).1 =
      M.edgeIntervalFirst (K.faceEdge f.1 f.2.1) f.2.2 := rfl

@[simp] theorem globalFanSecond_val (f : M.FanFace) :
    (M.globalFanSecond f).1 =
      M.edgeIntervalSecond (K.faceEdge f.1 f.2.1) f.2.2 := rfl

theorem globalFanFaceVertices_eq (f : M.FanFace) :
    M.globalFanFaceVertices f =
      {M.globalFanCenter f, M.globalFanFirst f, M.globalFanSecond f} := by
  ext v
  rw [M.mem_globalFanFaceVertices_iff]
  simp only [fanFaceVertices, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (hv | hv | hv)
    · exact Or.inl (Subtype.ext hv)
    · exact Or.inr (Or.inl (Subtype.ext hv))
    · exact Or.inr (Or.inr (Subtype.ext hv))
  · rintro (hv | hv | hv)
    · exact Or.inl (congrArg Subtype.val hv)
    · exact Or.inr (Or.inl (congrArg Subtype.val hv))
    · exact Or.inr (Or.inr (congrArg Subtype.val hv))

theorem globalFanCenter_ne_first (f g : M.FanFace) :
    M.globalFanCenter f ≠ M.globalFanFirst g := by
  intro h
  exact M.fanCenter_ne_fanFirst f g (congrArg Subtype.val h)

theorem globalFanCenter_ne_second (f g : M.FanFace) :
    M.globalFanCenter f ≠ M.globalFanSecond g := by
  intro h
  exact M.fanCenter_ne_fanSecond f g (congrArg Subtype.val h)

theorem globalFanCenter_eq_iff (f g : M.FanFace) :
    M.globalFanCenter f = M.globalFanCenter g ↔ f.1 = g.1 := by
  constructor
  · intro h
    apply K.faceCenter_injective
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    simp only [globalFanCenter_val]
    rw [h]

/-- A two-element subface not containing the fan center is exactly the global base pair. -/
theorem eq_globalFanBase_of_card_two_of_subset_of_center_notMem
    (f : M.FanFace) {e : Finset M.FanVertex}
    (hecard : e.card = 2) (hef : e ⊆ M.globalFanFaceVertices f)
    (hcenter : M.globalFanCenter f ∉ e) :
    e = {M.globalFanFirst f, M.globalFanSecond f} := by
  rw [M.globalFanFaceVertices_eq f] at hef
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    have hv' := hef hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
    rcases hv' with hv' | hv' | hv'
    · exact False.elim (hcenter (hv' ▸ hv))
    · simp [hv']
    · simp [hv']
  · rw [hecard]
    have hne : M.globalFanFirst f ≠ M.globalFanSecond f := by
      intro h
      exact M.edgeIntervalFirst_ne_second
        (K.faceEdge f.1 f.2.1) f.2.2 (congrArg Subtype.val h)
    simp [hne]

/-- Relabel global vertices of one face by their underlying intrinsic points. -/
noncomputable def fanFaceVertexEquiv (f : M.FanFace) :
    {v // v ∈ M.globalFanFaceVertices f} ≃
      {p // p ∈ M.fanFaceVertices f} where
  toFun v := ⟨v.1.1,
    (M.mem_globalFanFaceVertices_iff f v.1).mp v.2⟩
  invFun p := ⟨⟨p.1, Finset.mem_biUnion.mpr
      ⟨f, Finset.mem_univ f, p.2⟩⟩,
    (M.mem_globalFanFaceVertices_iff f _).mpr p.2⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

@[simp] theorem fanFaceVertexEquiv_apply_val (f : M.FanFace)
    (v : {v // v ∈ M.globalFanFaceVertices f}) :
    (M.fanFaceVertexEquiv f v).1 = v.1.1 := rfl

/-- Relabel a simplex on global fan vertices as a simplex on geometric points. -/
noncomputable def fanRelabelSimplex (f : M.FanFace)
    (x : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices f}) :
    stdSimplex ℝ {p // p ∈ M.fanFaceVertices f} :=
  stdSimplex.map (M.fanFaceVertexEquiv f) x

theorem fanRelabel_extended_apply (f : M.FanFace)
    (x : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices f})
    (v : M.FanVertex) :
    extendFaceCoordinates (M.fanFaceVertices f)
        (M.fanRelabelSimplex f x) v.1 =
      extendFaceCoordinates (M.globalFanFaceVertices f) x v := by
  classical
  by_cases hv : v ∈ M.globalFanFaceVertices f
  · have hp : v.1 ∈ M.fanFaceVertices f :=
      (M.mem_globalFanFaceVertices_iff f v).mp hv
    rw [extendFaceCoordinates_of_mem _ _ hp,
      extendFaceCoordinates_of_mem _ _ hv]
    simp only [fanRelabelSimplex, stdSimplex.map_coe,
      FunOnFinite.linearMap_apply_apply]
    let q : {q // q ∈ M.globalFanFaceVertices f} := ⟨v, hv⟩
    have hfilter : Finset.univ.filter
        (fun z : {z // z ∈ M.globalFanFaceVertices f} ↦
          M.fanFaceVertexEquiv f z = ⟨v.1, hp⟩) = {q} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hz
        have hactual : z.1.1 = q.1.1 := by
          simpa only [M.fanFaceVertexEquiv_apply_val f] using
            congrArg
              (fun w : {p // p ∈ M.fanFaceVertices f} ↦ w.1) hz
        exact Subtype.ext (Subtype.ext hactual)
      · intro hz
        subst z
        apply Subtype.ext
        rfl
    rw [hfilter]
    simp [q]
  · have hp : v.1 ∉ M.fanFaceVertices f :=
      fun hp ↦ hv ((M.mem_globalFanFaceVertices_iff f v).mpr hp)
    rw [extendFaceCoordinates_of_notMem _ _ hp,
      extendFaceCoordinates_of_notMem _ _ hv]

theorem fanRelabel_extended_eq_iff
    {f g : M.FanFace}
    {x : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices f}}
    {y : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices g}} :
    extendFaceCoordinates (M.fanFaceVertices f)
        (M.fanRelabelSimplex f x) =
      extendFaceCoordinates (M.fanFaceVertices g)
        (M.fanRelabelSimplex g y) ↔
    extendFaceCoordinates (M.globalFanFaceVertices f) x =
      extendFaceCoordinates (M.globalFanFaceVertices g) y := by
  constructor
  · intro h
    funext v
    rw [← M.fanRelabel_extended_apply f x v,
      ← M.fanRelabel_extended_apply g y v,
      congrFun h v.1]
  · intro h
    funext p
    by_cases hpf : p ∈ M.fanFaceVertices f
    · let v : M.FanVertex :=
        ⟨p, Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ f, hpf⟩⟩
      have hv := congrFun h v
      rw [← M.fanRelabel_extended_apply f x v,
        ← M.fanRelabel_extended_apply g y v] at hv
      exact hv
    · by_cases hpg : p ∈ M.fanFaceVertices g
      · let v : M.FanVertex :=
          ⟨p, Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, hpg⟩⟩
        have hv := congrFun h v
        rw [← M.fanRelabel_extended_apply f x v,
          ← M.fanRelabel_extended_apply g y v] at hv
        exact hv
      · rw [extendFaceCoordinates_of_notMem _ _ hpf,
          extendFaceCoordinates_of_notMem _ _ hpg]

/-- One marked fan face parametrized by the global used-vertex type. -/
noncomputable def globalFanFaceMap (f : M.FanFace) :
    stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices f} → K.realization :=
  fun x ↦ M.fanFaceMap f (M.fanRelabelSimplex f x)

theorem continuous_globalFanFaceMap (f : M.FanFace) :
    Continuous (M.globalFanFaceMap f) :=
  (M.continuous_fanFaceMap f).comp
    (stdSimplex.continuous_map (M.fanFaceVertexEquiv f))

theorem range_globalFanFaceMap (f : M.FanFace) :
    Set.range (M.globalFanFaceMap f) = Set.range (M.fanFaceMap f) := by
  apply Set.Subset.antisymm
  · rintro p ⟨x, rfl⟩
    exact Set.mem_range_self _
  · rintro p ⟨x, rfl⟩
    let y := stdSimplex.map (M.fanFaceVertexEquiv f).symm x
    refine ⟨y, congrArg (M.fanFaceMap f) ?_⟩
    change stdSimplex.map (M.fanFaceVertexEquiv f) y = x
    dsimp only [y]
    rw [stdSimplex.map_comp_apply]
    have he : (M.fanFaceVertexEquiv f : _ → _) ∘
        (M.fanFaceVertexEquiv f).symm = id := by
      funext z
      exact (M.fanFaceVertexEquiv f).apply_symm_apply z
    rw [he, stdSimplex.map_id_apply]

theorem globalFanFaceMap_mem_faceCarrier (f : M.FanFace)
    (x : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices f}) :
    M.globalFanFaceMap f x ∈ K.faceCarrier f.1.1 :=
  M.fanFaceMap_mem_faceCarrier f (M.fanRelabelSimplex f x)

/-- The affine map that evaluates global fan-vertex coordinates in the old intrinsic barycentric
space. -/
noncomputable def fanBarycentricAffine :
    (M.FanVertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
  (∑ v : M.FanVertex,
    (LinearMap.proj v).smulRight (v.1.1 : K.Vertex → ℝ)).toAffineMap

@[simp] theorem fanBarycentricAffine_apply (z : M.FanVertex → ℝ) :
    M.fanBarycentricAffine z =
      fun k ↦ ∑ v : M.FanVertex, z v * v.1.1 k := by
  funext k
  simp [fanBarycentricAffine, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- A globally relabeled fan-face map is affine evaluation at its actual intrinsic vertices. -/
theorem globalFanFaceMap_val_eq_fanBarycentricAffine
    (f : M.FanFace)
    (x : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices f}) :
    (M.globalFanFaceMap f x).1 =
      M.fanBarycentricAffine
        (extendFaceCoordinates (M.globalFanFaceVertices f) x) := by
  classical
  funext k
  change (∑ p : {p // p ∈ M.fanFaceVertices f},
      M.fanRelabelSimplex f x p * p.1.1 k) =
    M.fanBarycentricAffine
      (extendFaceCoordinates (M.globalFanFaceVertices f) x) k
  rw [M.fanBarycentricAffine_apply]
  change (∑ p : {p // p ∈ M.fanFaceVertices f},
      M.fanRelabelSimplex f x p * p.1.1 k) =
    ∑ v : M.FanVertex,
      extendFaceCoordinates (M.globalFanFaceVertices f) x v * v.1.1 k
  have hsupport :
      (∑ v : M.FanVertex,
          extendFaceCoordinates (M.globalFanFaceVertices f) x v * v.1.1 k) =
        ∑ v ∈ M.globalFanFaceVertices f,
          extendFaceCoordinates (M.globalFanFaceVertices f) x v * v.1.1 k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    rw [extendFaceCoordinates_of_notMem _ _ hv, zero_mul]
  rw [hsupport]
  rw [← sum_attach_mul_eq_sum_extendFaceCoordinates
    (M.globalFanFaceVertices f) x (fun v ↦ v.1.1 k)]
  let e := M.fanFaceVertexEquiv f
  calc
    (∑ p : {p // p ∈ M.fanFaceVertices f},
        M.fanRelabelSimplex f x p * p.1.1 k) =
      ∑ v : {v // v ∈ M.globalFanFaceVertices f},
        M.fanRelabelSimplex f x (e v) * (e v).1.1 k :=
      (e.sum_comp
        (fun p ↦ M.fanRelabelSimplex f x p * p.1.1 k)).symm
    _ = ∑ v : {v // v ∈ M.globalFanFaceVertices f},
        x v * v.1.1.1 k := by
      apply Finset.sum_congr rfl
      intro v _
      have hweight := M.fanRelabel_extended_apply f x v.1
      change extendFaceCoordinates (M.fanFaceVertices f)
          (M.fanRelabelSimplex f x) (e v).1 =
        extendFaceCoordinates (M.globalFanFaceVertices f) x v.1 at hweight
      rw [extendFaceCoordinates_of_mem _ _ (e v).2,
        extendFaceCoordinates_of_mem _ _ v.2] at hweight
      rw [hweight]
      rfl

/-- Equal zero-extended geometric-point coordinates give equal marked fan images. -/
theorem fanFaceMap_eq_of_extendedCoordinates_eq
    {f g : M.FanFace}
    {x : stdSimplex ℝ {p // p ∈ M.fanFaceVertices f}}
    {y : stdSimplex ℝ {p // p ∈ M.fanFaceVertices g}}
    (hxy : extendFaceCoordinates (M.fanFaceVertices f) x =
      extendFaceCoordinates (M.fanFaceVertices g) y) :
    M.fanFaceMap f x = M.fanFaceMap g y := by
  apply Subtype.ext
  funext v
  change (∑ p, x p * p.1.1 v) = ∑ p, y p * p.1.1 v
  exact sum_extendFaceCoordinates_eq_of_eq x y hxy (fun p ↦ p.1 v)

/-- Equal global fan coordinates are sufficient for equality of geometric images. -/
theorem globalFanFaceMap_eq_of_extendedCoordinates_eq
    {f g : M.FanFace}
    {x : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices f}}
    {y : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices g}}
    (hxy : extendFaceCoordinates (M.globalFanFaceVertices f) x =
      extendFaceCoordinates (M.globalFanFaceVertices g) y) :
    M.globalFanFaceMap f x = M.globalFanFaceMap g y :=
  M.fanFaceMap_eq_of_extendedCoordinates_eq
    ((M.fanRelabel_extended_eq_iff).mpr hxy)

/-- Equal geometric images of globally relabeled marked fan faces have equal zero-extended
barycentric coordinates. -/
theorem globalFanExtendedCoordinates_eq_of_faceMap_eq
    {f g : M.FanFace}
    {x : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices f}}
    {y : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices g}}
    (hxy : M.globalFanFaceMap f x = M.globalFanFaceMap g y) :
    extendFaceCoordinates (M.globalFanFaceVertices f) x =
      extendFaceCoordinates (M.globalFanFaceVertices g) y :=
  (M.fanRelabel_extended_eq_iff).mp
    (M.fanExtendedCoordinates_eq_of_faceMap_eq hxy)

/-- Exact face-to-face compatibility of the globally relabeled marked fan family. -/
theorem globalFanFaceMap_eq_iff
    {f g : M.FanFace}
    {x : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices f}}
    {y : stdSimplex ℝ {v // v ∈ M.globalFanFaceVertices g}} :
    M.globalFanFaceMap f x = M.globalFanFaceMap g y ↔
      extendFaceCoordinates (M.globalFanFaceVertices f) x =
        extendFaceCoordinates (M.globalFanFaceVertices g) y :=
  ⟨M.globalFanExtendedCoordinates_eq_of_faceMap_eq,
    M.globalFanFaceMap_eq_of_extendedCoordinates_eq⟩

/-- The finite globally compatible marked fan family as an ambient triangle complex in the old
intrinsic realization. -/
noncomputable abbrev markedFanLocallyFiniteTriangleComplex :
    LocallyFiniteTriangleComplex K.realization where
  Vertex := M.FanVertex
  vertexDecidableEq := inferInstance
  Face := M.FanFace
  faceDecidableEq := inferInstance
  faceVertices := M.globalFanFaceVertices
  faceVertices_card := by
    intro f
    rw [globalFanFaceVertices, Finset.card_map, Finset.card_attach,
      M.fanFaceVertices_card f]
  vertex_used := by
    rintro ⟨p, hp⟩
    obtain ⟨f, -, hpf⟩ := Finset.mem_biUnion.mp hp
    exact ⟨f, (M.mem_globalFanFaceVertices_iff f _).mpr hpf⟩
  faceMap := M.globalFanFaceMap
  faceMap_continuous := M.continuous_globalFanFaceMap
  faceMap_eq_iff := by
    intro f g x y
    exact M.globalFanFaceMap_eq_iff
  locallyFinite := locallyFinite_of_finite _

private theorem oldFaceEdge_eq_of_globalFanBase_eq (f g : M.FanFace)
    (hbase : ({M.globalFanFirst f, M.globalFanSecond f} : Finset M.FanVertex) =
      {M.globalFanFirst g, M.globalFanSecond g}) :
    K.faceEdge f.1 f.2.1 = K.faceEdge g.1 g.2.1 := by
  let E := K.faceEdge f.1 f.2.1
  let D := K.faceEdge g.1 g.2.1
  let p₀ := (M.globalFanFirst f).1
  let p₁ := (M.globalFanSecond f).1
  have hp₀E : p₀ ∈ K.faceCarrier E.1 :=
    ((M.mem_edgeMarks_iff E _).mp (M.edgeIntervalFirst_mem_edgeMarks E f.2.2)).2
  have hp₁E : p₁ ∈ K.faceCarrier E.1 :=
    ((M.mem_edgeMarks_iff E _).mp (M.edgeIntervalSecond_mem_edgeMarks E f.2.2)).2
  have hp₀Pair : M.globalFanFirst f ∈
      ({M.globalFanFirst g, M.globalFanSecond g} : Finset M.FanVertex) := by
    rw [← hbase]
    simp
  have hp₁Pair : M.globalFanSecond f ∈
      ({M.globalFanFirst g, M.globalFanSecond g} : Finset M.FanVertex) := by
    rw [← hbase]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp₀Pair hp₁Pair
  have hp₀D : p₀ ∈ K.faceCarrier D.1 := by
    change (M.globalFanFirst f).1 ∈ K.faceCarrier D.1
    rcases hp₀Pair with hp₀Pair | hp₀Pair
    · rw [congrArg Subtype.val hp₀Pair]
      exact ((M.mem_edgeMarks_iff D _).mp (M.edgeIntervalFirst_mem_edgeMarks D g.2.2)).2
    · rw [congrArg Subtype.val hp₀Pair]
      exact ((M.mem_edgeMarks_iff D _).mp (M.edgeIntervalSecond_mem_edgeMarks D g.2.2)).2
  have hp₁D : p₁ ∈ K.faceCarrier D.1 := by
    change (M.globalFanSecond f).1 ∈ K.faceCarrier D.1
    rcases hp₁Pair with hp₁Pair | hp₁Pair
    · rw [congrArg Subtype.val hp₁Pair]
      exact ((M.mem_edgeMarks_iff D _).mp (M.edgeIntervalFirst_mem_edgeMarks D g.2.2)).2
    · rw [congrArg Subtype.val hp₁Pair]
      exact ((M.mem_edgeMarks_iff D _).mp (M.edgeIntervalSecond_mem_edgeMarks D g.2.2)).2
  have hpNe : p₀ ≠ p₁ := M.edgeIntervalFirst_ne_second E f.2.2
  exact K.edge_eq_of_two_distinct_common_points E D hp₀E hp₀D hp₁E hp₁D hpNe

/-- The maximal global fan-face family inherits surface edge valence from the old intrinsic
complex. -/
theorem globalFanFaceFamily_edge_valence
    (hK : K.HasSurfaceEdgeValence) (e : Finset M.FanVertex)
    (hecard : e.card = 2) :
    (((Finset.univ : Finset M.FanFace).image M.globalFanFaceVertices
        ).filter fun s ↦ e ⊆ s).card ≤ 2 := by
  classical
  by_contra hle
  have hthree :
      2 <
        (((Finset.univ : Finset M.FanFace).image
            M.globalFanFaceVertices).filter fun s ↦ e ⊆ s).card := by
    omega
  obtain ⟨s₀, s₁, s₂, hs₀, hs₁, hs₂, hs₀₁, hs₀₂, hs₁₂⟩ :=
    Finset.two_lt_card_iff.mp hthree
  obtain ⟨hs₀Face, he₀⟩ := Finset.mem_filter.mp hs₀
  obtain ⟨hs₁Face, he₁⟩ := Finset.mem_filter.mp hs₁
  obtain ⟨hs₂Face, he₂⟩ := Finset.mem_filter.mp hs₂
  obtain ⟨f₀, -, hf₀⟩ := Finset.mem_image.mp hs₀Face
  obtain ⟨f₁, -, hf₁⟩ := Finset.mem_image.mp hs₁Face
  obtain ⟨f₂, -, hf₂⟩ := Finset.mem_image.mp hs₂Face
  subst s₀
  subst s₁
  subst s₂
  have global_eq_of_local_eq {f g : M.FanFace}
      (h : M.fanFaceVertices f = M.fanFaceVertices g) :
      M.globalFanFaceVertices f = M.globalFanFaceVertices g := by
    ext v
    rw [M.mem_globalFanFaceVertices_iff,
      M.mem_globalFanFaceVertices_iff, h]
  by_cases hcenter : M.globalFanCenter f₀ ∈ e
  · have heraseCard : (e.erase (M.globalFanCenter f₀)).card = 1 := by
      rw [Finset.card_erase_of_mem hcenter, hecard]
    obtain ⟨p, hpErase⟩ := Finset.card_eq_one.mp heraseCard
    have hpEraseMem : p ∈ e.erase (M.globalFanCenter f₀) := by
      rw [hpErase]
      exact Finset.mem_singleton_self p
    have hpMem : p ∈ e := (Finset.mem_erase.mp hpEraseMem).2
    have hpNe : p ≠ M.globalFanCenter f₀ :=
      (Finset.mem_erase.mp hpEraseMem).1
    have incidentData (g : M.FanFace)
        (heg : e ⊆ M.globalFanFaceVertices g) :
        f₀.1 = g.1 ∧
          (p.1 =
              M.edgeIntervalFirst (K.faceEdge g.1 g.2.1) g.2.2 ∨
            p.1 =
              M.edgeIntervalSecond (K.faceEdge g.1 g.2.1) g.2.2) := by
      have hcMem := heg hcenter
      rw [M.globalFanFaceVertices_eq g] at hcMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcMem
      have hparent : f₀.1 = g.1 := by
        rcases hcMem with hcMem | hcMem | hcMem
        · exact (M.globalFanCenter_eq_iff f₀ g).mp hcMem
        · exact False.elim (M.globalFanCenter_ne_first f₀ g hcMem)
        · exact False.elim (M.globalFanCenter_ne_second f₀ g hcMem)
      have hpFace := heg hpMem
      rw [M.globalFanFaceVertices_eq g] at hpFace
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpFace
      refine ⟨hparent, ?_⟩
      rcases hpFace with hpFace | hpFace | hpFace
      · have hcg :
            M.globalFanCenter g = M.globalFanCenter f₀ :=
          (M.globalFanCenter_eq_iff g f₀).mpr hparent.symm
        exact False.elim (hpNe (hpFace.trans hcg))
      · exact Or.inl (congrArg Subtype.val hpFace)
      · exact Or.inr (congrArg Subtype.val hpFace)
    have hd₀ := incidentData f₀ he₀
    have hd₁ := incidentData f₁ he₁
    have hd₂ := incidentData f₂ he₂
    rcases M.fanFaceVertices_pair_eq_of_three_same_parent_endpoint
        f₀ f₁ f₂ p.1 hd₁.1 hd₂.1 hd₀.2 hd₁.2 hd₂.2 with
      h₀₁ | h₀₂ | h₁₂
    · exact hs₀₁ (global_eq_of_local_eq h₀₁)
    · exact hs₀₂ (global_eq_of_local_eq h₀₂)
    · exact hs₁₂ (global_eq_of_local_eq h₁₂)
  · have center_not_of_incident (g : M.FanFace)
        (heg : e ⊆ M.globalFanFaceVertices g) :
        M.globalFanCenter g ∉ e := by
      intro hcg
      have hcgIn₀ := he₀ hcg
      rw [M.globalFanFaceVertices_eq f₀] at hcgIn₀
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcgIn₀
      rcases hcgIn₀ with hEq | hEq | hEq
      · exact hcenter (hEq ▸ hcg)
      · exact M.globalFanCenter_ne_first g f₀ hEq
      · exact M.globalFanCenter_ne_second g f₀ hEq
    have hb₀ :
        e = {M.globalFanFirst f₀, M.globalFanSecond f₀} :=
      M.eq_globalFanBase_of_card_two_of_subset_of_center_notMem
        f₀ hecard he₀ hcenter
    have hb₁ :
        e = {M.globalFanFirst f₁, M.globalFanSecond f₁} :=
      M.eq_globalFanBase_of_card_two_of_subset_of_center_notMem
        f₁ hecard he₁ (center_not_of_incident f₁ he₁)
    have hb₂ :
        e = {M.globalFanFirst f₂, M.globalFanSecond f₂} :=
      M.eq_globalFanBase_of_card_two_of_subset_of_center_notMem
        f₂ hecard he₂ (center_not_of_incident f₂ he₂)
    have hbase₀₁ :
        ({M.globalFanFirst f₀, M.globalFanSecond f₀} :
            Finset M.FanVertex) =
          {M.globalFanFirst f₁, M.globalFanSecond f₁} :=
      hb₀.symm.trans hb₁
    have hbase₀₂ :
        ({M.globalFanFirst f₀, M.globalFanSecond f₀} :
            Finset M.FanVertex) =
          {M.globalFanFirst f₂, M.globalFanSecond f₂} :=
      hb₀.symm.trans hb₂
    have hedge₀₁ := M.oldFaceEdge_eq_of_globalFanBase_eq f₀ f₁ hbase₀₁
    have hedge₀₂ := M.oldFaceEdge_eq_of_globalFanBase_eq f₀ f₂ hbase₀₂
    have faceVertices_eq_of_parent_eq_of_base_eq
        (g : M.FanFace) (hparent : f₀.1 = g.1)
        (hbase :
          ({M.globalFanFirst f₀, M.globalFanSecond f₀} :
              Finset M.FanVertex) =
            {M.globalFanFirst g, M.globalFanSecond g}) :
        M.globalFanFaceVertices f₀ = M.globalFanFaceVertices g := by
      rw [M.globalFanFaceVertices_eq f₀,
        M.globalFanFaceVertices_eq g]
      have hc :
          M.globalFanCenter f₀ = M.globalFanCenter g :=
        (M.globalFanCenter_eq_iff f₀ g).mpr hparent
      rw [hc, hbase]
    have hparent₀₁ : f₀.1 ≠ f₁.1 := by
      intro h
      exact hs₀₁
        (faceVertices_eq_of_parent_eq_of_base_eq f₁ h hbase₀₁)
    have hparent₀₂ : f₀.1 ≠ f₂.1 := by
      intro h
      exact hs₀₂
        (faceVertices_eq_of_parent_eq_of_base_eq f₂ h hbase₀₂)
    have hbase₁₂ :
        ({M.globalFanFirst f₁, M.globalFanSecond f₁} :
            Finset M.FanVertex) =
          {M.globalFanFirst f₂, M.globalFanSecond f₂} :=
      hbase₀₁.symm.trans hbase₀₂
    have hparent₁₂ : f₁.1 ≠ f₂.1 := by
      intro h
      have hc :
          M.globalFanCenter f₁ = M.globalFanCenter f₂ :=
        (M.globalFanCenter_eq_iff f₁ f₂).mpr h
      apply hs₁₂
      rw [M.globalFanFaceVertices_eq f₁,
        M.globalFanFaceVertices_eq f₂, hc, hbase₁₂]
    let E := K.faceEdge f₀.1 f₀.2.1
    have hf₀Incident :
        f₀.1.1 ∈ K.faces.filter fun t ↦ E.1 ⊆ t := by
      apply Finset.mem_filter.mpr
      exact ⟨f₀.1.2, K.faceEdge_subset_face f₀.1 f₀.2.1⟩
    have hf₁Incident :
        f₁.1.1 ∈ K.faces.filter fun t ↦ E.1 ⊆ t := by
      apply Finset.mem_filter.mpr
      refine ⟨f₁.1.2, ?_⟩
      change (K.faceEdge f₀.1 f₀.2.1).1 ⊆ f₁.1.1
      rw [hedge₀₁]
      exact K.faceEdge_subset_face f₁.1 f₁.2.1
    have hf₂Incident :
        f₂.1.1 ∈ K.faces.filter fun t ↦ E.1 ⊆ t := by
      apply Finset.mem_filter.mpr
      refine ⟨f₂.1.2, ?_⟩
      change (K.faceEdge f₀.1 f₀.2.1).1 ⊆ f₂.1.1
      rw [hedge₀₂]
      exact K.faceEdge_subset_face f₂.1 f₂.2.1
    have hparentThree :
        2 < (K.faces.filter fun t ↦ E.1 ⊆ t).card := by
      apply Finset.two_lt_card_iff.mpr
      refine ⟨f₀.1.1, f₁.1.1, f₂.1.1,
        hf₀Incident, hf₁Incident, hf₂Incident, ?_, ?_, ?_⟩
      · intro h
        exact hparent₀₁ (Subtype.ext h)
      · intro h
        exact hparent₀₂ (Subtype.ext h)
      · intro h
        exact hparent₁₂ (Subtype.ext h)
    have hbound := hK E.1 E.2
    omega

/-- The compact intrinsic complex underlying the global marked fan has surface edge valence. -/
theorem markedFanCompactIntrinsic_hasSurfaceEdgeValence
    (hK : K.HasSurfaceEdgeValence) :
    M.markedFanLocallyFiniteTriangleComplex.compactIntrinsic.HasSurfaceEdgeValence := by
  intro e he
  let fanFaceFintype : Fintype M.FanFace := inferInstance
  let L := M.markedFanLocallyFiniteTriangleComplex
  letI : Fintype L.Face := L.faceFintype
  have hfaces :
      L.compactIntrinsic.faces =
        (@Finset.univ M.FanFace fanFaceFintype).image
          M.globalFanFaceVertices := by
    rw [L.compactIntrinsic_faces]
    have huniv :
        (@Finset.univ L.Face L.faceFintype) =
          (@Finset.univ M.FanFace fanFaceFintype) := by
      ext f
      constructor <;> intro
      · exact @Finset.mem_univ M.FanFace fanFaceFintype f
      · exact @Finset.mem_univ L.Face inferInstance f
    rw [huniv]
    apply Finset.image_congr
    intro f _
    rfl
  rw [hfaces]
  exact M.globalFanFaceFamily_edge_valence hK e
    (M.markedFanLocallyFiniteTriangleComplex.compactIntrinsic.card_of_mem_edges he)

/-- The marked fan family covers the entire old intrinsic realization. -/
theorem markedFanLocallyFiniteTriangleComplex_support :
    M.markedFanLocallyFiniteTriangleComplex.support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  rcases p.2.2 with ⟨t, ht, hpt⟩
  let T : K.Face := ⟨t, ht⟩
  obtain ⟨i, j, x, hx⟩ :=
    M.exists_fanFaceMap_eq_of_mem_faceCarrier T hpt
  rw [LocallyFiniteTriangleComplex.support]
  apply Set.mem_iUnion.mpr
  refine ⟨(⟨T, i, j⟩ : M.FanFace), ?_⟩
  change p ∈ Set.range (M.globalFanFaceMap ⟨T, i, j⟩)
  rw [M.range_globalFanFaceMap]
  exact ⟨x, hx⟩

/-- The finite geometric triangulation of the old realization induced by all global edge marks. -/
noncomputable def markedFanGeometricTriangulation :
    GeometricTriangulation K.realization :=
  M.markedFanLocallyFiniteTriangleComplex.toGeometricTriangulation
    M.markedFanLocallyFiniteTriangleComplex_support

@[simp] theorem markedFanGeometricTriangulation_homeo_apply
    (x : M.markedFanLocallyFiniteTriangleComplex.compactIntrinsic.realization) :
    M.markedFanGeometricTriangulation.homeo x =
      M.markedFanLocallyFiniteTriangleComplex.compactEval x :=
  rfl

/-- The same evaluation homeomorphism with its source stated directly as the compact intrinsic
complex, avoiding any projection opacity through `GeometricTriangulation`. -/
noncomputable def markedFanHomeomorph :
    M.markedFanLocallyFiniteTriangleComplex.compactIntrinsic.realization ≃ₜ
      K.realization := by
  let L := M.markedFanLocallyFiniteTriangleComplex
  let e : L.compactIntrinsic.realization ≃ K.realization :=
    Equiv.ofBijective L.compactEval ⟨L.injective_compactEval, by
      intro y
      have hy : y ∈ L.support := by
        rw [M.markedFanLocallyFiniteTriangleComplex_support]
        exact Set.mem_univ y
      rw [← L.range_compactEval] at hy
      exact hy⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := e) L.continuous_compactEval

@[simp] theorem markedFanHomeomorph_apply
    (x : M.markedFanLocallyFiniteTriangleComplex.compactIntrinsic.realization) :
    M.markedFanHomeomorph x =
      M.markedFanLocallyFiniteTriangleComplex.compactEval x :=
  rfl

/-- Subdividing every old edge at the global marks and coning the consecutive intervals to the
old face centers gives a faithful finite intrinsic subdivision. -/
noncomputable def markedFanSubdivision : K.Subdivision where
  refined := M.markedFanLocallyFiniteTriangleComplex.compactIntrinsic
  homeo := M.markedFanHomeomorph
  affineOnFace := by
    intro s hs
    let L := M.markedFanLocallyFiniteTriangleComplex
    letI : Fintype L.Vertex :=
      M.markedFanLocallyFiniteTriangleComplex.compactIntrinsic.vertexFintype
    change s ∈ L.compactIntrinsic.faces at hs
    rw [L.compactIntrinsic_faces] at hs
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hs
    change M.FanFace at f
    refine ⟨M.fanBarycentricAffine, ?_⟩
    intro x hx
    have heval := L.compactEval_eq_faceMap f x hx
    have hhomeo :
        (M.markedFanHomeomorph x).1 =
          (L.compactEval x).1 :=
      congrArg Subtype.val
        (M.markedFanHomeomorph_apply x)
    rw [hhomeo, heval]
    change (M.globalFanFaceMap f
      (L.restrictToFace (M.globalFanFaceVertices f)
        ⟨x.1, x.2.1⟩ hx)).1 = M.fanBarycentricAffine x.1
    rw [M.globalFanFaceMap_val_eq_fanBarycentricAffine]
    apply congrArg M.fanBarycentricAffine
    funext v
    by_cases hv : v ∈ M.globalFanFaceVertices f
    · rw [extendFaceCoordinates_of_mem _ _ hv]
      rfl
    · rw [extendFaceCoordinates_of_notMem _ _ hv]
      exact (hx v hv).symm
  subordinate := by
    intro s hs
    let L := M.markedFanLocallyFiniteTriangleComplex
    letI : Fintype L.Vertex :=
      M.markedFanLocallyFiniteTriangleComplex.compactIntrinsic.vertexFintype
    change s ∈ L.compactIntrinsic.faces at hs
    rw [L.compactIntrinsic_faces] at hs
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hs
    change M.FanFace at f
    refine ⟨f.1.1, f.1.2, ?_⟩
    intro x hx
    have heval := L.compactEval_eq_faceMap f x hx
    have hhomeo :
        M.markedFanHomeomorph x =
          L.compactEval x :=
      M.markedFanHomeomorph_apply x
    rw [hhomeo, heval]
    change M.globalFanFaceMap f
      (L.restrictToFace (M.globalFanFaceVertices f)
        ⟨x.1, x.2.1⟩ hx) ∈ K.faceCarrier f.1.1
    exact M.globalFanFaceMap_mem_faceCarrier f _

end EdgeMarking

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
