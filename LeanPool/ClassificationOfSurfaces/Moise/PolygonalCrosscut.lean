/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalPolyhedron
import LeanPool.ClassificationOfSurfaces.Moise.FreeTriangle

/-!
# Polygonal crosscuts

The set-theoretic part of Moise Chapter 2, Theorems 7 and 8.  Three polygonal arcs with common
endpoints form three polygons.  When the third arc is a chord inside the first polygon, the two
polygons containing the chord lie inside the first polygon.  This is the cutting lemma used in
the free-triangle induction of Chapter 3.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PolygonalCircle

/-- Splitting a nondegenerate segment at a non-endpoint produces two subsegments meeting only
at the split point. -/
theorem segment_split_inter {a b p : Plane} (hp : p ∈ segment ℝ a b)
    (hpa : p ≠ a) (hpb : p ≠ b) :
    segment ℝ a p ∩ segment ℝ p b = {p} := by
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  have hab : a ≠ b := by
    intro hab
    subst b
    rw [AffineMap.lineMap_same_apply] at hpa
    exact hpa rfl
  have hc0 : 0 < c := by
    exact lt_of_le_of_ne hc.1 fun hc0 => hpa <| by
      rw [← hc0, AffineMap.lineMap_apply_zero]
  have hc1 : c < 1 := by
    exact lt_of_le_of_ne hc.2 fun hc1 => hpb <| by
      rw [hc1, AffineMap.lineMap_apply_one]
  apply Set.Subset.antisymm
  · rintro x ⟨hxLeft, hxRight⟩
    rw [segment_eq_image_lineMap] at hxLeft hxRight
    obtain ⟨d, hd, rfl⟩ := hxLeft
    obtain ⟨e, he, heq⟩ := hxRight
    rw [AffineMap.lineMap_lineMap_right, AffineMap.lineMap_lineMap_left] at heq
    have hparam : d * c = 1 - (1 - e) * (1 - c) :=
      (AffineMap.lineMap_eq_lineMap_iff.mp heq.symm).resolve_left hab
    have hle : d * c ≤ c := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd.2) hc.1]
    have hge : c ≤ 1 - (1 - e) * (1 - c) := by
      nlinarith [mul_nonneg he.1 (sub_nonneg.mpr hc.2)]
    have hdc : d * c = c := le_antisymm hle (hparam ▸ hge)
    rw [AffineMap.lineMap_lineMap_right, hdc]
    exact Set.mem_singleton _
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- Vertex sequence obtained by inserting `p` in edge zero.  Its cyclic order is
`p, v₁, ..., vₙ₋₁, v₀`. -/
def insertZeroVertex (J : PolygonalCircle) (p : Plane) : ZMod (J.n + 1) → Plane :=
  fun i => if i.val = 0 then p else J.vertex (i.val : ZMod J.n)

@[simp] theorem insertZeroVertex_zero (J : PolygonalCircle) (p : Plane) :
    J.insertZeroVertex p 0 = p := by
  simp [insertZeroVertex]

theorem insertZeroVertex_natCast (J : PolygonalCircle) (p : Plane) {m : ℕ}
    (hm0 : 0 < m) (hm : m < J.n + 1) :
    J.insertZeroVertex p (m : ZMod (J.n + 1)) = J.vertex (m : ZMod J.n) := by
  rw [insertZeroVertex, ZMod.val_natCast_of_lt hm]
  simp only [ite_eq_right hm0.ne']

/-- The prospective edges of `insertZero`, before packaging the simple-polygon proofs. -/
def insertZeroEdgeSegment (J : PolygonalCircle) (p : Plane)
    (i : ZMod (J.n + 1)) : Set Plane :=
  segment ℝ (J.insertZeroVertex p i) (J.insertZeroVertex p (i + 1))

theorem insertZeroEdgeSegment_zero (J : PolygonalCircle) (p : Plane) :
    J.insertZeroEdgeSegment p 0 = segment ℝ p (J.vertex 1) := by
  unfold insertZeroEdgeSegment
  rw [insertZeroVertex_zero]
  have htwo : 1 < J.n + 1 := by
    have := J.three_le
    omega
  rw [show (0 : ZMod (J.n + 1)) + 1 = 1 by simp]
  unfold insertZeroVertex
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt htwo]
  simp

theorem insertZeroEdgeSegment_middle (J : PolygonalCircle) (p : Plane) {m : ℕ}
    (hm0 : 0 < m) (hm : m < J.n) :
    J.insertZeroEdgeSegment p (m : ZMod (J.n + 1)) =
      J.edgeSegment (m : ZMod J.n) := by
  unfold insertZeroEdgeSegment edgeSegment
  rw [J.insertZeroVertex_natCast p hm0 (by omega)]
  have hm1 : m + 1 < J.n + 1 := by omega
  have hsucc : (m : ZMod (J.n + 1)) + 1 = (m + 1 : ℕ) := by
    norm_num [Nat.cast_add]
  rw [hsucc, J.insertZeroVertex_natCast p (by omega) hm1]
  congr 2
  norm_num [Nat.cast_add]

theorem insertZeroEdgeSegment_last (J : PolygonalCircle) (p : Plane) :
    J.insertZeroEdgeSegment p (J.n : ZMod (J.n + 1)) =
      segment ℝ (J.vertex 0) p := by
  unfold insertZeroEdgeSegment
  have hn : 0 < J.n := by
    have := J.three_le
    omega
  rw [J.insertZeroVertex_natCast p hn (by omega)]
  have hwrap : (J.n : ZMod (J.n + 1)) + 1 = 0 := by
    calc
      (J.n : ZMod (J.n + 1)) + 1 =
          ((J.n + 1 : ℕ) : ZMod (J.n + 1)) := by
            rw [Nat.cast_add, Nat.cast_one]
      _ = 0 := ZMod.natCast_self (J.n + 1)
  rw [hwrap, J.insertZeroVertex_zero]
  congr 2
  exact ZMod.natCast_self J.n

theorem insertZeroVertex_adjacent_ne (J : PolygonalCircle) {p : Plane}
    (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1)
    (i : ZMod (J.n + 1)) :
    J.insertZeroVertex p i ≠ J.insertZeroVertex p (i + 1) := by
  let m := i.val
  have hi : (m : ZMod (J.n + 1)) = i := ZMod.natCast_zmod_val i
  have hmle : m ≤ J.n := by
    have := i.val_lt
    omega
  rw [← hi]
  by_cases hm0 : m = 0
  · rw [hm0]
    change J.insertZeroVertex p (0 : ZMod (J.n + 1)) ≠
      J.insertZeroVertex p ((0 : ZMod (J.n + 1)) + 1)
    rw [J.insertZeroVertex_zero]
    have htwo : 1 < J.n + 1 := by
      have := J.three_le
      omega
    have hsucc : (0 : ZMod (J.n + 1)) + 1 = (1 : ZMod (J.n + 1)) := by simp
    rw [hsucc]
    unfold insertZeroVertex
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt htwo]
    simp only [ite_eq_right (by omega : (1 : ℕ) ≠ 0)]
    simpa only [Nat.cast_one] using hp1
  by_cases hmn : m = J.n
  · rw [hmn]
    have hn : 0 < J.n := by
      have := J.three_le
      omega
    rw [J.insertZeroVertex_natCast p hn (by omega)]
    have hwrap : (J.n : ZMod (J.n + 1)) + 1 = 0 := by
      calc
        (J.n : ZMod (J.n + 1)) + 1 =
            ((J.n + 1 : ℕ) : ZMod (J.n + 1)) := by
              rw [Nat.cast_add, Nat.cast_one]
        _ = 0 := ZMod.natCast_self (J.n + 1)
    rw [hwrap, J.insertZeroVertex_zero]
    intro h
    apply hp0
    calc
      p = J.vertex (J.n : ZMod J.n) := h.symm
      _ = J.vertex 0 := congrArg J.vertex (ZMod.natCast_self J.n)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hmlt : m < J.n := lt_of_le_of_ne hmle hmn
    rw [J.insertZeroVertex_natCast p hmpos (by omega)]
    have hsucc : (m : ZMod (J.n + 1)) + 1 = (m + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hsucc, J.insertZeroVertex_natCast p (by omega) (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one] using
      J.adjacent_ne (m : ZMod J.n)

theorem insertZero_consecutive_inter (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1)
    (i : ZMod (J.n + 1)) :
    J.insertZeroEdgeSegment p i ∩ J.insertZeroEdgeSegment p (i + 1) =
      {J.insertZeroVertex p (i + 1)} := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  let m := i.val
  have hi : (m : ZMod (J.n + 1)) = i := ZMod.natCast_zmod_val i
  have hmle : m ≤ J.n := by
    have := i.val_lt
    omega
  rw [← hi]
  by_cases hm0 : m = 0
  · rw [hm0]
    rw [Nat.cast_zero]
    simp only [zero_add]
    change J.insertZeroEdgeSegment p 0 ∩ J.insertZeroEdgeSegment p 1 =
      {J.insertZeroVertex p 1}
    rw [J.insertZeroEdgeSegment_zero]
    have hn : 1 < J.n := by
      have := J.three_le
      omega
    have hedge1 := J.insertZeroEdgeSegment_middle p (m := 1) (by omega) hn
    have hvertex1 := J.insertZeroVertex_natCast p (m := 1) (by omega) (by omega)
    have hedge1' : J.insertZeroEdgeSegment p (1 : ZMod (J.n + 1)) =
        J.edgeSegment (1 : ZMod J.n) := by
      simpa only [Nat.cast_one] using hedge1
    have hvertex1' : J.insertZeroVertex p (1 : ZMod (J.n + 1)) =
        J.vertex (1 : ZMod J.n) := by
      simpa only [Nat.cast_one] using hvertex1
    rw [hedge1', hvertex1']
    have hbase := J.consecutive_inter 0
    have hsub : segment ℝ p (J.vertex 1) ⊆
        segment ℝ (J.vertex 0) (J.vertex 1) :=
      (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset hp'
        (right_mem_segment ℝ _ _)
    unfold edgeSegment at hbase ⊢
    simp only [zero_add, one_add_one_eq_two] at hbase ⊢
    apply Set.Subset.antisymm
    · intro x hx
      exact hbase ▸ ⟨hsub hx.1, hx.2⟩
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  by_cases hmn : m = J.n
  · rw [hmn]
    have hwrap : (J.n : ZMod (J.n + 1)) + 1 = 0 := by
      calc
        (J.n : ZMod (J.n + 1)) + 1 =
            ((J.n + 1 : ℕ) : ZMod (J.n + 1)) := by
              rw [Nat.cast_add, Nat.cast_one]
        _ = 0 := ZMod.natCast_self (J.n + 1)
    rw [hwrap, J.insertZeroEdgeSegment_last, J.insertZeroEdgeSegment_zero,
      J.insertZeroVertex_zero]
    exact segment_split_inter hp' hp0 hp1
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hmlt : m < J.n := lt_of_le_of_ne hmle hmn
    by_cases hmlast : m + 1 = J.n
    · have hedgeM := J.insertZeroEdgeSegment_middle p hmpos hmlt
      have hedgeLast := J.insertZeroEdgeSegment_last p
      have hsucc : (m : ZMod (J.n + 1)) + 1 = (J.n : ZMod (J.n + 1)) := by
        calc
          (m : ZMod (J.n + 1)) + 1 = (m + 1 : ℕ) := by
            rw [Nat.cast_add, Nat.cast_one]
          _ = (J.n : ℕ) := by rw [hmlast]
      rw [hedgeM, hsucc, hedgeLast]
      have hvertex : J.insertZeroVertex p (J.n : ZMod (J.n + 1)) = J.vertex 0 := by
        rw [J.insertZeroVertex_natCast p (by omega) (by omega)]
        exact congrArg J.vertex (ZMod.natCast_self J.n)
      rw [hvertex]
      have hprev : (m : ZMod J.n) + 1 = 0 := by
        calc
          (m : ZMod J.n) + 1 = (m + 1 : ℕ) := by
            rw [Nat.cast_add, Nat.cast_one]
          _ = (J.n : ℕ) := by rw [hmlast]
          _ = 0 := ZMod.natCast_self J.n
      have hbase := J.consecutive_inter (m : ZMod J.n)
      have hprev2 : (m : ZMod J.n) + 2 = 1 := by
        calc
          (m : ZMod J.n) + 2 = ((m : ZMod J.n) + 1) + 1 := by
            rw [show (2 : ZMod J.n) = 1 + 1 by norm_num]
            abel
          _ = 0 + 1 := by rw [hprev]
          _ = 1 := zero_add 1
      unfold edgeSegment at hbase ⊢
      rw [hprev, hprev2] at hbase
      rw [hprev]
      have hsub : segment ℝ (J.vertex 0) p ⊆
          segment ℝ (J.vertex 0) (J.vertex 1) :=
        (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset
          (left_mem_segment ℝ _ _) hp'
      apply Set.Subset.antisymm
      · intro x hx
        exact hbase ▸ ⟨hx.1, hsub hx.2⟩
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
    · have hm1lt : m + 1 < J.n := by omega
      have hedgeM := J.insertZeroEdgeSegment_middle p hmpos hmlt
      have hedgeM1 := J.insertZeroEdgeSegment_middle p (m := m + 1) (by omega) hm1lt
      have hsucc : (m : ZMod (J.n + 1)) + 1 = (m + 1 : ℕ) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hedgeM, hsucc, hedgeM1]
      have hvertex := J.insertZeroVertex_natCast p (m := m + 1) (by omega) (by omega)
      rw [hvertex]
      simpa only [edgeSegment, Nat.cast_add, Nat.cast_one, add_assoc,
        one_add_one_eq_two] using
        J.consecutive_inter (m : ZMod J.n)

theorem vertex_zero_not_mem_insertZero_first (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    J.vertex 0 ∉ segment ℝ p (J.vertex 1) := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  intro hmem
  have hinter := segment_split_inter hp' hp0 hp1
  have hboth : J.vertex 0 ∈
      segment ℝ (J.vertex 0) p ∩ segment ℝ p (J.vertex 1) :=
    ⟨left_mem_segment ℝ _ _, hmem⟩
  rw [hinter, Set.mem_singleton_iff] at hboth
  exact hp0 hboth.symm

theorem vertex_one_not_mem_insertZero_last (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    J.vertex 1 ∉ segment ℝ (J.vertex 0) p := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  intro hmem
  have hinter := segment_split_inter hp' hp0 hp1
  have hboth : J.vertex 1 ∈
      segment ℝ (J.vertex 0) p ∩ segment ℝ p (J.vertex 1) :=
    ⟨hmem, right_mem_segment ℝ _ _⟩
  rw [hinter, Set.mem_singleton_iff] at hboth
  exact hp1 hboth.symm

theorem disjoint_insertZero_first_previous (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    Disjoint (segment ℝ p (J.vertex 1))
      (J.edgeSegment ((J.n - 1 : ℕ) : ZMod J.n)) := by
  have hn : 0 < J.n := by
    have := J.three_le
    omega
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  have hprev : ((J.n - 1 : ℕ) : ZMod J.n) + 1 = 0 := by
    calc
      ((J.n - 1 : ℕ) : ZMod J.n) + 1 = ((J.n - 1 + 1 : ℕ) : ZMod J.n) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = (J.n : ℕ) := congrArg (fun q : ℕ => (q : ZMod J.n))
        (Nat.sub_add_cancel (by omega))
      _ = 0 := ZMod.natCast_self J.n
  have hprev2 : ((J.n - 1 : ℕ) : ZMod J.n) + 2 = 1 := by
    calc
      ((J.n - 1 : ℕ) : ZMod J.n) + 2 =
          (((J.n - 1 : ℕ) : ZMod J.n) + 1) + 1 := by
            rw [show (2 : ZMod J.n) = 1 + 1 by norm_num]
            abel
      _ = 0 + 1 := by rw [hprev]
      _ = 1 := zero_add 1
  have hbase := J.consecutive_inter ((J.n - 1 : ℕ) : ZMod J.n)
  rw [hprev, hprev2] at hbase
  rw [Set.disjoint_left]
  intro x hxFirst hxPrev
  have hxEdge0 : x ∈ J.edgeSegment 0 := by
    simpa only [edgeSegment, zero_add] using
      (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset hp'
        (right_mem_segment ℝ _ _) hxFirst
  have hxBase : x ∈ J.edgeSegment ((J.n - 1 : ℕ) : ZMod J.n) ∩
      J.edgeSegment 0 := ⟨hxPrev, hxEdge0⟩
  unfold edgeSegment at hxBase
  rw [hprev] at hxBase
  have hxBase' : x = J.vertex 0 := by
    simpa only [zero_add, hbase, Set.mem_singleton_iff] using hxBase
  exact J.vertex_zero_not_mem_insertZero_first hp hp0 hp1 (hxBase' ▸ hxFirst)

theorem disjoint_insertZero_last_next (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    Disjoint (segment ℝ (J.vertex 0) p) (J.edgeSegment 1) := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  have hbase := J.consecutive_inter 0
  simp only [zero_add] at hbase
  rw [Set.disjoint_left]
  intro x hxLast hxNext
  have hxEdge0 : x ∈ J.edgeSegment 0 := by
    simpa only [edgeSegment, zero_add] using
      (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset
        (left_mem_segment ℝ _ _) hp' hxLast
  have hxBase : x ∈ J.edgeSegment 0 ∩ J.edgeSegment 1 := by
    exact ⟨hxEdge0, hxNext⟩
  unfold edgeSegment at hxBase
  simp only [zero_add, one_add_one_eq_two, hbase, Set.mem_singleton_iff] at hxBase
  exact J.vertex_one_not_mem_insertZero_last hp hp0 hp1 (hxBase ▸ hxLast)

private theorem natCast_eq_natCast_of_lt {n m l : ℕ}
    (hm : m < n) (hl : l < n) (h : (m : ZMod n) = (l : ZMod n)) : m = l := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hl] at hv

private theorem natCast_eq_succ_of_pos_lt {n m l : ℕ} [NeZero n] [Fact (1 < n)]
    (hm0 : 0 < m) (hm : m < n) (hl : l < n)
    (h : (m : ZMod n) = (l : ZMod n) + 1) : m = l + 1 := by
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hm, ZMod.val_add,
    ZMod.val_natCast_of_lt hl, ZMod.val_one] at hv
  by_cases hln : l + 1 < n
  · rwa [Nat.mod_eq_of_lt hln] at hv
  · have hle : n ≤ l + 1 := Nat.le_of_not_gt hln
    have heq : l + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

theorem insertZero_first_subset_edge_zero (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) :
    segment ℝ p (J.vertex 1) ⊆ J.edgeSegment 0 := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  intro x hx
  simpa only [edgeSegment, zero_add] using
    (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset hp'
      (right_mem_segment ℝ _ _) hx

theorem insertZero_last_subset_edge_zero (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) :
    segment ℝ (J.vertex 0) p ⊆ J.edgeSegment 0 := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  intro x hx
  simpa only [edgeSegment, zero_add] using
    (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset
      (left_mem_segment ℝ _ _) hp' hx

/-- Splitting edge zero preserves disjointness of every pair of non-adjacent edges. -/
theorem insertZero_nonadjacent_disjoint (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1)
    (i j : ZMod (J.n + 1)) (hij : i ≠ j) (hprev : i ≠ j + 1)
    (hnext : j ≠ i + 1) :
    J.insertZeroEdgeSegment p i ∩ J.insertZeroEdgeSegment p j = ∅ := by
  let : Fact (1 < J.n) := ⟨by have := J.three_le; omega⟩
  let m := i.val
  let l := j.val
  have hm : m < J.n + 1 := i.val_lt
  have hl : l < J.n + 1 := j.val_lt
  have hi : (m : ZMod (J.n + 1)) = i := ZMod.natCast_zmod_val i
  have hj : (l : ZMod (J.n + 1)) = j := ZMod.natCast_zmod_val j
  rw [← hi, ← hj] at hij hprev hnext ⊢
  have hmle : m ≤ J.n := by omega
  have hlle : l ≤ J.n := by omega
  have hwrap : (J.n : ZMod (J.n + 1)) + 1 = 0 := by
    calc
      (J.n : ZMod (J.n + 1)) + 1 = ((J.n + 1 : ℕ) : ZMod (J.n + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = 0 := ZMod.natCast_self (J.n + 1)
  by_cases hm0 : m = 0
  · rw [hm0] at hij hprev hnext ⊢
    simp only [Nat.cast_zero] at hij hprev hnext ⊢
    by_cases hl0 : l = 0
    · rw [hl0] at hij hprev hnext ⊢
      simp only [Nat.cast_zero] at hij hprev hnext ⊢
      exact (hij rfl).elim
    by_cases hln : l = J.n
    · rw [hln] at hij hprev hnext ⊢
      exact (hprev hwrap.symm).elim
    have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
    have hllt : l < J.n := lt_of_le_of_ne hlle hln
    rw [J.insertZeroEdgeSegment_zero,
      J.insertZeroEdgeSegment_middle p hlpos hllt]
    by_cases hl1 : l = 1
    · rw [hl1] at hnext ⊢
      exact (hnext (by norm_num)).elim
    by_cases hllast : l = J.n - 1
    · rw [hllast]
      exact Set.disjoint_iff_inter_eq_empty.mp
        (J.disjoint_insertZero_first_previous hp hp0 hp1)
    have hOld : J.edgeSegment 0 ∩ J.edgeSegment (l : ZMod J.n) = ∅ := by
      apply J.nonadjacent_disjoint
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_natCast_of_lt hllt] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_add, ZMod.val_natCast_of_lt hllt,
          ZMod.val_one] at hv
        have hsum : l + 1 < J.n := by omega
        rw [Nat.mod_eq_of_lt hsum] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hllt, ZMod.val_add, ZMod.val_zero,
          ZMod.val_one, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
        exact hl1 hv
    rw [Set.eq_empty_iff_forall_notMem]; rintro x ⟨hxFirst, hxOld⟩
    exact Set.eq_empty_iff_forall_notMem.mp hOld x
      ⟨J.insertZero_first_subset_edge_zero hp hxFirst, hxOld⟩
  by_cases hmn : m = J.n
  · rw [hmn] at hij hprev hnext ⊢
    by_cases hl0 : l = 0
    · rw [hl0] at hij hprev hnext ⊢
      simp only [Nat.cast_zero] at hij hprev hnext ⊢
      exact (hnext hwrap.symm).elim
    by_cases hln : l = J.n
    · rw [hln] at hij hprev hnext ⊢
      exact (hij rfl).elim
    have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
    have hllt : l < J.n := lt_of_le_of_ne hlle hln
    rw [J.insertZeroEdgeSegment_last,
      J.insertZeroEdgeSegment_middle p hlpos hllt]
    by_cases hl1 : l = 1
    · rw [hl1]
      rw [Set.inter_comm]
      simpa only [Nat.cast_one] using Set.disjoint_iff_inter_eq_empty.mp
        (J.disjoint_insertZero_last_next hp hp0 hp1).symm
    by_cases hllast : l = J.n - 1
    · have hcast : (l : ZMod (J.n + 1)) + 1 =
          (J.n : ZMod (J.n + 1)) := by
        rw [hllast]
        calc
          ((J.n - 1 : ℕ) : ZMod (J.n + 1)) + 1 =
              ((J.n - 1 + 1 : ℕ) : ZMod (J.n + 1)) := by
                rw [Nat.cast_add, Nat.cast_one]
          _ = (J.n : ℕ) := congrArg (fun q : ℕ => (q : ZMod (J.n + 1)))
            (Nat.sub_add_cancel (by have := J.three_le; omega))
      exact (hprev hcast.symm).elim
    have hOld : J.edgeSegment 0 ∩ J.edgeSegment (l : ZMod J.n) = ∅ := by
      apply J.nonadjacent_disjoint
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_natCast_of_lt hllt] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_add, ZMod.val_natCast_of_lt hllt,
          ZMod.val_one] at hv
        have hsum : l + 1 < J.n := by omega
        rw [Nat.mod_eq_of_lt hsum] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hllt, ZMod.val_add, ZMod.val_zero,
          ZMod.val_one, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
        exact hl1 hv
    rw [Set.eq_empty_iff_forall_notMem]; rintro x ⟨hxLast, hxOld⟩
    exact Set.eq_empty_iff_forall_notMem.mp hOld x
      ⟨J.insertZero_last_subset_edge_zero hp hxLast, hxOld⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hmlt : m < J.n := lt_of_le_of_ne hmle hmn
  rw [J.insertZeroEdgeSegment_middle p hmpos hmlt]
  by_cases hl0 : l = 0
  · rw [hl0] at hij hprev hnext ⊢
    simp only [Nat.cast_zero] at hij hprev hnext ⊢
    rw [J.insertZeroEdgeSegment_zero]
    by_cases hm1 : m = 1
    · rw [hm1] at hprev
      exact (hprev (by norm_num)).elim
    by_cases hmlast : m = J.n - 1
    · rw [hmlast]
      rw [Set.inter_comm]
      exact Set.disjoint_iff_inter_eq_empty.mp
        (J.disjoint_insertZero_first_previous hp hp0 hp1)
    have hOld : J.edgeSegment (m : ZMod J.n) ∩ J.edgeSegment 0 = ∅ := by
      apply J.nonadjacent_disjoint
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hmlt, ZMod.val_zero] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hmlt, ZMod.val_add, ZMod.val_zero,
          ZMod.val_one, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
        exact hm1 hv
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_add, ZMod.val_natCast_of_lt hmlt,
          ZMod.val_one] at hv
        have hsum : m + 1 < J.n := by omega
        rw [Nat.mod_eq_of_lt hsum] at hv
        omega
    rw [Set.eq_empty_iff_forall_notMem]; rintro x ⟨hxOld, hxFirst⟩
    exact Set.eq_empty_iff_forall_notMem.mp hOld x
      ⟨hxOld, J.insertZero_first_subset_edge_zero hp hxFirst⟩
  by_cases hln : l = J.n
  · rw [hln] at hij hprev hnext ⊢
    rw [J.insertZeroEdgeSegment_last]
    by_cases hm1 : m = 1
    · rw [hm1]
      simpa only [Nat.cast_one] using Set.disjoint_iff_inter_eq_empty.mp
        (J.disjoint_insertZero_last_next hp hp0 hp1).symm
    by_cases hmlast : m = J.n - 1
    · have hcast : (m : ZMod (J.n + 1)) + 1 =
          (J.n : ZMod (J.n + 1)) := by
        rw [hmlast]
        calc
          ((J.n - 1 : ℕ) : ZMod (J.n + 1)) + 1 =
              ((J.n - 1 + 1 : ℕ) : ZMod (J.n + 1)) := by
                rw [Nat.cast_add, Nat.cast_one]
          _ = (J.n : ℕ) := congrArg (fun q : ℕ => (q : ZMod (J.n + 1)))
            (Nat.sub_add_cancel (by have := J.three_le; omega))
      exact (hnext hcast.symm).elim
    have hOld : J.edgeSegment (m : ZMod J.n) ∩ J.edgeSegment 0 = ∅ := by
      apply J.nonadjacent_disjoint
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hmlt, ZMod.val_zero] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hmlt, ZMod.val_add, ZMod.val_zero,
          ZMod.val_one, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
        exact hm1 hv
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_add, ZMod.val_natCast_of_lt hmlt,
          ZMod.val_one] at hv
        have hsum : m + 1 < J.n := by omega
        rw [Nat.mod_eq_of_lt hsum] at hv
        omega
    rw [Set.eq_empty_iff_forall_notMem]; rintro x ⟨hxOld, hxLast⟩
    exact Set.eq_empty_iff_forall_notMem.mp hOld x
      ⟨hxOld, J.insertZero_last_subset_edge_zero hp hxLast⟩
  have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
  have hllt : l < J.n := lt_of_le_of_ne hlle hln
  rw [J.insertZeroEdgeSegment_middle p hlpos hllt]
  apply J.nonadjacent_disjoint
  · intro h
    have hml := natCast_eq_natCast_of_lt hmlt hllt h
    apply hij
    rw [hml]
  · intro h
    have hml := natCast_eq_succ_of_pos_lt hmpos hmlt hllt h
    apply hprev
    rw [hml, Nat.cast_add, Nat.cast_one]
  · intro h
    have hlm := natCast_eq_succ_of_pos_lt hlpos hllt hmlt h
    apply hnext
    rw [hlm, Nat.cast_add, Nat.cast_one]

/-- A point on a segment splits it into two subsegments whose union is the original segment. -/
theorem segment_split_union {a b p : Plane} (hp : p ∈ segment ℝ a b) :
    segment ℝ a p ∪ segment ℝ p b = segment ℝ a b := by
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · exact (convex_segment a b).segment_subset (left_mem_segment ℝ _ _) hp hx
    · exact (convex_segment a b).segment_subset hp (right_mem_segment ℝ _ _) hx
  · intro x hx
    rw [← insert_endpoints_openSegment] at hx
    rcases hx with rfl | rfl | hx
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (right_mem_segment ℝ _ _)
    · have hpRange : p ∈ Set.range (AffineMap.lineMap a b : ℝ → Plane) := by
        rw [segment_eq_image_lineMap] at hp
        obtain ⟨c, -, hc⟩ := hp
        exact ⟨c, hc⟩
      rcases openSegment_subset_union a b hpRange hx with rfl | hx | hx
      · exact Or.inl (right_mem_segment ℝ _ _)
      · exact Or.inl (openSegment_subset_segment ℝ _ _ hx)
      · exact Or.inr (openSegment_subset_segment ℝ _ _ hx)

/-- Subdivide edge zero at a non-endpoint.  The cyclic order is
`p, v₁, ..., vₙ₋₁, v₀`. -/
def insertZero (J : PolygonalCircle) (p : Plane) (hp : p ∈ J.edgeSegment 0)
    (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) : PolygonalCircle where
  n := J.n + 1
  three_le := by have := J.three_le; omega
  vertex := J.insertZeroVertex p
  adjacent_ne := J.insertZeroVertex_adjacent_ne hp0 hp1
  consecutive_inter := by
    intro i
    simpa only [insertZeroEdgeSegment, add_assoc, one_add_one_eq_two] using
      J.insertZero_consecutive_inter hp hp0 hp1 i
  nonadjacent_disjoint := by
    intro i j hij hprev hnext
    simpa only [insertZeroEdgeSegment] using
      J.insertZero_nonadjacent_disjoint hp hp0 hp1 i j hij hprev hnext

@[simp] theorem insertZero_n (J : PolygonalCircle) (p : Plane)
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    (J.insertZero p hp hp0 hp1).n = J.n + 1 := rfl

@[simp] theorem insertZero_vertex_zero (J : PolygonalCircle) (p : Plane)
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    (J.insertZero p hp hp0 hp1).vertex 0 = p := by
  exact J.insertZeroVertex_zero p

/-- Inserting a vertex into an edge does not change the polygon carrier. -/
theorem insertZero_carrier (J : PolygonalCircle) (p : Plane) (hp : p ∈ J.edgeSegment 0)
    (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    (J.insertZero p hp hp0 hp1).carrier = J.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    unfold carrier at hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    let m := i.val
    have hm : m < J.n + 1 := i.val_lt
    have hcast : (m : ZMod (J.n + 1)) = i := ZMod.natCast_zmod_val i
    rw [← hcast] at hi
    change x ∈ J.insertZeroEdgeSegment p (m : ZMod (J.n + 1)) at hi
    by_cases hm0 : m = 0
    · rw [hm0, Nat.cast_zero, J.insertZeroEdgeSegment_zero] at hi
      exact J.edgeSegment_subset_carrier 0 (J.insertZero_first_subset_edge_zero hp hi)
    by_cases hmn : m = J.n
    · rw [hmn, J.insertZeroEdgeSegment_last] at hi
      exact J.edgeSegment_subset_carrier 0 (J.insertZero_last_subset_edge_zero hp hi)
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hmlt : m < J.n := by omega
    rw [J.insertZeroEdgeSegment_middle p hmpos hmlt] at hi
    exact J.edgeSegment_subset_carrier (m : ZMod J.n) hi
  · intro x hx
    unfold carrier at hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    by_cases hi0 : i = 0
    · subst i
      have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
        simpa only [edgeSegment, zero_add] using hp
      have hsplit := segment_split_union hp'
      have hi' : x ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
        simpa only [edgeSegment, zero_add] using hi
      rw [← hsplit] at hi'
      rcases hi' with hi' | hi'
      · apply (J.insertZero p hp hp0 hp1).edgeSegment_subset_carrier
          (J.n : ZMod (J.n + 1))
        change x ∈ J.insertZeroEdgeSegment p (J.n : ZMod (J.n + 1))
        rwa [J.insertZeroEdgeSegment_last]
      · apply (J.insertZero p hp hp0 hp1).edgeSegment_subset_carrier 0
        change x ∈ J.insertZeroEdgeSegment p 0
        rwa [J.insertZeroEdgeSegment_zero]
    · let m := i.val
      have hmpos : 0 < m := Nat.pos_of_ne_zero fun hm0 =>
        hi0 ((ZMod.val_eq_zero i).mp hm0)
      have hmlt : m < J.n := i.val_lt
      apply (J.insertZero p hp hp0 hp1).edgeSegment_subset_carrier
        (m : ZMod (J.n + 1))
      change x ∈ J.insertZeroEdgeSegment p (m : ZMod (J.n + 1))
      rw [J.insertZeroEdgeSegment_middle p hmpos hmlt]
      rwa [ZMod.natCast_zmod_val i]

/-- Cyclically reindex a polygon so that the old index `a` becomes the new index zero. -/
def rotate (J : PolygonalCircle) (a : ZMod J.n) : PolygonalCircle where
  n := J.n
  three_le := J.three_le
  vertex i := J.vertex (i + a)
  adjacent_ne i := by
    convert J.adjacent_ne (i + a) using 1; ring
  consecutive_inter i := by
    convert J.consecutive_inter (i + a) using 1 <;> ring
  nonadjacent_disjoint i j hij hprev hnext := by
    have h := J.nonadjacent_disjoint (i + a) (j + a)
      (fun h => hij (add_right_cancel h))
      (fun h => hprev (add_right_cancel (by calc
        i + a = j + a + 1 := h
        _ = (j + 1) + a := by ring)))
      (fun h => hnext (add_right_cancel (by calc
        j + a = i + a + 1 := h
        _ = (i + 1) + a := by ring)))
    convert h using 1; ring

@[simp] theorem rotate_n (J : PolygonalCircle) (a : ZMod J.n) :
    (J.rotate a).n = J.n := rfl

@[simp] theorem rotate_vertex (J : PolygonalCircle) (a i : ZMod J.n) :
    (J.rotate a).vertex i = J.vertex (i + a) := rfl

theorem rotate_edgeSegment (J : PolygonalCircle) (a i : ZMod J.n) :
    (J.rotate a).edgeSegment i = J.edgeSegment (i + a) := by
  change segment ℝ (J.vertex (i + a)) (J.vertex ((i + 1) + a)) =
    segment ℝ (J.vertex (i + a)) (J.vertex (i + a + 1))
  congr 2
  exact add_right_comm i (1 : ZMod J.n) a

theorem rotate_carrier (J : PolygonalCircle) (a : ZMod J.n) :
    (J.rotate a).carrier = J.carrier := by
  apply Set.Subset.antisymm
  · intro p hp
    unfold carrier rotate edgeSegment at hp
    rw [Set.mem_iUnion] at hp
    obtain ⟨i, hi⟩ := hp
    apply J.edgeSegment_subset_carrier (i + a)
    change p ∈ segment ℝ (J.vertex (i + a)) (J.vertex (i + a + 1))
    convert hi using 1; ring
  · intro p hp
    unfold carrier at hp
    rw [Set.mem_iUnion] at hp
    obtain ⟨i, hi⟩ := hp
    change p ∈ segment ℝ (J.vertex i) (J.vertex (i + 1)) at hi
    unfold carrier rotate edgeSegment
    rw [Set.mem_iUnion]
    refine ⟨i - a, ?_⟩
    convert hi using 1; ring

/-- The bounded and unbounded complementary components depend only on the polygon carrier, not
on its cyclic indexing. -/
theorem regions_eq_of_carrier_eq {J J' : PolygonalCircle}
    (hcarrier : J.carrier = J'.carrier) :
    J.interiorRegion = J'.interiorRegion ∧ J.exteriorRegion = J'.exteriorRegion := by
  have hsplitJ' : J'.exteriorRegion ⊆ J.interiorRegion ∪ J.exteriorRegion := by
    intro p hp
    have hpCompl : p ∈ J'.carrierᶜ := by
      rw [← J'.interior_union_exterior]
      exact Or.inr hp
    have hpCompl' : p ∈ J.carrierᶜ := by rwa [hcarrier]
    rwa [← J.interior_union_exterior] at hpCompl'
  have hmeetExterior : (J'.exteriorRegion ∩ J.exteriorRegion).Nonempty := by
    by_contra h
    have hsubsetInterior : J'.exteriorRegion ⊆ J.interiorRegion := by
      intro p hp
      rcases hsplitJ' hp with hpInt | hpExt
      · exact hpInt
      · exact False.elim <| h ⟨p, hp, hpExt⟩
    exact J'.not_isBounded_exteriorRegion
      (J.isBounded_interiorRegion.subset hsubsetInterior)
  have hExteriorSub : J'.exteriorRegion ⊆ J.exteriorRegion :=
    J'.isConnected_exteriorRegion.isPreconnected.subset_right_of_subset_union
      J.isOpen_interiorRegion J.isOpen_exteriorRegion J.disjoint_interior_exterior
      hsplitJ' hmeetExterior
  have hsplitJ : J.exteriorRegion ⊆ J'.interiorRegion ∪ J'.exteriorRegion := by
    intro p hp
    have hpCompl : p ∈ J.carrierᶜ := by
      rw [← J.interior_union_exterior]
      exact Or.inr hp
    have hpCompl' : p ∈ J'.carrierᶜ := by rwa [← hcarrier]
    rwa [← J'.interior_union_exterior] at hpCompl'
  have hmeetExterior' : (J.exteriorRegion ∩ J'.exteriorRegion).Nonempty := by
    obtain ⟨p, hpJ', hpJ⟩ := hmeetExterior
    exact ⟨p, hpJ, hpJ'⟩
  have hExteriorSub' : J.exteriorRegion ⊆ J'.exteriorRegion :=
    J.isConnected_exteriorRegion.isPreconnected.subset_right_of_subset_union
      J'.isOpen_interiorRegion J'.isOpen_exteriorRegion J'.disjoint_interior_exterior
      hsplitJ hmeetExterior'
  have hExterior : J.exteriorRegion = J'.exteriorRegion :=
    Set.Subset.antisymm hExteriorSub' hExteriorSub
  refine ⟨?_, hExterior⟩
  have hcomplements : J.interiorRegion ∪ J.exteriorRegion =
      J'.interiorRegion ∪ J'.exteriorRegion := by
    rw [J.interior_union_exterior, J'.interior_union_exterior, hcarrier]
  apply Set.Subset.antisymm
  · intro p hp
    have hpUnion : p ∈ J'.interiorRegion ∪ J'.exteriorRegion := by
      rw [← hcomplements]
      exact Or.inl hp
    rcases hpUnion with hpInt | hpExt
    · exact hpInt
    · exact False.elim <| Set.disjoint_left.mp J.disjoint_interior_exterior
        hp (hExterior ▸ hpExt)
  · intro p hp
    have hpUnion : p ∈ J.interiorRegion ∪ J.exteriorRegion := by
      rw [hcomplements]
      exact Or.inl hp
    rcases hpUnion with hpInt | hpExt
    · exact hpInt
    · exact False.elim <| Set.disjoint_left.mp J'.disjoint_interior_exterior
        hp (hExterior ▸ hpExt)

theorem rotate_interiorRegion (J : PolygonalCircle) (a : ZMod J.n) :
    (J.rotate a).interiorRegion = J.interiorRegion :=
  (regions_eq_of_carrier_eq (J.rotate_carrier a)).1

theorem rotate_exteriorRegion (J : PolygonalCircle) (a : ZMod J.n) :
    (J.rotate a).exteriorRegion = J.exteriorRegion :=
  (regions_eq_of_carrier_eq (J.rotate_carrier a)).2

theorem insertZero_interiorRegion (J : PolygonalCircle) (p : Plane)
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    (J.insertZero p hp hp0 hp1).interiorRegion = J.interiorRegion :=
  (regions_eq_of_carrier_eq (J.insertZero_carrier p hp hp0 hp1)).1

theorem insertZero_exteriorRegion (J : PolygonalCircle) (p : Plane)
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    (J.insertZero p hp hp0 hp1).exteriorRegion = J.exteriorRegion :=
  (regions_eq_of_carrier_eq (J.insertZero_carrier p hp hp0 hp1)).2

/-- A point is a vertex of one of the cyclic presentations of a polygon. -/
def IsVertexPoint (J : PolygonalCircle) (p : Plane) : Prop :=
  ∃ i, J.vertex i = p

/-- A point known to be a polygon vertex lies on an edge exactly when it is one of that edge's
two endpoints. -/
theorem IsVertexPoint.mem_edgeSegment_iff {J : PolygonalCircle} {p : Plane}
    (hp : J.IsVertexPoint p) (i : ZMod J.n) :
    p ∈ J.edgeSegment i ↔ p = J.vertex i ∨ p = J.vertex (i + 1) := by
  obtain ⟨j, rfl⟩ := hp
  rw [J.vertex_mem_edgeSegment_iff j i]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl (J.vertex_injective h)
    · exact Or.inr (J.vertex_injective h)

theorem isVertexPoint_rotate_iff (J : PolygonalCircle) (a : ZMod J.n) (p : Plane) :
    (J.rotate a).IsVertexPoint p ↔ J.IsVertexPoint p := by
  change (∃ i : ZMod J.n, J.vertex (i + a) = p) ↔
    ∃ i : ZMod J.n, J.vertex i = p
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i + a, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i - a, ?_⟩
    simpa only [rotate_vertex, sub_add_cancel] using hi

theorem isVertexPoint_insertZero (J : PolygonalCircle) (p : Plane)
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1)
    {q : Plane} (hq : J.IsVertexPoint q) :
    (J.insertZero p hp hp0 hp1).IsVertexPoint q := by
  obtain ⟨i, rfl⟩ := hq
  by_cases hi0 : i = 0
  · subst i
    refine ⟨(J.n : ZMod (J.n + 1)), ?_⟩
    change J.insertZeroVertex p (J.n : ZMod (J.n + 1)) = J.vertex 0
    rw [J.insertZeroVertex_natCast p (by have := J.three_le; omega) (by omega)]
    exact congrArg J.vertex (ZMod.natCast_self J.n)
  · let m := i.val
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun hm =>
      hi0 ((ZMod.val_eq_zero i).mp hm)
    have hmlt : m < J.n := i.val_lt
    refine ⟨(m : ZMod (J.n + 1)), ?_⟩
    change J.insertZeroVertex p (m : ZMod (J.n + 1)) = J.vertex i
    rw [J.insertZeroVertex_natCast p hm0 (by omega), ZMod.natCast_zmod_val i]

/-- Insert a boundary point as vertex zero without changing the carrier, while retaining every
old vertex.  Endpoint cases need only a cyclic reindexing; an interior edge point uses
`insertZero`. -/
theorem exists_refinement_vertex_zero (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.carrier) :
    ∃ J' : PolygonalCircle,
      J'.carrier = J.carrier ∧ J'.vertex 0 = p ∧
        ∀ q, J.IsVertexPoint q → J'.IsVertexPoint q := by
  simp only [carrier, Set.mem_iUnion] at hp
  obtain ⟨i, hi⟩ := hp
  let R := J.rotate i
  have hiR : p ∈ R.edgeSegment 0 := by
    change p ∈ (J.rotate i).edgeSegment (0 : ZMod J.n)
    rw [J.rotate_edgeSegment]
    simpa only [zero_add] using hi
  by_cases hp0 : p = R.vertex 0
  · refine ⟨R, J.rotate_carrier i, hp0.symm, ?_⟩
    intro q hq
    exact (J.isVertexPoint_rotate_iff i q).mpr hq
  by_cases hp1 : p = R.vertex 1
  · let R' := R.rotate 1
    refine ⟨R', ?_, ?_, ?_⟩
    · exact (R.rotate_carrier 1).trans (J.rotate_carrier i)
    · dsimp [R']
      change R.vertex ((0 : ZMod R.n) + 1) = p
      rw [zero_add]
      exact hp1.symm
    · intro q hq
      exact (R.isVertexPoint_rotate_iff 1 q).mpr
        ((J.isVertexPoint_rotate_iff i q).mpr hq)
  · let J' := R.insertZero p hiR hp0 hp1
    refine ⟨J', (R.insertZero_carrier p hiR hp0 hp1).trans (J.rotate_carrier i), ?_, ?_⟩
    · exact R.insertZero_vertex_zero p hiR hp0 hp1
    · intro q hq
      exact R.isVertexPoint_insertZero p hiR hp0 hp1
        ((J.isVertexPoint_rotate_iff i q).mpr hq)

/-- Refine a polygonal presentation so that every point of a prescribed finite subset of its
carrier is a polygon vertex, without changing the carrier. -/
theorem exists_refinement_vertices (J : PolygonalCircle) (F : Finset Plane)
    (hF : ∀ p ∈ F, p ∈ J.carrier) :
    ∃ J' : PolygonalCircle, J'.carrier = J.carrier ∧
      ∀ p ∈ F, J'.IsVertexPoint p := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      exact ⟨J, rfl, by simp⟩
  | @insert p F hpF ih =>
      obtain ⟨K, hKcarrier, hKF⟩ := ih (fun q hq => hF q (Finset.mem_insert_of_mem hq))
      have hpK : p ∈ K.carrier := by
        rw [hKcarrier]
        exact hF p (Finset.mem_insert_self p F)
      obtain ⟨K', hK'carrier, hK'p, hkeep⟩ := K.exists_refinement_vertex_zero hpK
      refine ⟨K', hK'carrier.trans hKcarrier, ?_⟩
      intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · exact ⟨0, hK'p⟩
      · exact hkeep q (hKF q hq)

/-- A straight crosscut of a polygonal disk: its endpoints lie on the polygon, while every
other point of the segment lies in the polygon interior. -/
structure ProperChord (J : PolygonalCircle) where
  /-- The `P` declaration. -/
  P : Plane
  /-- The `Q` declaration. -/
  Q : Plane
  ne : P ≠ Q
  P_mem : P ∈ J.carrier
  Q_mem : Q ∈ J.carrier
  interior_subset : segment ℝ P Q \ {P, Q} ⊆ J.interiorRegion

namespace ProperChord

variable {J : PolygonalCircle} (C : J.ProperChord)

/-- Transport a proper chord across a different cyclic polygon presentation with the same
carrier. -/
def congrCarrier {J' : PolygonalCircle} (hcarrier : J'.carrier = J.carrier) :
    J'.ProperChord where
  P := C.P
  Q := C.Q
  ne := C.ne
  P_mem := by rw [hcarrier]; exact C.P_mem
  Q_mem := by rw [hcarrier]; exact C.Q_mem
  interior_subset := by
    rw [(regions_eq_of_carrier_eq hcarrier).1]
    exact C.interior_subset

/-- Reindexing the boundary polygon does not change a proper chord. -/
def rotate (a : ZMod J.n) : (J.rotate a).ProperChord where
  P := C.P
  Q := C.Q
  ne := C.ne
  P_mem := by rw [J.rotate_carrier]; exact C.P_mem
  Q_mem := by rw [J.rotate_carrier]; exact C.Q_mem
  interior_subset := by
    rw [J.rotate_interiorRegion]
    exact C.interior_subset

/-- The chord meets the original polygon precisely at its endpoints. -/
theorem segment_inter_carrier :
    segment ℝ C.P C.Q ∩ J.carrier = {C.P, C.Q} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSegment, hxCarrier⟩
    by_contra hxEndpoints
    have hxInterior := C.interior_subset ⟨hxSegment, hxEndpoints⟩
    have hxCompl : x ∈ J.carrierᶜ := by
      rw [← J.interior_union_exterior]
      exact Or.inl hxInterior
    exact hxCompl hxCarrier
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨left_mem_segment ℝ _ _, C.P_mem⟩
    · exact ⟨right_mem_segment ℝ _ _, C.Q_mem⟩

theorem interior_nonempty :
    (segment ℝ C.P C.Q \ {C.P, C.Q}).Nonempty := by
  refine ⟨midpoint ℝ C.P C.Q, midpoint_mem_segment C.P C.Q, ?_⟩
  intro h
  rcases h with h | h
  · exact C.ne ((midpoint_eq_left_iff (R := ℝ)).mp h)
  · exact C.ne ((midpoint_eq_right_iff (R := ℝ)).mp h)

/-- Each endpoint of a proper chord lies on a concrete polygon edge. -/
theorem exists_endpoint_edges :
    ∃ i j : ZMod J.n, C.P ∈ J.edgeSegment i ∧ C.Q ∈ J.edgeSegment j := by
  have hP := C.P_mem
  have hQ := C.Q_mem
  unfold PolygonalCircle.carrier at hP hQ
  simp only [Set.mem_iUnion] at hP hQ
  obtain ⟨i, hi⟩ := hP
  obtain ⟨j, hj⟩ := hQ
  exact ⟨i, j, hi, hj⟩

/-- The endpoints of a proper chord cannot lie on one polygon edge. -/
theorem endpoint_edges_ne {i j : ZMod J.n} (hi : C.P ∈ J.edgeSegment i)
    (hj : C.Q ∈ J.edgeSegment j) : i ≠ j := by
  intro hij
  subst j
  let m := midpoint ℝ C.P C.Q
  have hmSegment : m ∈ segment ℝ C.P C.Q := midpoint_mem_segment C.P C.Q
  have hmEndpoints : m ∉ ({C.P, C.Q} : Set Plane) := by
    intro hm
    rcases hm with hm | hm
    · exact C.ne ((midpoint_eq_left_iff (R := ℝ)).mp hm)
    · exact C.ne ((midpoint_eq_right_iff (R := ℝ)).mp hm)
  have hmInterior : m ∈ J.interiorRegion :=
    C.interior_subset ⟨hmSegment, hmEndpoints⟩
  have hmEdge : m ∈ J.edgeSegment i := by
    exact (convex_segment (𝕜 := ℝ) (J.vertex i) (J.vertex (i + 1))).segment_subset
      hi hj hmSegment
  have hmCarrier : m ∈ J.carrier := J.edgeSegment_subset_carrier i hmEdge
  have hmCompl : m ∈ J.carrierᶜ := by
    rw [← J.interior_union_exterior]
    exact Or.inl hmInterior
  exact hmCompl hmCarrier

/-- Normalize a proper chord so that its first endpoint lies on edge zero and its second
endpoint lies on an edge with a positive ordinary index. -/
theorem exists_rotated_endpoint_edges :
    ∃ a : ZMod J.n, ∃ k : ℕ, 0 < k ∧ k < J.n ∧
      C.P ∈ (J.rotate a).edgeSegment 0 ∧
      C.Q ∈ (J.rotate a).edgeSegment (k : ZMod J.n) := by
  obtain ⟨i, j, hi, hj⟩ := C.exists_endpoint_edges
  let d : ZMod J.n := j - i
  have hd : d ≠ 0 := by
    intro hd
    apply C.endpoint_edges_ne hi hj
    have : j = i := sub_eq_zero.mp hd
    exact this.symm
  refine ⟨i, d.val, ?_, d.val_lt, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero fun h => hd (d.val_eq_zero.mp h)
  · change C.P ∈ (J.rotate i).edgeSegment (0 : ZMod J.n)
    rw [show (J.rotate i).edgeSegment (0 : ZMod J.n) =
      J.edgeSegment (0 + i) from J.rotate_edgeSegment i 0]
    simpa using hi
  · rw [J.rotate_edgeSegment]
    have hcast : (d.val : ZMod J.n) = d := ZMod.natCast_zmod_val d
    rw [hcast]
    simpa [d] using hj

/-- After subdividing boundary edges and cyclically reindexing, both chord endpoints are
vertices, with the first at index zero and the second at a strictly positive ordinary index. -/
theorem exists_vertex_normalization :
    ∃ J' : PolygonalCircle, ∃ k : ℕ,
      2 ≤ k ∧ k + 1 < J'.n ∧ J'.carrier = J.carrier ∧
        J'.vertex 0 = C.P ∧ J'.vertex (k : ZMod J'.n) = C.Q ∧
          ∃ C' : J'.ProperChord, C'.P = C.P ∧ C'.Q = C.Q := by
  obtain ⟨JP, hJPcarrier, hJPP, -⟩ :=
    J.exists_refinement_vertex_zero C.P_mem
  let CP : JP.ProperChord := C.congrCarrier hJPcarrier
  obtain ⟨JQ, hJQcarrier, hJQQ, hkeep⟩ :=
    JP.exists_refinement_vertex_zero CP.Q_mem
  have hPVertex : JQ.IsVertexPoint C.P := by
    apply hkeep C.P
    exact ⟨0, hJPP⟩
  obtain ⟨i, hiP⟩ := hPVertex
  have hi0 : i ≠ 0 := by
    intro hi0
    subst i
    apply C.ne
    calc
      C.P = JQ.vertex 0 := hiP.symm
      _ = C.Q := hJQQ
  let R := JQ.rotate i
  let d : ZMod JQ.n := -i
  have hd0 : d ≠ 0 := by
    intro hd
    apply hi0
    have : -d = i := by simp [d]
    rw [hd] at this
    simpa using this.symm
  have hRcarrier : R.carrier = J.carrier := by
    exact (JQ.rotate_carrier i).trans (hJQcarrier.trans hJPcarrier)
  have hRzero : R.vertex 0 = C.P := by
    change JQ.vertex ((0 : ZMod JQ.n) + i) = C.P
    simpa only [zero_add] using hiP
  have hRk : R.vertex (d.val : ZMod R.n) = C.Q := by
    have hdcast : (d.val : ZMod JQ.n) = d := ZMod.natCast_zmod_val d
    change JQ.vertex ((d.val : ZMod JQ.n) + i) = C.Q
    rw [hdcast]
    simp only [d, neg_add_cancel]
    exact hJQQ
  let CR : R.ProperChord := C.congrCarrier hRcarrier
  have hk1 : d.val ≠ 1 := by
    intro hk1
    have hPedge : CR.P ∈ R.edgeSegment 0 := by
      change C.P ∈ R.edgeSegment 0
      rw [← hRzero]
      exact left_mem_segment ℝ _ _
    have hQedge : CR.Q ∈ R.edgeSegment 0 := by
      change C.Q ∈ R.edgeSegment 0
      rw [← hRk, hk1]
      unfold edgeSegment
      simpa only [Nat.cast_one, zero_add] using
        right_mem_segment ℝ (R.vertex 0) (R.vertex 1)
    exact (CR.endpoint_edges_ne hPedge hQedge) rfl
  have hklast : d.val + 1 ≠ JQ.n := by
    intro hlast
    change d.val + 1 = R.n at hlast
    have hQedge : CR.Q ∈ R.edgeSegment (d.val : ZMod R.n) := by
      change C.Q ∈ R.edgeSegment (d.val : ZMod R.n)
      rw [← hRk]
      exact left_mem_segment ℝ _ _
    have hsucc : (d.val : ZMod R.n) + 1 = 0 := by
      calc
        (d.val : ZMod R.n) + 1 = ((d.val + 1 : ℕ) : ZMod R.n) := by
          rw [Nat.cast_add, Nat.cast_one]
        _ = (R.n : ℕ) := by rw [hlast]
        _ = 0 := ZMod.natCast_self R.n
    have hPedge : CR.P ∈ R.edgeSegment (d.val : ZMod R.n) := by
      change C.P ∈ R.edgeSegment (d.val : ZMod R.n)
      rw [← hRzero]
      unfold edgeSegment
      rw [hsucc]
      exact right_mem_segment ℝ _ _
    exact (CR.endpoint_edges_ne hPedge hQedge) rfl
  refine ⟨R, d.val, ?_, ?_, hRcarrier, hRzero, hRk, CR, rfl, rfl⟩
  · have hdpos := Nat.pos_of_ne_zero fun hdval => hd0 ((ZMod.val_eq_zero d).mp hdval)
    omega
  · have := d.val_lt
    change d.val + 1 < JQ.n
    omega

/-- Reverse the orientation of a proper chord. -/
def symm : J.ProperChord where
  P := C.Q
  Q := C.P
  ne := C.ne.symm
  P_mem := C.Q_mem
  Q_mem := C.P_mem
  interior_subset := by
    rw [segment_symm]
    simpa only [Set.pair_comm] using C.interior_subset

/-- Vertex sequence for the polygon consisting of vertices `0,...,k` and the closing chord. -/
def forwardCutVertex (k : ℕ) : ZMod (k + 1) → Plane :=
  fun i => J.vertex (i.val : ZMod J.n)

theorem forwardCutVertex_natCast {k m : ℕ} (hm : m < k + 1) :
    forwardCutVertex (J := J) k (m : ZMod (k + 1)) = J.vertex (m : ZMod J.n) := by
  unfold forwardCutVertex
  rw [ZMod.val_natCast_of_lt hm]

theorem edgeBeforeChord_inter_chord {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    J.edgeSegment ((k - 1 : ℕ) : ZMod J.n) ∩ segment ℝ C.Q C.P = {C.Q} := by
  let : Fact (1 < J.n) := ⟨by omega⟩
  have hkpos : 0 < k := by omega
  have hkmem : C.Q ∈ J.edgeSegment ((k - 1 : ℕ) : ZMod J.n) := by
    rw [← hQ]
    apply (J.vertex_mem_edgeSegment_iff (k : ZMod J.n)
      ((k - 1 : ℕ) : ZMod J.n)).mpr
    right
    calc
      (k : ZMod J.n) = ((k - 1 + 1 : ℕ) : ZMod J.n) :=
        congrArg (fun q : ℕ => (q : ZMod J.n)) (by omega)
      _ = ((k - 1 : ℕ) : ZMod J.n) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
  have hPnot : C.P ∉ J.edgeSegment ((k - 1 : ℕ) : ZMod J.n) := by
    rw [← hP]
    intro hmem
    rcases (J.vertex_mem_edgeSegment_iff (0 : ZMod J.n)
      ((k - 1 : ℕ) : ZMod J.n)).mp hmem with h | h
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_natCast_of_lt (by omega : k - 1 < J.n)] at hv
      omega
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_add,
        ZMod.val_natCast_of_lt (by omega : k - 1 < J.n), ZMod.val_one] at hv
      rw [Nat.mod_eq_of_lt (by omega : k - 1 + 1 < J.n)] at hv
      omega
  apply Set.Subset.antisymm
  · rintro x ⟨hxEdge, hxChord⟩
    have hxCarrier : x ∈ J.carrier := J.edgeSegment_subset_carrier _ hxEdge
    have hx : x ∈ segment ℝ C.P C.Q ∩ J.carrier := by
      rw [segment_symm]
      exact ⟨hxChord, hxCarrier⟩
    rw [C.segment_inter_carrier] at hx
    rcases hx with rfl | rfl
    · exact (hPnot hxEdge).elim
    · exact Set.mem_singleton _
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨hkmem, left_mem_segment ℝ _ _⟩

theorem chord_inter_firstEdge {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    segment ℝ C.Q C.P ∩ J.edgeSegment 0 = {C.P} := by
  let : Fact (1 < J.n) := ⟨by omega⟩
  have hQnot : C.Q ∉ J.edgeSegment 0 := by
    rw [← hQ]
    intro hmem
    rcases (J.vertex_mem_edgeSegment_iff (k : ZMod J.n) 0).mp hmem with h | h
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega : k < J.n), ZMod.val_zero] at hv
      omega
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega : k < J.n), ZMod.val_add,
        ZMod.val_zero, ZMod.val_one, Nat.zero_add,
        Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
      omega
  have hPmem : C.P ∈ J.edgeSegment 0 := by
    rw [← hP]
    exact left_mem_segment ℝ _ _
  apply Set.Subset.antisymm
  · rintro x ⟨hxChord, hxEdge⟩
    have hxCarrier : x ∈ J.carrier := J.edgeSegment_subset_carrier _ hxEdge
    have hx : x ∈ segment ℝ C.P C.Q ∩ J.carrier := by
      rw [segment_symm]
      exact ⟨hxChord, hxCarrier⟩
    rw [C.segment_inter_carrier] at hx
    rcases hx with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hQnot hxEdge).elim
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨right_mem_segment ℝ _ _, hPmem⟩

theorem chord_disjoint_middleEdge {k m : ℕ} (hm0 : 0 < m) (hmk : m + 1 < k)
    (hk : k < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    Disjoint (segment ℝ C.Q C.P) (J.edgeSegment (m : ZMod J.n)) := by
  let : Fact (1 < J.n) := ⟨by omega⟩
  have hPnot : C.P ∉ J.edgeSegment (m : ZMod J.n) := by
    rw [← hP]
    intro hmem
    rcases (J.vertex_mem_edgeSegment_iff (0 : ZMod J.n) (m : ZMod J.n)).mp hmem with h | h
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_natCast_of_lt (by omega : m < J.n)] at hv
      omega
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_add, ZMod.val_natCast_of_lt (by omega : m < J.n),
        ZMod.val_one, Nat.mod_eq_of_lt (by omega : m + 1 < J.n)] at hv
      omega
  have hQnot : C.Q ∉ J.edgeSegment (m : ZMod J.n) := by
    rw [← hQ]
    intro hmem
    rcases (J.vertex_mem_edgeSegment_iff (k : ZMod J.n) (m : ZMod J.n)).mp hmem with h | h
    · have := natCast_eq_natCast_of_lt hk (by omega : m < J.n) h
      omega
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hk, ZMod.val_add,
        ZMod.val_natCast_of_lt (by omega : m < J.n), ZMod.val_one,
        Nat.mod_eq_of_lt (by omega : m + 1 < J.n)] at hv
      omega
  rw [Set.disjoint_left]
  intro x hxChord hxEdge
  have hxCarrier : x ∈ J.carrier := J.edgeSegment_subset_carrier _ hxEdge
  have hx : x ∈ segment ℝ C.P C.Q ∩ J.carrier := by
    rw [segment_symm]
    exact ⟨hxChord, hxCarrier⟩
  rw [C.segment_inter_carrier] at hx
  exact hx.elim (fun h => hPnot (h ▸ hxEdge)) (fun h => hQnot (h ▸ hxEdge))

/-- The `forwardCutEdgeSegment` declaration. -/
def forwardCutEdgeSegment (k : ℕ) (i : ZMod (k + 1)) : Set Plane :=
  segment ℝ (forwardCutVertex (J := J) k i)
    (forwardCutVertex (J := J) k (i + 1))

theorem forwardCutEdgeSegment_of_lt {k m : ℕ} (hm : m < k) :
    forwardCutEdgeSegment (J := J) k (m : ZMod (k + 1)) =
      J.edgeSegment (m : ZMod J.n) := by
  unfold forwardCutEdgeSegment edgeSegment
  rw [forwardCutVertex_natCast (J := J) (by omega)]
  have hsucc : (m : ZMod (k + 1)) + 1 = (m + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hsucc, forwardCutVertex_natCast (J := J) (by omega)]
  congr 2
  rw [Nat.cast_add, Nat.cast_one]

theorem forwardCutEdgeSegment_last {k : ℕ} (_ : k < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    forwardCutEdgeSegment (J := J) k (k : ZMod (k + 1)) = segment ℝ C.Q C.P := by
  unfold forwardCutEdgeSegment
  rw [forwardCutVertex_natCast (J := J) (by omega), hQ]
  have hwrap : (k : ZMod (k + 1)) + 1 = 0 := by
    calc
      (k : ZMod (k + 1)) + 1 = ((k + 1 : ℕ) : ZMod (k + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = 0 := ZMod.natCast_self (k + 1)
  rw [hwrap]
  unfold forwardCutVertex
  rw [ZMod.val_zero]
  simp only [Nat.cast_zero]
  rw [hP]

theorem forwardCutVertex_adjacent_ne {k : ℕ} (_ : 2 ≤ k) (_ : k < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q)
    (i : ZMod (k + 1)) :
    forwardCutVertex (J := J) k i ≠ forwardCutVertex (J := J) k (i + 1) := by
  let m := i.val
  have hm : m < k + 1 := i.val_lt
  have hcast : (m : ZMod (k + 1)) = i := ZMod.natCast_zmod_val i
  rw [← hcast]
  by_cases hmk : m = k
  · rw [hmk, forwardCutVertex_natCast (J := J) (by omega), hQ]
    have hwrap : (k : ZMod (k + 1)) + 1 = 0 := by
      calc
        (k : ZMod (k + 1)) + 1 = ((k + 1 : ℕ) : ZMod (k + 1)) := by
          rw [Nat.cast_add, Nat.cast_one]
        _ = 0 := ZMod.natCast_self (k + 1)
    rw [hwrap]
    unfold forwardCutVertex
    rw [ZMod.val_zero]
    simp only [Nat.cast_zero]
    rw [hP]
    exact C.ne.symm
  · have hmlt : m < k := by omega
    rw [forwardCutVertex_natCast (J := J) (by omega)]
    have hsucc : (m : ZMod (k + 1)) + 1 = (m + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hsucc, forwardCutVertex_natCast (J := J) (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one] using J.adjacent_ne (m : ZMod J.n)

theorem forwardCut_consecutive_inter {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q)
    (i : ZMod (k + 1)) :
    forwardCutEdgeSegment (J := J) k i ∩
      forwardCutEdgeSegment (J := J) k (i + 1) =
        {forwardCutVertex (J := J) k (i + 1)} := by
  let : Fact (1 < k + 1) := ⟨by omega⟩
  let m := i.val
  have hm : m < k + 1 := i.val_lt
  have hcast : (m : ZMod (k + 1)) = i := ZMod.natCast_zmod_val i
  rw [← hcast]
  by_cases hmk : m = k
  · rw [hmk, C.forwardCutEdgeSegment_last (by omega) hP hQ]
    have hwrap : (k : ZMod (k + 1)) + 1 = 0 := by
      calc
        (k : ZMod (k + 1)) + 1 = ((k + 1 : ℕ) : ZMod (k + 1)) := by
          rw [Nat.cast_add, Nat.cast_one]
        _ = 0 := ZMod.natCast_self (k + 1)
    rw [hwrap]
    unfold forwardCutEdgeSegment forwardCutVertex
    simp only [zero_add, ZMod.val_zero, ZMod.val_one]
    simp only [Nat.cast_zero, Nat.cast_one]
    rw [hP]
    have hfirst := C.chord_inter_firstEdge hk2 hk hP hQ
    unfold edgeSegment at hfirst
    simp only [zero_add] at hfirst
    rw [hP] at hfirst
    exact hfirst
  have hmlt : m < k := by omega
  by_cases hmnext : m + 1 = k
  · rw [forwardCutEdgeSegment_of_lt (J := J) hmlt]
    have hsucc : (m : ZMod (k + 1)) + 1 = (k : ZMod (k + 1)) := by
      calc
        (m : ZMod (k + 1)) + 1 = (m + 1 : ℕ) := by
          rw [Nat.cast_add, Nat.cast_one]
        _ = (k : ℕ) := by rw [hmnext]
    rw [hsucc, C.forwardCutEdgeSegment_last (by omega) hP hQ]
    rw [forwardCutVertex_natCast (J := J) (by omega), hQ]
    have hmEq : m = k - 1 := by omega
    rw [hmEq]
    exact C.edgeBeforeChord_inter_chord hk2 hk hP hQ
  · have hm2 : m + 1 < k := by omega
    rw [forwardCutEdgeSegment_of_lt (J := J) hmlt]
    have hsucc : (m : ZMod (k + 1)) + 1 = (m + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hsucc, forwardCutEdgeSegment_of_lt (J := J) hm2]
    rw [forwardCutVertex_natCast (J := J) (by omega)]
    simpa only [edgeSegment, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using J.consecutive_inter (m : ZMod J.n)

theorem forwardCut_nonadjacent_disjoint {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q)
    (i j : ZMod (k + 1)) (hij : i ≠ j) (hprev : i ≠ j + 1)
    (hnext : j ≠ i + 1) :
    forwardCutEdgeSegment (J := J) k i ∩
      forwardCutEdgeSegment (J := J) k j = ∅ := by
  let : Fact (1 < J.n) := ⟨by omega⟩
  let m := i.val
  let l := j.val
  have hm : m < k + 1 := i.val_lt
  have hl : l < k + 1 := j.val_lt
  have hi : (m : ZMod (k + 1)) = i := ZMod.natCast_zmod_val i
  have hj : (l : ZMod (k + 1)) = j := ZMod.natCast_zmod_val j
  rw [← hi, ← hj] at hij hprev hnext ⊢
  have hmle : m ≤ k := by omega
  have hlle : l ≤ k := by omega
  have hwrap : (k : ZMod (k + 1)) + 1 = 0 := by
    calc
      (k : ZMod (k + 1)) + 1 = ((k + 1 : ℕ) : ZMod (k + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = 0 := ZMod.natCast_self (k + 1)
  by_cases hmk : m = k
  · rw [hmk] at hij hprev hnext ⊢
    by_cases hlk : l = k
    · rw [hlk] at hij
      exact (hij rfl).elim
    have hllt : l < k := by omega
    by_cases hl0 : l = 0
    · rw [hl0, Nat.cast_zero] at hnext
      exact (hnext hwrap.symm).elim
    by_cases hlsucc : l + 1 = k
    · apply False.elim
      apply hprev
      calc
        (k : ZMod (k + 1)) = (l + 1 : ℕ) := by rw [hlsucc]
        _ = (l : ZMod (k + 1)) + 1 := by rw [Nat.cast_add, Nat.cast_one]
    rw [C.forwardCutEdgeSegment_last (by omega) hP hQ,
      forwardCutEdgeSegment_of_lt (J := J) hllt]
    exact Set.disjoint_iff_inter_eq_empty.mp
      (C.chord_disjoint_middleEdge (Nat.pos_of_ne_zero hl0) (by omega)
        (by omega) hP hQ)
  have hmlt : m < k := by omega
  by_cases hlk : l = k
  · rw [hlk] at hij hprev hnext ⊢
    by_cases hm0 : m = 0
    · rw [hm0, Nat.cast_zero] at hprev
      exact (hprev hwrap.symm).elim
    by_cases hmsucc : m + 1 = k
    · apply False.elim
      apply hnext
      calc
        (k : ZMod (k + 1)) = (m + 1 : ℕ) := by rw [hmsucc]
        _ = (m : ZMod (k + 1)) + 1 := by rw [Nat.cast_add, Nat.cast_one]
    rw [forwardCutEdgeSegment_of_lt (J := J) hmlt,
      C.forwardCutEdgeSegment_last (by omega) hP hQ]
    exact Set.disjoint_iff_inter_eq_empty.mp
      (C.chord_disjoint_middleEdge (Nat.pos_of_ne_zero hm0) (by omega)
        (by omega) hP hQ).symm
  have hllt : l < k := by omega
  rw [forwardCutEdgeSegment_of_lt (J := J) hmlt,
    forwardCutEdgeSegment_of_lt (J := J) hllt]
  apply J.nonadjacent_disjoint
  · intro h
    have hml := natCast_eq_natCast_of_lt (by omega : m < J.n) (by omega : l < J.n) h
    apply hij
    rw [hml]
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega : m < J.n), ZMod.val_add,
      ZMod.val_natCast_of_lt (by omega : l < J.n)] at hv
    have hone : (1 : ZMod J.n).val = 1 := by
      rw [ZMod.val_one]
    rw [hone, Nat.mod_eq_of_lt (by omega : l + 1 < J.n)] at hv
    apply hprev
    rw [hv, Nat.cast_add, Nat.cast_one]
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega : l < J.n), ZMod.val_add,
      ZMod.val_natCast_of_lt (by omega : m < J.n)] at hv
    have hone : (1 : ZMod J.n).val = 1 := by
      rw [ZMod.val_one]
    rw [hone, Nat.mod_eq_of_lt (by omega : m + 1 < J.n)] at hv
    apply hnext
    rw [hv, Nat.cast_add, Nat.cast_one]

/-- Close the forward boundary arc from vertex `0` to vertex `k` by a proper chord. -/
def forwardCutCircle {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    PolygonalCircle where
  n := k + 1
  three_le := by omega
  vertex := forwardCutVertex (J := J) k
  adjacent_ne := C.forwardCutVertex_adjacent_ne hk2 (by omega) hP hQ
  consecutive_inter := by
    intro i
    simpa only [forwardCutEdgeSegment, add_assoc, one_add_one_eq_two] using
      C.forwardCut_consecutive_inter hk2 hk hP hQ i
  nonadjacent_disjoint := by
    intro i j hij hprev hnext
    simpa only [forwardCutEdgeSegment] using
      C.forwardCut_nonadjacent_disjoint hk2 hk hP hQ i j hij hprev hnext

/-- The forward boundary arc consisting of old edges `0,...,k-1`. -/
def forwardArc (k : ℕ) : Set Plane :=
  ⋃ m : Fin k, J.edgeSegment (m.val : ZMod J.n)

theorem forwardCutCircle_carrier {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    (C.forwardCutCircle hk2 hk hP hQ).carrier =
      forwardArc (J := J) k ∪ segment ℝ C.Q C.P := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [PolygonalCircle.carrier, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    let m := i.val
    have hm : m < k + 1 := i.val_lt
    have hcast : (m : ZMod (k + 1)) = i := ZMod.natCast_zmod_val i
    rw [← hcast] at hi
    change x ∈ forwardCutEdgeSegment (J := J) k (m : ZMod (k + 1)) at hi
    by_cases hmk : m = k
    · right
      rwa [hmk, C.forwardCutEdgeSegment_last (by omega) hP hQ] at hi
    · left
      have hmlt : m < k := by omega
      simp only [forwardArc, Set.mem_iUnion]
      refine ⟨⟨m, hmlt⟩, ?_⟩
      rwa [forwardCutEdgeSegment_of_lt (J := J) hmlt] at hi
  · rintro x (hx | hx)
    · simp only [forwardArc, Set.mem_iUnion] at hx
      obtain ⟨m, hm⟩ := hx
      simp only [PolygonalCircle.carrier, Set.mem_iUnion]
      refine ⟨(m.val : ZMod (k + 1)), ?_⟩
      change x ∈ forwardCutEdgeSegment (J := J) k (m.val : ZMod (k + 1))
      rwa [forwardCutEdgeSegment_of_lt (J := J) m.isLt]
    · simp only [PolygonalCircle.carrier, Set.mem_iUnion]
      refine ⟨(k : ZMod (k + 1)), ?_⟩
      change x ∈ forwardCutEdgeSegment (J := J) k (k : ZMod (k + 1))
      rwa [C.forwardCutEdgeSegment_last (by omega) hP hQ]

theorem endpoints_mem_forwardArc {k : ℕ} (hk2 : 2 ≤ k) (_ : k < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    C.P ∈ forwardArc (J := J) k ∧ C.Q ∈ forwardArc (J := J) k := by
  constructor
  · simp only [forwardArc, Set.mem_iUnion]
    refine ⟨⟨0, by omega⟩, ?_⟩
    have hmem : C.P ∈ J.edgeSegment 0 := by
      rw [← hP]
      exact left_mem_segment ℝ _ _
    simpa using hmem
  · simp only [forwardArc, Set.mem_iUnion]
    refine ⟨⟨k - 1, by omega⟩, ?_⟩
    change C.Q ∈ J.edgeSegment ((k - 1 : ℕ) : ZMod J.n)
    rw [← hQ]
    apply (J.vertex_mem_edgeSegment_iff (k : ZMod J.n)
      ((k - 1 : ℕ) : ZMod J.n)).mpr
    right
    calc
      (k : ZMod J.n) = ((k - 1 + 1 : ℕ) : ZMod J.n) :=
        congrArg (fun q : ℕ => (q : ZMod J.n)) (by omega)
      _ = ((k - 1 : ℕ) : ZMod J.n) + 1 := by rw [Nat.cast_add, Nat.cast_one]

theorem forwardArc_interior_nonempty {k : ℕ} (hk2 : 2 ≤ k) (_ : k < J.n)
    (hP : J.vertex 0 = C.P) (_ : J.vertex (k : ZMod J.n) = C.Q) :
    (forwardArc (J := J) k \ {C.P, C.Q}).Nonempty := by
  refine ⟨J.vertex 1, ?_, ?_⟩
  · simp only [forwardArc, Set.mem_iUnion]
    refine ⟨⟨0, by omega⟩, ?_⟩
    have hmem : J.vertex 1 ∈ J.edgeSegment 0 := by
      unfold edgeSegment
      simpa only [zero_add] using right_mem_segment ℝ (J.vertex 0) (J.vertex 1)
    simpa using hmem
  · intro hendpoint
    rcases hendpoint with h | h
    · apply J.adjacent_ne 0
      simpa only [zero_add, hP] using h.symm
    · have hPedge : C.P ∈ J.edgeSegment 0 := by
        rw [← hP]
        exact left_mem_segment ℝ _ _
      have hQedge : C.Q ∈ J.edgeSegment 0 := by
        rw [← h]
        unfold edgeSegment
        simpa only [zero_add] using right_mem_segment ℝ (J.vertex 0) (J.vertex 1)
      exact (C.endpoint_edges_ne hPedge hQedge) rfl

theorem forwardArc_subset_carrier {k : ℕ} :
    forwardArc (J := J) k ⊆ J.carrier := by
  intro x hx
  simp only [forwardArc, Set.mem_iUnion] at hx
  obtain ⟨m, hm⟩ := hx
  exact J.edgeSegment_subset_carrier _ hm

/-- The complementary boundary arc, expressed as a forward arc after rotating vertex `k` to
index zero. -/
def backwardArc (k : ℕ) : Set Plane :=
  forwardArc (J := J.rotate (k : ZMod J.n)) (J.n - k)

theorem backwardArc_subset_carrier {k : ℕ} :
    backwardArc (J := J) k ⊆ J.carrier := by
  intro x hx
  have hx' := forwardArc_subset_carrier (J := J.rotate (k : ZMod J.n)) hx
  rwa [J.rotate_carrier] at hx'

theorem rotate_edgeSegment_nat {k m : ℕ} (_ : k < J.n) (_ : m + k < J.n) :
    (J.rotate (k : ZMod J.n)).edgeSegment (m : ZMod J.n) =
      J.edgeSegment (m + k : ZMod J.n) := by
  rw [J.rotate_edgeSegment]

/-- The two cyclic boundary arcs cover the original polygon carrier. -/
theorem forwardArc_union_backwardArc {k : ℕ} (hk : k < J.n) :
    forwardArc (J := J) k ∪ backwardArc (J := J) k = J.carrier := by
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · exact forwardArc_subset_carrier (J := J) hx
    · exact backwardArc_subset_carrier (J := J) hx
  · intro x hx
    simp only [PolygonalCircle.carrier, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    let m := i.val
    have hm : m < J.n := i.val_lt
    have hcast : (m : ZMod J.n) = i := ZMod.natCast_zmod_val i
    rw [← hcast] at hi
    by_cases hmk : m < k
    · left
      simp only [forwardArc, Set.mem_iUnion]
      exact ⟨⟨m, hmk⟩, hi⟩
    · right
      let l := m - k
      have hl : l < J.n - k := by omega
      simp only [backwardArc, forwardArc, Set.mem_iUnion]
      refine ⟨⟨l, hl⟩, ?_⟩
      change x ∈ (J.rotate (k : ZMod J.n)).edgeSegment (l : ZMod J.n)
      have hlk : l + k = m := Nat.sub_add_cancel (Nat.le_of_not_gt hmk)
      have hedge := rotate_edgeSegment_nat (J := J) hk (by omega : l + k < J.n)
      rw [hedge]
      have hidx : (l : ZMod J.n) + (k : ZMod J.n) = (m : ZMod J.n) := by
        rw [← Nat.cast_add, hlk]
      rw [hidx]
      exact hi

/-- The complementary arc has the same two endpoints as the forward arc. -/
theorem endpoints_mem_backwardArc {k : ℕ} (hkpos : 0 < k) (hk2 : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    C.P ∈ backwardArc (J := J) k ∧ C.Q ∈ backwardArc (J := J) k := by
  let R := J.rotate (k : ZMod J.n)
  let CR : R.ProperChord := C.symm.rotate (k : ZMod J.n)
  have hlen : 2 ≤ J.n - k := by omega
  have hRzero : R.vertex 0 = CR.P := by
    change J.vertex ((0 : ZMod J.n) + k) = C.Q
    simpa only [zero_add] using hQ
  have hRlast' : (J.rotate (k : ZMod J.n)).vertex
      ((J.n - k : ℕ) : ZMod J.n) = C.P := by
    change J.vertex (((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n)) = C.P
    have hsum : ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) = 0 := by
      calc
        ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) =
            ((J.n - k + k : ℕ) : ZMod J.n) := by rw [Nat.cast_add]
        _ = (J.n : ℕ) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 0 := ZMod.natCast_self J.n
    rw [hsum]
    exact hP
  have hRlast : R.vertex ((J.n - k : ℕ) : ZMod R.n) = CR.Q := by
    exact hRlast'
  have hlenlt : J.n - k < R.n := by
    change J.n - k < J.n
    omega
  have hends := CR.endpoints_mem_forwardArc hlen hlenlt hRzero hRlast
  exact ⟨hends.2, hends.1⟩

theorem forwardArc_inter_chord {k : ℕ} (hk2 : 2 ≤ k) (hk : k < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    forwardArc (J := J) k ∩ segment ℝ C.P C.Q = {C.P, C.Q} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxArc, hxChord⟩
    have hxCarrier := forwardArc_subset_carrier (J := J) hxArc
    exact C.segment_inter_carrier ▸ ⟨hxChord, hxCarrier⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨(C.endpoints_mem_forwardArc hk2 hk hP hQ).1,
        left_mem_segment ℝ _ _⟩
    · exact ⟨(C.endpoints_mem_forwardArc hk2 hk hP hQ).2,
        right_mem_segment ℝ _ _⟩

theorem backwardArc_inter_chord {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    backwardArc (J := J) k ∩ segment ℝ C.P C.Q = {C.P, C.Q} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxArc, hxChord⟩
    have hxCarrier := backwardArc_subset_carrier (J := J) hxArc
    exact C.segment_inter_carrier ▸ ⟨hxChord, hxCarrier⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨(C.endpoints_mem_backwardArc (by omega) hk hP hQ).1,
        left_mem_segment ℝ _ _⟩
    · exact ⟨(C.endpoints_mem_backwardArc (by omega) hk hP hQ).2,
        right_mem_segment ℝ _ _⟩

/-- The two complementary cyclic boundary arcs meet only at their endpoints. -/
theorem forwardArc_inter_backwardArc {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    forwardArc (J := J) k ∩ backwardArc (J := J) k = {C.P, C.Q} := by
  let : Fact (1 < J.n) := ⟨by omega⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxF, hxB⟩
    simp only [forwardArc, Set.mem_iUnion] at hxF
    simp only [backwardArc, forwardArc, Set.mem_iUnion] at hxB
    obtain ⟨m, hm⟩ := hxF
    obtain ⟨l, hl⟩ := hxB
    let a := m.val
    let b := l.val + k
    have ha : a < k := m.isLt
    have hb0 : k ≤ b := by dsimp [b]; omega
    have hbn : b < J.n := by dsimp [b]; omega
    have hm' : x ∈ J.edgeSegment (a : ZMod J.n) := by
      simpa [a] using hm
    have hrot := rotate_edgeSegment_nat (J := J) (k := k) (m := l.val)
      (by omega) (by omega)
    have hlOld : x ∈ J.edgeSegment (b : ZMod J.n) := by
      have hl' : x ∈ (J.rotate (k : ZMod J.n)).edgeSegment (l.val : ZMod J.n) := by
        exact hl
      rw [hrot] at hl'
      have hidx : (l.val : ZMod J.n) + (k : ZMod J.n) = (b : ZMod J.n) := by
        dsimp [b]
        rw [Nat.cast_add]
      rwa [hidx] at hl'
    have hab : (a : ZMod J.n) ≠ (b : ZMod J.n) := by
      intro heq
      have := natCast_eq_natCast_of_lt (by omega : a < J.n) hbn heq
      omega
    have hxEnds := J.edgeSegment_inter_subset_endpoints hab ⟨hm', hlOld⟩
    rcases hxEnds with hxa | hxa
    · have hvertexB : J.vertex (a : ZMod J.n) ∈ J.edgeSegment (b : ZMod J.n) := by
        rwa [hxa] at hlOld
      rcases (J.vertex_mem_edgeSegment_iff (a : ZMod J.n)
        (b : ZMod J.n)).mp hvertexB with heq | hsucc
      · exact (hab heq).elim
      · have hv := congrArg ZMod.val hsucc
        rw [ZMod.val_natCast_of_lt (by omega : a < J.n), ZMod.val_add,
          ZMod.val_natCast_of_lt hbn, ZMod.val_one] at hv
        by_cases hblt : b + 1 < J.n
        · rw [Nat.mod_eq_of_lt hblt] at hv
          omega
        · have hblast : b + 1 = J.n := by omega
          rw [hblast, Nat.mod_self] at hv
          have ha0 : a = 0 := by omega
          left
          calc
            x = J.vertex (a : ZMod J.n) := hxa
            _ = J.vertex (0 : ZMod J.n) := by rw [ha0]; simp only [Nat.cast_zero]
            _ = C.P := hP
    · have ha1 : a + 1 < J.n := by omega
      rw [Set.mem_singleton_iff] at hxa
      have hcast : (a : ZMod J.n) + 1 = (a + 1 : ℕ) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hcast] at hxa
      have hvertexB : J.vertex ((a + 1 : ℕ) : ZMod J.n) ∈
          J.edgeSegment (b : ZMod J.n) := by
        rwa [hxa] at hlOld
      rcases (J.vertex_mem_edgeSegment_iff ((a + 1 : ℕ) : ZMod J.n)
        (b : ZMod J.n)).mp hvertexB with heq | hsucc
      · have habNat := natCast_eq_natCast_of_lt ha1 hbn heq
        have haLast : a + 1 = k := by omega
        right
        calc
          x = J.vertex ((a + 1 : ℕ) : ZMod J.n) := hxa
          _ = J.vertex (k : ZMod J.n) := by rw [haLast]
          _ = C.Q := hQ
      · have hv := congrArg ZMod.val hsucc
        rw [ZMod.val_natCast_of_lt ha1, ZMod.val_add,
          ZMod.val_natCast_of_lt hbn, ZMod.val_one] at hv
        by_cases hblt : b + 1 < J.n
        · rw [Nat.mod_eq_of_lt hblt] at hv
          omega
        · have hblast : b + 1 = J.n := by omega
          rw [hblast, Nat.mod_self] at hv
          omega
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨(C.endpoints_mem_forwardArc hk2 (by omega) hP hQ).1,
        (C.endpoints_mem_backwardArc (by omega) hk hP hQ).1⟩
    · exact ⟨(C.endpoints_mem_forwardArc hk2 (by omega) hP hQ).2,
        (C.endpoints_mem_backwardArc (by omega) hk hP hQ).2⟩

/-- Close the complementary boundary arc by the same chord, using a cyclic rotation. -/
def backwardCutCircle {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    PolygonalCircle := by
  let R := J.rotate (k : ZMod J.n)
  let CR : R.ProperChord := C.symm.rotate (k : ZMod J.n)
  have hlen : 2 ≤ J.n - k := by omega
  have hcut : J.n - k + 1 < R.n := by
    change J.n - k + 1 < J.n
    omega
  have hRzero : R.vertex 0 = CR.P := by
    change J.vertex ((0 : ZMod J.n) + k) = C.Q
    simpa only [zero_add] using hQ
  have hRlast : R.vertex ((J.n - k : ℕ) : ZMod R.n) = CR.Q := by
    change J.vertex (((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n)) = C.P
    have hsum : ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) = 0 := by
      calc
        ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) =
            ((J.n - k + k : ℕ) : ZMod J.n) := by rw [Nat.cast_add]
        _ = (J.n : ℕ) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 0 := ZMod.natCast_self J.n
    rw [hsum]
    exact hP
  exact CR.forwardCutCircle hlen hcut hRzero hRlast

theorem backwardCutCircle_carrier {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    (C.backwardCutCircle hk2 hk hP hQ).carrier =
      backwardArc (J := J) k ∪ segment ℝ C.P C.Q := by
  classical
  unfold backwardCutCircle
  dsimp only
  rw [PolygonalCircle.ProperChord.forwardCutCircle_carrier]
  simp only [backwardArc, ProperChord.symm, ProperChord.rotate]

theorem backwardArc_interior_nonempty {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    (backwardArc (J := J) k \ {C.P, C.Q}).Nonempty := by
  let R := J.rotate (k : ZMod J.n)
  let CR : R.ProperChord := C.symm.rotate (k : ZMod J.n)
  have hlen : 2 ≤ J.n - k := by omega
  have hRzero : R.vertex 0 = CR.P := by
    change J.vertex ((0 : ZMod J.n) + k) = C.Q
    simpa only [zero_add] using hQ
  have hRlast : R.vertex ((J.n - k : ℕ) : ZMod R.n) = CR.Q := by
    change J.vertex (((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n)) = C.P
    have hsum : ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) = 0 := by
      calc
        ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) =
            ((J.n - k + k : ℕ) : ZMod J.n) := by rw [Nat.cast_add]
        _ = (J.n : ℕ) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 0 := ZMod.natCast_self J.n
    rw [hsum]
    exact hP
  have hnonempty := CR.forwardArc_interior_nonempty hlen (by
    change J.n - k < J.n
    omega) hRzero hRlast
  have hCRP : CR.P = C.Q := rfl
  have hCRQ : CR.Q = C.P := rfl
  rw [hCRP, hCRQ] at hnonempty
  simpa only [backwardArc, Set.pair_comm] using hnonempty

end ProperChord

/-- Crossing predicate for one oriented segment, separated from cyclic indexing. -/
def SegmentCrossed (v w P : Plane) : Prop :=
  (v 1 ≤ P 1 ∧ P 1 < w 1 ∨ w 1 ≤ P 1 ∧ P 1 < v 1) ∧
    crossingX v w (P 1) < P 0

theorem edgeCrossed_iff_segmentCrossed (J : PolygonalCircle) (i : ZMod J.n) (P : Plane) :
    J.EdgeCrossed i P ↔ SegmentCrossed (J.vertex i) (J.vertex (i + 1)) P :=
  Iff.rfl

theorem crossingX_comm {v w : Plane} {y : ℝ} (h : v 1 ≠ w 1) :
    crossingX v w y = crossingX w v y := by
  unfold crossingX
  field_simp
  ring

theorem segmentCrossed_comm (v w P : Plane) :
    SegmentCrossed v w P ↔ SegmentCrossed w v P := by
  by_cases hheight : v 1 = w 1
  · unfold SegmentCrossed
    rw [hheight]
    constructor <;> rintro ⟨hband, -⟩ <;>
      rcases hband with hband | hband <;>
      exact (not_lt_of_ge hband.1 hband.2).elim
  · unfold SegmentCrossed
    rw [crossingX_comm hheight]
    tauto

open scoped Classical in
/-- Number of crossed polygon edges before reducing modulo two, indexed by ordinary naturals. -/
noncomputable def crossingCount (J : PolygonalCircle) (P : Plane) : ℕ :=
  ∑ m ∈ Finset.range J.n, if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0

theorem index_eq_crossingCount_mod (J : PolygonalCircle) (P : Plane) :
    J.index P = J.crossingCount P % 2 := by
  classical
  unfold index crossingCount
  rw [Finset.card_filter]
  simp only [Finset.sum_const_zero, Finset.sum_ite, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  congr 2
  apply Finset.card_bij (fun z _ => z.val)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨z.val_lt, by rwa [ZMod.natCast_zmod_val z]⟩
  · intro z _ w _ h
    exact ZMod.val_injective J.n h
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    refine ⟨(m : ZMod J.n), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [ZMod.val_natCast_of_lt hm.1] using hm.2
    · exact ZMod.val_natCast_of_lt hm.1

theorem rotate_edgeCrossed_iff (J : PolygonalCircle) (a i : ZMod J.n) (P : Plane) :
    (J.rotate a).EdgeCrossed i P ↔ J.EdgeCrossed (i + a) P := by
  change SegmentCrossed (J.vertex (i + a)) (J.vertex ((i + 1) + a)) P ↔
    SegmentCrossed (J.vertex (i + a)) (J.vertex (i + a + 1)) P
  abel

namespace ProperChord

variable {J : PolygonalCircle} (C : J.ProperChord)

theorem forwardCutCircle_edgeCrossed_of_lt {k m : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (hm : m < k) (P : Plane) :
    (C.forwardCutCircle hk2 hk hP hQ).EdgeCrossed (m : ZMod (k + 1)) P ↔
      J.EdgeCrossed (m : ZMod J.n) P := by
  change SegmentCrossed (forwardCutVertex (J := J) k (m : ZMod (k + 1)))
      (forwardCutVertex (J := J) k ((m : ZMod (k + 1)) + 1)) P ↔
    SegmentCrossed (J.vertex (m : ZMod J.n)) (J.vertex ((m : ZMod J.n) + 1)) P
  rw [forwardCutVertex_natCast (J := J) (by omega)]
  have hsucc : (m : ZMod (k + 1)) + 1 = (m + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hsucc, forwardCutVertex_natCast (J := J) (by omega)]
  rw [Nat.cast_add, Nat.cast_one]

theorem forwardCutCircle_edgeCrossed_last {k : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (P : Plane) :
    (C.forwardCutCircle hk2 hk hP hQ).EdgeCrossed (k : ZMod (k + 1)) P ↔
      SegmentCrossed C.P C.Q P := by
  change SegmentCrossed (forwardCutVertex (J := J) k (k : ZMod (k + 1)))
      (forwardCutVertex (J := J) k ((k : ZMod (k + 1)) + 1)) P ↔
    SegmentCrossed C.P C.Q P
  rw [forwardCutVertex_natCast (J := J) (by omega), hQ]
  have hwrap : (k : ZMod (k + 1)) + 1 = 0 := by
    calc
      (k : ZMod (k + 1)) + 1 = ((k + 1 : ℕ) : ZMod (k + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = 0 := ZMod.natCast_self (k + 1)
  have hnext : forwardCutVertex (J := J) k ((k : ZMod (k + 1)) + 1) = C.P := by
    rw [hwrap]
    unfold forwardCutVertex
    rw [ZMod.val_zero]
    simpa only [Nat.cast_zero] using hP
  have hnextEq : SegmentCrossed C.Q
      (forwardCutVertex (J := J) k ((k : ZMod (k + 1)) + 1)) P =
        SegmentCrossed C.Q C.P P :=
    congrArg (fun q => SegmentCrossed C.Q q P) hnext
  constructor
  · intro h
    have h' : SegmentCrossed C.Q
        (forwardCutVertex (J := J) k ((k : ZMod (k + 1)) + 1)) P := h
    exact (segmentCrossed_comm C.Q C.P P).mp (hnextEq.mp h')
  · intro h
    have h' := (segmentCrossed_comm C.Q C.P P).mpr h
    have h'' : SegmentCrossed C.Q
        (forwardCutVertex (J := J) k ((k : ZMod (k + 1)) + 1)) P :=
      hnextEq.mpr h'
    exact h''

open scoped Classical in
theorem crossingCount_forwardCutCircle {k : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (P : Plane) :
    (C.forwardCutCircle hk2 hk hP hQ).crossingCount P =
      (∑ m ∈ Finset.range k, if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0) +
        if SegmentCrossed C.P C.Q P then 1 else 0 := by
  unfold crossingCount
  change (∑ m ∈ Finset.range (k + 1),
    if (C.forwardCutCircle hk2 hk hP hQ).EdgeCrossed (m : ZMod (k + 1)) P
      then 1 else 0) = _
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    have hmlt := Finset.mem_range.mp hm
    rw [C.forwardCutCircle_edgeCrossed_of_lt hk2 hk hP hQ hmlt]
  · rw [C.forwardCutCircle_edgeCrossed_last hk2 hk hP hQ]

open scoped Classical in
theorem crossingCount_backwardCutCircle {k : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (P : Plane) :
    (C.backwardCutCircle hk2 hk hP hQ).crossingCount P =
      (∑ m ∈ Finset.range (J.n - k),
        if J.EdgeCrossed ((m + k : ℕ) : ZMod J.n) P then 1 else 0) +
          if SegmentCrossed C.P C.Q P then 1 else 0 := by
  let R := J.rotate (k : ZMod J.n)
  let CR : R.ProperChord := C.symm.rotate (k : ZMod J.n)
  have hlen : 2 ≤ J.n - k := by omega
  have hcut : J.n - k + 1 < R.n := by
    change J.n - k + 1 < J.n
    omega
  have hRzero : R.vertex 0 = CR.P := by
    change J.vertex ((0 : ZMod J.n) + k) = C.Q
    simpa only [zero_add] using hQ
  have hRlast : R.vertex ((J.n - k : ℕ) : ZMod R.n) = CR.Q := by
    change J.vertex (((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n)) = C.P
    have hsum : ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) = 0 := by
      calc
        ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) =
            ((J.n - k + k : ℕ) : ZMod J.n) := by rw [Nat.cast_add]
        _ = (J.n : ℕ) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 0 := ZMod.natCast_self J.n
    rw [hsum]
    exact hP
  have hcount := CR.crossingCount_forwardCutCircle hlen hcut hRzero hRlast P
  change (CR.forwardCutCircle hlen hcut hRzero hRlast).crossingCount P = _
  rw [hcount]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    have hmlt := Finset.mem_range.mp hm
    have hrotate := J.rotate_edgeCrossed_iff (k : ZMod J.n)
      (m : ZMod J.n) P
    have hidx : (m : ZMod J.n) + (k : ZMod J.n) = (m + k : ℕ) := by
      rw [Nat.cast_add]
    rw [hidx] at hrotate
    have hrotate' : R.EdgeCrossed (m : ZMod R.n) P ↔
        J.EdgeCrossed ((m + k : ℕ) : ZMod J.n) P := hrotate
    exact if_congr hrotate' rfl rfl
  · have hcomm := segmentCrossed_comm C.Q C.P P
    change (if SegmentCrossed C.Q C.P P then 1 else 0) = _
    exact if_congr hcomm rfl rfl

theorem index_parity_cutCircles {k : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (P : Plane) :
    J.index P = ((C.forwardCutCircle hk2 hk hP hQ).index P +
      (C.backwardCutCircle hk2 hk hP hQ).index P) % 2 := by
  classical
  let A := ∑ m ∈ Finset.range k,
    if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0
  let B := ∑ m ∈ Finset.range (J.n - k),
    if J.EdgeCrossed ((m + k : ℕ) : ZMod J.n) P then 1 else 0
  let e := if SegmentCrossed C.P C.Q P then 1 else 0
  have hcountJ : J.crossingCount P = A + B := by
    unfold crossingCount A B
    have hkn : k + (J.n - k) = J.n := Nat.add_sub_of_le (by omega)
    calc
      (∑ m ∈ Finset.range J.n,
          if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0) =
          ∑ m ∈ Finset.range (k + (J.n - k)),
            if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0 := by rw [hkn]
      _ = (∑ m ∈ Finset.range k,
          if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0) +
          ∑ m ∈ Finset.range (J.n - k),
            if J.EdgeCrossed ((k + m : ℕ) : ZMod J.n) P then 1 else 0 := by
              exact Finset.sum_range_add _ _ _
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro m hm
        rw [Nat.add_comm]
  have hcountF := C.crossingCount_forwardCutCircle hk2 hk hP hQ P
  have hcountB := C.crossingCount_backwardCutCircle hk2 hk hP hQ P
  rw [J.index_eq_crossingCount_mod,
    (C.forwardCutCircle hk2 hk hP hQ).index_eq_crossingCount_mod,
    (C.backwardCutCircle hk2 hk hP hQ).index_eq_crossingCount_mod,
    hcountJ, hcountF, hcountB]
  change (A + B) % 2 = ((A + e) % 2 + (B + e) % 2) % 2
  dsimp [e]
  by_cases hcross : SegmentCrossed C.P C.Q P <;> simp [hcross] ; omega

end ProperChord

end PolygonalCircle

/-- The carrier data of a polygonal theta graph.  `J12`, `J13`, and `J23` are the polygons
formed by the indicated pairs of arcs. -/
structure PolygonalTheta where
  /-- The `P` declaration. -/
  P : Plane
  /-- The `Q` declaration. -/
  Q : Plane
  /-- The `B1` declaration. -/
  B1 : Set Plane
  /-- The `B2` declaration. -/
  B2 : Set Plane
  /-- The `B3` declaration. -/
  B3 : Set Plane
  /-- The `J12` declaration. -/
  J12 : PolygonalCircle
  /-- The `J13` declaration. -/
  J13 : PolygonalCircle
  /-- The `J23` declaration. -/
  J23 : PolygonalCircle
  P_mem_B1 : P ∈ B1
  Q_mem_B1 : Q ∈ B1
  P_mem_B2 : P ∈ B2
  Q_mem_B2 : Q ∈ B2
  P_mem_B3 : P ∈ B3
  Q_mem_B3 : Q ∈ B3
  B1_inter_B2 : B1 ∩ B2 = {P, Q}
  B1_inter_B3 : B1 ∩ B3 = {P, Q}
  B2_inter_B3 : B2 ∩ B3 = {P, Q}
  carrier12 : J12.carrier = B1 ∪ B2
  carrier13 : J13.carrier = B1 ∪ B3
  carrier23 : J23.carrier = B2 ∪ B3
  chord_subset : B3 ⊆ {P, Q} ∪ J12.interiorRegion
  B1_interior_nonempty : (B1 \ {P, Q}).Nonempty
  B2_interior_nonempty : (B2 \ {P, Q}).Nonempty
  chord_interior_nonempty : (B3 \ {P, Q}).Nonempty
  index_parity : ∀ x, x ∉ J12.carrier → x ∉ J13.carrier → x ∉ J23.carrier →
    J12.index x = (J13.index x + J23.index x) % 2

namespace PolygonalCircle.ProperChord

variable {J : PolygonalCircle} (C : J.ProperChord)

/-- Every proper straight chord of a polygon determines the finite polygonal theta graph used
in Moise Chapter 2, Theorems 7 and 8. -/
theorem exists_polygonalTheta :
    ∃ G : PolygonalTheta,
      G.J12.carrier = J.carrier ∧ G.P = C.P ∧ G.Q = C.Q ∧ G.B3 = segment ℝ C.P C.Q := by
  obtain ⟨J', k, hk2, hk, hcarrier, hP, hQ, C', hC'P, hC'Q⟩ :=
    C.exists_vertex_normalization
  have hP' : J'.vertex 0 = C'.P := hP.trans hC'P.symm
  have hQ' : J'.vertex (k : ZMod J'.n) = C'.Q := hQ.trans hC'Q.symm
  let J13 := C'.forwardCutCircle hk2 hk hP' hQ'
  let J23 := C'.backwardCutCircle hk2 hk hP' hQ'
  let B1 := forwardArc (J := J') k
  let B2 := backwardArc (J := J') k
  let B3 := segment ℝ C'.P C'.Q
  let G : PolygonalTheta :=
    { P := C'.P
      Q := C'.Q
      B1 := B1
      B2 := B2
      B3 := B3
      J12 := J'
      J13 := J13
      J23 := J23
      P_mem_B1 := (C'.endpoints_mem_forwardArc hk2 (by omega) hP' hQ').1
      Q_mem_B1 := (C'.endpoints_mem_forwardArc hk2 (by omega) hP' hQ').2
      P_mem_B2 := (C'.endpoints_mem_backwardArc (by omega) hk hP' hQ').1
      Q_mem_B2 := (C'.endpoints_mem_backwardArc (by omega) hk hP' hQ').2
      P_mem_B3 := left_mem_segment ℝ _ _
      Q_mem_B3 := right_mem_segment ℝ _ _
      B1_inter_B2 := C'.forwardArc_inter_backwardArc hk2 hk hP' hQ'
      B1_inter_B3 := C'.forwardArc_inter_chord hk2 (by omega) hP' hQ'
      B2_inter_B3 := C'.backwardArc_inter_chord hk2 hk hP' hQ'
      carrier12 := by
        dsimp [B1, B2]
        exact (forwardArc_union_backwardArc (J := J') (by omega)).symm
      carrier13 := by
        dsimp [J13, B1, B3]
        rw [C'.forwardCutCircle_carrier hk2 hk hP' hQ', segment_symm]
      carrier23 := by
        dsimp [J23, B2, B3]
        exact C'.backwardCutCircle_carrier hk2 hk hP' hQ'
      chord_subset := by
        intro x hx
        by_cases hxEnds : x ∈ ({C'.P, C'.Q} : Set Plane)
        · exact Or.inl hxEnds
        · exact Or.inr (C'.interior_subset ⟨hx, hxEnds⟩)
      B1_interior_nonempty := C'.forwardArc_interior_nonempty hk2 (by omega) hP' hQ'
      B2_interior_nonempty := C'.backwardArc_interior_nonempty hk2 hk hP' hQ'
      chord_interior_nonempty := C'.interior_nonempty
      index_parity := by
        intro x _ _ _
        exact C'.index_parity_cutCircles hk2 hk hP' hQ' x }
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · exact hcarrier
  · exact hC'P
  · exact hC'Q
  · dsimp [G, B3]
    rw [hC'P, hC'Q]

end PolygonalCircle.ProperChord

/-- A theta crosscut realized by an edge of a triangle mesh of the original polygonal disk.
This is the exact interface between the separation theorem of Chapter 2 and the cutting
induction of Chapter 3. -/
structure PolygonalTheta.MeshCrosscut (G : PolygonalTheta) (M : TriangleMesh) where
  support_eq : M.toPlaneComplex.support = G.J12.closedRegion
  /-- The `chordEdge` declaration. -/
  chordEdge : Finset M.Vertex
  chordEdge_mem : chordEdge ∈ M.edges
  chordVertices : M.position '' (chordEdge : Set M.Vertex) = {G.P, G.Q}
  chordCarrier : convexHull ℝ (M.position '' (chordEdge : Set M.Vertex)) = G.B3

namespace PolygonalTheta

variable (G : PolygonalTheta)

theorem endpoints_subset_carrier12 : ({G.P, G.Q} : Set Plane) ⊆ G.J12.carrier := by
  rw [G.carrier12]
  intro x hx
  rcases hx with (rfl | rfl) <;> simp [G.P_mem_B1, G.Q_mem_B1]

theorem exterior12_disjoint_B3 : Disjoint G.J12.exteriorRegion G.B3 := by
  rw [Set.disjoint_left]
  intro x hxExterior hxB3
  rcases G.chord_subset hxB3 with hxEndpoint | hxInterior
  · have hxCarrier := G.endpoints_subset_carrier12 hxEndpoint
    have hxCompl : x ∈ G.J12.carrierᶜ := by
      rw [← G.J12.interior_union_exterior]
      exact Or.inr hxExterior
    exact hxCompl hxCarrier
  · exact Set.disjoint_left.mp G.J12.disjoint_interior_exterior hxInterior hxExterior

theorem exterior12_subset_exterior13 :
    G.J12.exteriorRegion ⊆ G.J13.exteriorRegion := by
  have hsubsetCompl : G.J12.exteriorRegion ⊆ G.J13.carrierᶜ := by
    intro x hx
    rw [G.carrier13]
    intro hxCarrier
    rcases hxCarrier with hxB1 | hxB3
    · have hxJ12 : x ∈ G.J12.carrier := by rw [G.carrier12]; exact Or.inl hxB1
      have hxCompl : x ∈ G.J12.carrierᶜ := by
        rw [← G.J12.interior_union_exterior]
        exact Or.inr hx
      exact hxCompl hxJ12
    · exact Set.disjoint_left.mp G.exterior12_disjoint_B3 hx hxB3
  have hsubsetUnion : G.J12.exteriorRegion ⊆
      G.J13.interiorRegion ∪ G.J13.exteriorRegion := by
    rw [G.J13.interior_union_exterior]
    exact hsubsetCompl
  by_contra hnot
  have hwitness : ∃ x ∈ G.J12.exteriorRegion, x ∈ G.J13.interiorRegion := by
    obtain ⟨x, hx12, hxNot13⟩ := Set.not_subset.mp hnot
    rcases hsubsetUnion hx12 with hx13 | hx13
    · exact ⟨x, hx12, hx13⟩
    · exact (hxNot13 hx13).elim
  have hallInterior : G.J12.exteriorRegion ⊆ G.J13.interiorRegion :=
    G.J12.isConnected_exteriorRegion.isPreconnected.subset_left_of_subset_union
      G.J13.isOpen_interiorRegion G.J13.isOpen_exteriorRegion
      G.J13.disjoint_interior_exterior hsubsetUnion hwitness
  exact G.J12.not_isBounded_exteriorRegion
    (G.J13.isBounded_interiorRegion.subset hallInterior)

theorem B2_diff_endpoints_subset_exterior13 :
    G.B2 \ {G.P, G.Q} ⊆ G.J13.exteriorRegion := by
  intro x hx
  have hxFrontier12 : x ∈ frontier G.J12.exteriorRegion := by
    rw [G.J12.frontier_exteriorRegion, G.carrier12]
    exact Or.inr hx.1
  have hxClosure12 : x ∈ closure G.J12.exteriorRegion := frontier_subset_closure hxFrontier12
  have hxClosure13 : x ∈ closure G.J13.exteriorRegion :=
    closure_mono G.exterior12_subset_exterior13 hxClosure12
  have hxNotCarrier13 : x ∉ G.J13.carrier := by
    rw [G.carrier13]
    rintro (hxB1 | hxB3)
    · have : x ∈ G.B1 ∩ G.B2 := ⟨hxB1, hx.1⟩
      rw [G.B1_inter_B2] at this
      exact hx.2 this
    · have : x ∈ G.B2 ∩ G.B3 := ⟨hx.1, hxB3⟩
      rw [G.B2_inter_B3] at this
      exact hx.2 this
  rw [closure_eq_self_union_frontier, G.J13.frontier_exteriorRegion] at hxClosure13
  exact hxClosure13.resolve_right hxNotCarrier13

theorem interior13_subset_interior12 :
    G.J13.interiorRegion ⊆ G.J12.interiorRegion := by
  have hsubsetCompl : G.J13.interiorRegion ⊆ G.J12.carrierᶜ := by
    intro x hx13
    rw [G.carrier12]
    rintro (hxB1 | hxB2)
    · have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inl hxB1
      have hxCompl13 : x ∈ G.J13.carrierᶜ := by
        rw [← G.J13.interior_union_exterior]
        exact Or.inl hx13
      exact hxCompl13 hxCarrier13
    · by_cases hxEndpoint : x ∈ ({G.P, G.Q} : Set Plane)
      · have hxB1 : x ∈ G.B1 := by
          rcases hxEndpoint with (rfl | rfl)
          · exact G.P_mem_B1
          · exact G.Q_mem_B1
        have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inl hxB1
        have hxCompl13 : x ∈ G.J13.carrierᶜ := by
          rw [← G.J13.interior_union_exterior]
          exact Or.inl hx13
        exact hxCompl13 hxCarrier13
      · have hxExterior13 := G.B2_diff_endpoints_subset_exterior13 ⟨hxB2, hxEndpoint⟩
        exact Set.disjoint_left.mp G.J13.disjoint_interior_exterior hx13 hxExterior13
  have hsubsetUnion : G.J13.interiorRegion ⊆
      G.J12.interiorRegion ∪ G.J12.exteriorRegion := by
    rw [G.J12.interior_union_exterior]
    exact hsubsetCompl
  obtain ⟨y, hyB3, hyEndpoint⟩ := G.chord_interior_nonempty
  have hyInside12 : y ∈ G.J12.interiorRegion :=
    (G.chord_subset hyB3).resolve_left hyEndpoint
  have hyFrontier13 : y ∈ frontier G.J13.interiorRegion := by
    rw [G.J13.frontier_interiorRegion, G.carrier13]
    exact Or.inr hyB3
  have hyClosure : y ∈ closure
      (G.J12.interiorRegion ∩ G.J13.interiorRegion) :=
    G.J12.isOpen_interiorRegion.inter_closure
      ⟨hyInside12, frontier_subset_closure hyFrontier13⟩
  obtain ⟨z, hz12, hz13⟩ := Set.Nonempty.of_closure ⟨y, hyClosure⟩
  exact G.J13.isConnected_interiorRegion.isPreconnected.subset_left_of_subset_union
    G.J12.isOpen_interiorRegion G.J12.isOpen_exteriorRegion
    G.J12.disjoint_interior_exterior hsubsetUnion ⟨z, hz13, hz12⟩

/-- Exchange the two boundary arcs of a theta graph. -/
def swap12 : PolygonalTheta where
  P := G.P
  Q := G.Q
  B1 := G.B2
  B2 := G.B1
  B3 := G.B3
  J12 := G.J12
  J13 := G.J23
  J23 := G.J13
  P_mem_B1 := G.P_mem_B2
  Q_mem_B1 := G.Q_mem_B2
  P_mem_B2 := G.P_mem_B1
  Q_mem_B2 := G.Q_mem_B1
  P_mem_B3 := G.P_mem_B3
  Q_mem_B3 := G.Q_mem_B3
  B1_inter_B2 := by rw [Set.inter_comm, G.B1_inter_B2]
  B1_inter_B3 := G.B2_inter_B3
  B2_inter_B3 := G.B1_inter_B3
  carrier12 := by rw [G.carrier12, Set.union_comm]
  carrier13 := G.carrier23
  carrier23 := G.carrier13
  chord_subset := G.chord_subset
  B1_interior_nonempty := G.B2_interior_nonempty
  B2_interior_nonempty := G.B1_interior_nonempty
  chord_interior_nonempty := G.chord_interior_nonempty
  index_parity := by
    intro x hx12 hx23 hx13
    rw [Nat.add_comm]
    exact G.index_parity x hx12 hx13 hx23

theorem exterior12_subset_exterior23 :
    G.J12.exteriorRegion ⊆ G.J23.exteriorRegion :=
  (G.swap12).exterior12_subset_exterior13

theorem B1_diff_endpoints_subset_exterior23 :
    G.B1 \ {G.P, G.Q} ⊆ G.J23.exteriorRegion :=
  (G.swap12).B2_diff_endpoints_subset_exterior13

theorem interior23_subset_interior12 :
    G.J23.interiorRegion ⊆ G.J12.interiorRegion :=
  (G.swap12).interior13_subset_interior12

/-- The interior of one cut-off polygon lies in the exterior of the other. -/
theorem interior13_subset_exterior23 :
    G.J13.interiorRegion ⊆ G.J23.exteriorRegion := by
  have hsubsetCompl : G.J13.interiorRegion ⊆ G.J23.carrierᶜ := by
    intro x hx13
    rw [G.carrier23]
    rintro (hxB2 | hxB3)
    · by_cases hxEndpoint : x ∈ ({G.P, G.Q} : Set Plane)
      · have hxB1 : x ∈ G.B1 := by
          rcases hxEndpoint with (rfl | rfl)
          · exact G.P_mem_B1
          · exact G.Q_mem_B1
        have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inl hxB1
        have hxCompl13 : x ∈ G.J13.carrierᶜ := by
          rw [← G.J13.interior_union_exterior]
          exact Or.inl hx13
        exact hxCompl13 hxCarrier13
      · have hxExterior13 := G.B2_diff_endpoints_subset_exterior13 ⟨hxB2, hxEndpoint⟩
        exact Set.disjoint_left.mp G.J13.disjoint_interior_exterior hx13 hxExterior13
    · have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inr hxB3
      have hxCompl13 : x ∈ G.J13.carrierᶜ := by
        rw [← G.J13.interior_union_exterior]
        exact Or.inl hx13
      exact hxCompl13 hxCarrier13
  have hsubsetUnion : G.J13.interiorRegion ⊆
      G.J23.interiorRegion ∪ G.J23.exteriorRegion := by
    rw [G.J23.interior_union_exterior]
    exact hsubsetCompl
  obtain ⟨y, hyB1, hyEndpoint⟩ := G.B1_interior_nonempty
  have hyExterior23 := G.B1_diff_endpoints_subset_exterior23 ⟨hyB1, hyEndpoint⟩
  have hyFrontier13 : y ∈ frontier G.J13.interiorRegion := by
    rw [G.J13.frontier_interiorRegion, G.carrier13]
    exact Or.inl hyB1
  have hyClosure : y ∈ closure
      (G.J23.exteriorRegion ∩ G.J13.interiorRegion) :=
    G.J23.isOpen_exteriorRegion.inter_closure
      ⟨hyExterior23, frontier_subset_closure hyFrontier13⟩
  obtain ⟨z, hz23, hz13⟩ := Set.Nonempty.of_closure ⟨y, hyClosure⟩
  exact G.J13.isConnected_interiorRegion.isPreconnected.subset_right_of_subset_union
    G.J23.isOpen_interiorRegion G.J23.isOpen_exteriorRegion
    G.J23.disjoint_interior_exterior hsubsetUnion ⟨z, hz13, hz23⟩

theorem interior23_subset_exterior13 :
    G.J23.interiorRegion ⊆ G.J13.exteriorRegion :=
  (G.swap12).interior13_subset_exterior23

/-- The two polygons cut off by the chord have disjoint interiors. -/
theorem disjoint_interior13_interior23 :
    Disjoint G.J13.interiorRegion G.J23.interiorRegion := by
  have hsubsetCompl : G.J13.interiorRegion ⊆ G.J23.carrierᶜ := by
    intro x hx13
    rw [G.carrier23]
    rintro (hxB2 | hxB3)
    · by_cases hxEndpoint : x ∈ ({G.P, G.Q} : Set Plane)
      · have hxB1 : x ∈ G.B1 := by
          rcases hxEndpoint with (rfl | rfl)
          · exact G.P_mem_B1
          · exact G.Q_mem_B1
        have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inl hxB1
        have hxCompl13 : x ∈ G.J13.carrierᶜ := by
          rw [← G.J13.interior_union_exterior]
          exact Or.inl hx13
        exact hxCompl13 hxCarrier13
      · have hxExterior13 := G.B2_diff_endpoints_subset_exterior13 ⟨hxB2, hxEndpoint⟩
        exact Set.disjoint_left.mp G.J13.disjoint_interior_exterior hx13 hxExterior13
    · have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inr hxB3
      have hxCompl13 : x ∈ G.J13.carrierᶜ := by
        rw [← G.J13.interior_union_exterior]
        exact Or.inl hx13
      exact hxCompl13 hxCarrier13
  have hsubsetUnion : G.J13.interiorRegion ⊆
      G.J23.interiorRegion ∪ G.J23.exteriorRegion := by
    rw [G.J23.interior_union_exterior]
    exact hsubsetCompl
  obtain ⟨y, hyB1, hyEndpoint⟩ := G.B1_interior_nonempty
  have hyExterior23 := G.B1_diff_endpoints_subset_exterior23 ⟨hyB1, hyEndpoint⟩
  have hyFrontier13 : y ∈ frontier G.J13.interiorRegion := by
    rw [G.J13.frontier_interiorRegion, G.carrier13]
    exact Or.inl hyB1
  have hyClosure : y ∈ closure
      (G.J23.exteriorRegion ∩ G.J13.interiorRegion) :=
    G.J23.isOpen_exteriorRegion.inter_closure
      ⟨hyExterior23, frontier_subset_closure hyFrontier13⟩
  obtain ⟨z, hz23, hz13⟩ := Set.Nonempty.of_closure ⟨y, hyClosure⟩
  have hallExterior : G.J13.interiorRegion ⊆ G.J23.exteriorRegion :=
    G.J13.isConnected_interiorRegion.isPreconnected.subset_right_of_subset_union
      G.J23.isOpen_interiorRegion G.J23.isOpen_exteriorRegion
      G.J23.disjoint_interior_exterior hsubsetUnion ⟨z, hz13, hz23⟩
  exact Set.disjoint_left.mpr fun x hx13 hx23 =>
    Set.disjoint_left.mp G.J23.disjoint_interior_exterior hx23 (hallExterior hx13)

/-- The two closed subdisks cut off by a proper chord meet exactly in that chord. -/
theorem closedRegion13_inter_closedRegion23 :
    G.J13.closedRegion ∩ G.J23.closedRegion = G.B3 := by
  rw [G.J13.closedRegion_eq_union, G.J23.closedRegion_eq_union,
    G.carrier13, G.carrier23]
  ext x
  constructor
  · rintro ⟨hx13, hx23⟩
    rcases hx13 with hxInt13 | hxB1 | hxB3
    · have hxExt23 := G.interior13_subset_exterior23 hxInt13
      rcases hx23 with hxInt23 | hxCarrier23
      · exact False.elim <|
          Set.disjoint_left.mp G.J23.disjoint_interior_exterior hxInt23 hxExt23
      · have hxCompl : x ∈ G.J23.carrierᶜ := by
          rw [← G.J23.interior_union_exterior]
          exact Or.inr hxExt23
        have hxCarrier23' : x ∈ G.J23.carrier := by
          rw [G.carrier23]
          exact hxCarrier23
        exact False.elim (hxCompl hxCarrier23')
    · rcases hx23 with hxInt23 | hxB2 | hxB3
      · have hxExt13 := G.interior23_subset_exterior13 hxInt23
        have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inl hxB1
        have hxCompl : x ∈ G.J13.carrierᶜ := by
          rw [← G.J13.interior_union_exterior]
          exact Or.inr hxExt13
        exact False.elim (hxCompl hxCarrier13)
      · have hxEndpoint : x ∈ ({G.P, G.Q} : Set Plane) := by
          rw [← G.B1_inter_B2]
          exact ⟨hxB1, hxB2⟩
        rcases hxEndpoint with (rfl | rfl)
        · exact G.P_mem_B3
        · exact G.Q_mem_B3
      · exact hxB3
    · exact hxB3
  · intro hxB3
    exact ⟨Or.inr (Or.inr hxB3), Or.inr (Or.inr hxB3)⟩

theorem interior12_diff_chord_subset :
    G.J12.interiorRegion \ G.B3 ⊆ G.J13.interiorRegion ∪ G.J23.interiorRegion := by
  intro x hx
  have hxNotB1 : x ∉ G.B1 := by
    intro hxB1
    have hxCarrier : x ∈ G.J12.carrier := by rw [G.carrier12]; exact Or.inl hxB1
    have hxCompl : x ∈ G.J12.carrierᶜ := by
      rw [← G.J12.interior_union_exterior]
      exact Or.inl hx.1
    exact hxCompl hxCarrier
  have hxNotB2 : x ∉ G.B2 := by
    intro hxB2
    have hxCarrier : x ∈ G.J12.carrier := by rw [G.carrier12]; exact Or.inr hxB2
    have hxCompl : x ∈ G.J12.carrierᶜ := by
      rw [← G.J12.interior_union_exterior]
      exact Or.inl hx.1
    exact hxCompl hxCarrier
  have hxNot13 : x ∉ G.J13.carrier := by
    rw [G.carrier13]
    rintro (hxB1 | hxB3)
    · exact hxNotB1 hxB1
    · exact hx.2 hxB3
  have hxNot23 : x ∉ G.J23.carrier := by
    rw [G.carrier23]
    rintro (hxB2 | hxB3)
    · exact hxNotB2 hxB2
    · exact hx.2 hxB3
  have hxNot12 : x ∉ G.J12.carrier := by
    rw [G.carrier12]
    rintro (hxB1 | hxB2)
    · exact hxNotB1 hxB1
    · exact hxNotB2 hxB2
  have hxSplit13 : x ∈ G.J13.interiorRegion ∪ G.J13.exteriorRegion := by
    rw [G.J13.interior_union_exterior]
    exact hxNot13
  have hxSplit23 : x ∈ G.J23.interiorRegion ∪ G.J23.exteriorRegion := by
    rw [G.J23.interior_union_exterior]
    exact hxNot23
  rcases hxSplit13 with hx13 | hx13
  · exact Or.inl hx13
  rcases hxSplit23 with hx23 | hx23
  · exact Or.inr hx23
  exfalso
  have hindex12 : G.J12.index x = 1 := by
    have hm : x ∈ G.J12.indexRegion 1 := by
      rw [← G.J12.interiorRegion_eq_indexRegion_one]
      exact hx.1
    exact hm.2
  have hindex13 : G.J13.index x = 0 := by
    have hm : x ∈ G.J13.indexRegion 0 := by
      rw [← G.J13.exteriorRegion_eq_indexRegion_zero]
      exact hx13
    exact hm.2
  have hindex23 : G.J23.index x = 0 := by
    have hm : x ∈ G.J23.indexRegion 0 := by
      rw [← G.J23.exteriorRegion_eq_indexRegion_zero]
      exact hx23
    exact hm.2
  have hparity := G.index_parity x hxNot12 hxNot13 hxNot23
  rw [hindex12, hindex13, hindex23] at hparity
  norm_num at hparity

/-- Moise Chapter 2, Theorem 8(2): the two chord polygons exactly fill the original closed
polygonal disk. -/
theorem closedRegion_eq_union :
    G.J12.closedRegion = G.J13.closedRegion ∪ G.J23.closedRegion := by
  rw [G.J12.closedRegion_eq_union, G.J13.closedRegion_eq_union,
    G.J23.closedRegion_eq_union]
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hxInterior | hxCarrier
    · by_cases hxB3 : x ∈ G.B3
      · left
        exact Or.inr (by rw [G.carrier13]; exact Or.inr hxB3)
      · rcases G.interior12_diff_chord_subset ⟨hxInterior, hxB3⟩ with hx13 | hx23
        · exact Or.inl (Or.inl hx13)
        · exact Or.inr (Or.inl hx23)
    · rw [G.carrier12] at hxCarrier
      rcases hxCarrier with hxB1 | hxB2
      · exact Or.inl (Or.inr (by rw [G.carrier13]; exact Or.inl hxB1))
      · exact Or.inr (Or.inr (by rw [G.carrier23]; exact Or.inl hxB2))
  · intro x
    rintro (hx13 | hx23)
    · rcases hx13 with hxInterior | hxCarrier
      · exact Or.inl (G.interior13_subset_interior12 hxInterior)
      · rw [G.carrier13] at hxCarrier
        rcases hxCarrier with hxB1 | hxB3
        · exact Or.inr (by rw [G.carrier12]; exact Or.inl hxB1)
        · rcases G.chord_subset hxB3 with hxEndpoint | hxInterior
          · exact Or.inr (G.endpoints_subset_carrier12 hxEndpoint)
          · exact Or.inl hxInterior
    · rcases hx23 with hxInterior | hxCarrier
      · exact Or.inl (G.interior23_subset_interior12 hxInterior)
      · rw [G.carrier23] at hxCarrier
        rcases hxCarrier with hxB2 | hxB3
        · exact Or.inr (by rw [G.carrier12]; exact Or.inr hxB2)
        · rcases G.chord_subset hxB3 with hxEndpoint | hxInterior
          · exact Or.inr (G.endpoints_subset_carrier12 hxEndpoint)
          · exact Or.inl hxInterior

namespace MeshCrosscut

variable {G : PolygonalTheta} {M : TriangleMesh} (C : G.MeshCrosscut M)

/-- Exchange the two sides of a realized mesh crosscut. -/
noncomputable def swap12 (C : G.MeshCrosscut M) : G.swap12.MeshCrosscut M where
  support_eq := C.support_eq
  chordEdge := C.chordEdge
  chordEdge_mem := C.chordEdge_mem
  chordVertices := C.chordVertices
  chordCarrier := C.chordCarrier

/-- A mesh triangle lies wholly on one side of a realized crosscut. -/
theorem triangle_interior_side (C : G.MeshCrosscut M) (T : M.Triangle) :
    interior (M.triangleCarrier T.1) ⊆ G.J13.interiorRegion ∨
      interior (M.triangleCarrier T.1) ⊆ G.J23.interiorRegion := by
  have htriangleSupport : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1
      (Set.subset_iUnion_of_subset T.2 subset_rfl)
  have hinside12 : interior (M.triangleCarrier T.1) ⊆ G.J12.interiorRegion := by
    rw [← G.J12.interior_closedRegion,
      ← PolygonalTheta.MeshCrosscut.support_eq C]
    exact interior_mono htriangleSupport
  have hdisjointChord :
      Disjoint (interior (M.triangleCarrier T.1)) G.B3 := by
    rw [← PolygonalTheta.MeshCrosscut.chordCarrier C]
    exact M.disjoint_interior_triangleCarrier_edgeCarrier T
      (PolygonalTheta.MeshCrosscut.chordEdge_mem C)
  have hsplit : interior (M.triangleCarrier T.1) ⊆
      G.J13.interiorRegion ∪ G.J23.interiorRegion := by
    intro p hp
    exact G.interior12_diff_chord_subset
      ⟨hinside12 hp, fun hpChord => Set.disjoint_left.mp hdisjointChord hp hpChord⟩
  obtain ⟨p, hp⟩ := M.interior_triangleCarrier_nonempty T
  rcases hsplit hp with hp13 | hp23
  · exact Or.inl <|
      (convex_convexHull ℝ _).interior.isPreconnected.subset_left_of_subset_union
        G.J13.isOpen_interiorRegion G.J23.isOpen_interiorRegion
        G.disjoint_interior13_interior23 hsplit ⟨p, hp, hp13⟩
  · exact Or.inr <|
      (convex_convexHull ℝ _).interior.isPreconnected.subset_right_of_subset_union
        G.J13.isOpen_interiorRegion G.J23.isOpen_interiorRegion
        G.disjoint_interior13_interior23 hsplit ⟨p, hp, hp23⟩

/-- Select the maximal triangles lying on the `J13` side of the crosscut. -/
noncomputable def side13Mesh (_ : G.MeshCrosscut M) : TriangleMesh := by
  classical
  exact M.restrictTriangles fun t =>
    (interior (M.triangleCarrier t) ∩ G.J13.interiorRegion).Nonempty

/-- Select the maximal triangles lying on the `J23` side of the crosscut. -/
noncomputable def side23Mesh (_ : G.MeshCrosscut M) : TriangleMesh := by
  classical
  exact M.restrictTriangles fun t =>
    (interior (M.triangleCarrier t) ∩ G.J23.interiorRegion).Nonempty

@[simp] theorem swap12_side13Mesh : C.swap12.side13Mesh = C.side23Mesh := rfl

@[simp] theorem swap12_side23Mesh : C.swap12.side23Mesh = C.side13Mesh := rfl

private theorem triangleCarrier_subset_side13 {t : Finset M.Vertex}
    (ht : t ∈ C.side13Mesh.triangles) :
    M.triangleCarrier t ⊆ G.J13.closedRegion := by
  classical
  have htM : t ∈ M.triangles :=
    (M.mem_restrictTriangles_triangles fun u =>
      (interior (M.triangleCarrier u) ∩ G.J13.interiorRegion).Nonempty).mp ht |>.1
  have hmeet : (interior (M.triangleCarrier t) ∩ G.J13.interiorRegion).Nonempty :=
    (M.mem_restrictTriangles_triangles fun u =>
      (interior (M.triangleCarrier u) ∩ G.J13.interiorRegion).Nonempty).mp ht |>.2
  let T : M.Triangle := ⟨t, htM⟩
  have hside : interior (M.triangleCarrier t) ⊆ G.J13.interiorRegion := by
    rcases triangle_interior_side C T with h13 | h23
    · exact h13
    · obtain ⟨p, hpT, hp13⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp G.disjoint_interior13_interior23
        hp13 (h23 hpT)
  rw [← M.closure_interior_triangleCarrier T, PolygonalCircle.closedRegion]
  exact closure_mono hside

private theorem triangleCarrier_subset_side23 {t : Finset M.Vertex}
    (ht : t ∈ C.side23Mesh.triangles) :
    M.triangleCarrier t ⊆ G.J23.closedRegion := by
  classical
  have htM : t ∈ M.triangles :=
    (M.mem_restrictTriangles_triangles fun u =>
      (interior (M.triangleCarrier u) ∩ G.J23.interiorRegion).Nonempty).mp ht |>.1
  have hmeet : (interior (M.triangleCarrier t) ∩ G.J23.interiorRegion).Nonempty :=
    (M.mem_restrictTriangles_triangles fun u =>
      (interior (M.triangleCarrier u) ∩ G.J23.interiorRegion).Nonempty).mp ht |>.2
  let T : M.Triangle := ⟨t, htM⟩
  have hside : interior (M.triangleCarrier t) ⊆ G.J23.interiorRegion := by
    rcases triangle_interior_side C T with h13 | h23
    · obtain ⟨p, hpT, hp23⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp G.disjoint_interior13_interior23
        (h13 hpT) hp23
    · exact h23
  rw [← M.closure_interior_triangleCarrier T, PolygonalCircle.closedRegion]
  exact closure_mono hside

/-- Restricting along a realized crosscut gives exactly the first closed polygonal subdisk. -/
theorem side13Mesh_support :
    C.side13Mesh.toPlaneComplex.support = G.J13.closedRegion := by
  classical
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨t, ht, hpt⟩ := hp
    exact C.triangleCarrier_subset_side13 ht hpt
  · rw [PolygonalCircle.closedRegion]
    apply closure_minimal _ C.side13Mesh.toPlaneComplex.isCompact_support.isClosed
    intro p hp13
    have hp12 : p ∈ G.J12.closedRegion := by
      rw [G.closedRegion_eq_union]
      exact Or.inl (by rw [G.J13.closedRegion_eq_union]; exact Or.inl hp13)
    have hpSupport : p ∈ M.toPlaneComplex.support := by
      rwa [PolygonalTheta.MeshCrosscut.support_eq C]
    rw [M.toPlaneComplex_support] at hpSupport
    simp only [Set.mem_iUnion] at hpSupport
    obtain ⟨t, ht, hpt⟩ := hpSupport
    let T : M.Triangle := ⟨t, ht⟩
    have hpClosure : p ∈ closure (interior (M.triangleCarrier t)) := by
      rw [M.closure_interior_triangleCarrier T]
      exact hpt
    have hpInterClosure : p ∈ closure
        (G.J13.interiorRegion ∩ interior (M.triangleCarrier t)) :=
      G.J13.isOpen_interiorRegion.inter_closure ⟨hp13, hpClosure⟩
    have hmeet :
        (interior (M.triangleCarrier t) ∩ G.J13.interiorRegion).Nonempty := by
      obtain ⟨q, hq13, hqt⟩ := Set.Nonempty.of_closure ⟨p, hpInterClosure⟩
      exact ⟨q, hqt, hq13⟩
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion_of_mem t <| Set.mem_iUnion_of_mem
      ((M.mem_restrictTriangles_triangles fun u =>
        (interior (M.triangleCarrier u) ∩ G.J13.interiorRegion).Nonempty).mpr
          ⟨ht, hmeet⟩) hpt

/-- Restricting along a realized crosscut gives exactly the second closed polygonal subdisk. -/
theorem side23Mesh_support :
    C.side23Mesh.toPlaneComplex.support = G.J23.closedRegion := by
  classical
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨t, ht, hpt⟩ := hp
    exact C.triangleCarrier_subset_side23 ht hpt
  · rw [PolygonalCircle.closedRegion]
    apply closure_minimal _ C.side23Mesh.toPlaneComplex.isCompact_support.isClosed
    intro p hp23
    have hp12 : p ∈ G.J12.closedRegion := by
      rw [G.closedRegion_eq_union]
      exact Or.inr (by rw [G.J23.closedRegion_eq_union]; exact Or.inl hp23)
    have hpSupport : p ∈ M.toPlaneComplex.support := by
      rwa [PolygonalTheta.MeshCrosscut.support_eq C]
    rw [M.toPlaneComplex_support] at hpSupport
    simp only [Set.mem_iUnion] at hpSupport
    obtain ⟨t, ht, hpt⟩ := hpSupport
    let T : M.Triangle := ⟨t, ht⟩
    have hpClosure : p ∈ closure (interior (M.triangleCarrier t)) := by
      rw [M.closure_interior_triangleCarrier T]
      exact hpt
    have hpInterClosure : p ∈ closure
        (G.J23.interiorRegion ∩ interior (M.triangleCarrier t)) :=
      G.J23.isOpen_interiorRegion.inter_closure ⟨hp23, hpClosure⟩
    have hmeet :
        (interior (M.triangleCarrier t) ∩ G.J23.interiorRegion).Nonempty := by
      obtain ⟨q, hq23, hqt⟩ := Set.Nonempty.of_closure ⟨p, hpInterClosure⟩
      exact ⟨q, hqt, hq23⟩
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion_of_mem t <| Set.mem_iUnion_of_mem
      ((M.mem_restrictTriangles_triangles fun u =>
        (interior (M.triangleCarrier u) ∩ G.J23.interiorRegion).Nonempty).mpr
          ⟨ht, hmeet⟩) hpt

theorem mem_side13Mesh_triangles_iff {t : Finset M.Vertex} :
    t ∈ C.side13Mesh.triangles ↔ t ∈ M.triangles ∧
      interior (M.triangleCarrier t) ⊆ G.J13.interiorRegion := by
  classical
  change t ∈ (M.restrictTriangles fun u =>
    (interior (M.triangleCarrier u) ∩ G.J13.interiorRegion).Nonempty).triangles ↔ _
  rw [M.mem_restrictTriangles_triangles]
  constructor
  · rintro ⟨ht, hmeet⟩
    let T : M.Triangle := ⟨t, ht⟩
    refine ⟨ht, ?_⟩
    rcases triangle_interior_side C T with h13 | h23
    · exact h13
    · obtain ⟨p, hpT, hp13⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp G.disjoint_interior13_interior23
        hp13 (h23 hpT)
  · rintro ⟨ht, hside⟩
    obtain ⟨p, hp⟩ := M.interior_triangleCarrier_nonempty ⟨t, ht⟩
    exact ⟨ht, p, hp, hside hp⟩

theorem mem_side23Mesh_triangles_iff {t : Finset M.Vertex} :
    t ∈ C.side23Mesh.triangles ↔ t ∈ M.triangles ∧
      interior (M.triangleCarrier t) ⊆ G.J23.interiorRegion := by
  classical
  change t ∈ (M.restrictTriangles fun u =>
    (interior (M.triangleCarrier u) ∩ G.J23.interiorRegion).Nonempty).triangles ↔ _
  rw [M.mem_restrictTriangles_triangles]
  constructor
  · rintro ⟨ht, hmeet⟩
    let T : M.Triangle := ⟨t, ht⟩
    refine ⟨ht, ?_⟩
    rcases triangle_interior_side C T with h13 | h23
    · obtain ⟨p, hpT, hp23⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp G.disjoint_interior13_interior23
        (h13 hpT) hp23
    · exact h23
  · rintro ⟨ht, hside⟩
    obtain ⟨p, hp⟩ := M.interior_triangleCarrier_nonempty ⟨t, ht⟩
    exact ⟨ht, p, hp, hside hp⟩

/-- The two restricted triangle sets partition the original mesh. -/
theorem side_triangles_union :
    C.side13Mesh.triangles ∪ C.side23Mesh.triangles = M.triangles := by
  classical
  ext t
  constructor
  · intro ht
    rcases Finset.mem_union.mp ht with ht13 | ht23
    · exact (C.mem_side13Mesh_triangles_iff.mp ht13).1
    · exact (C.mem_side23Mesh_triangles_iff.mp ht23).1
  · intro ht
    let T : M.Triangle := ⟨t, ht⟩
    rcases triangle_interior_side C T with h13 | h23
    · exact Finset.mem_union_left _ <| C.mem_side13Mesh_triangles_iff.mpr ⟨ht, h13⟩
    · exact Finset.mem_union_right _ <| C.mem_side23Mesh_triangles_iff.mpr ⟨ht, h23⟩

/-- No maximal triangle occurs on both sides of the crosscut. -/
theorem disjoint_side_triangles :
    Disjoint C.side13Mesh.triangles C.side23Mesh.triangles := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht13 ht23
  have h13 := (C.mem_side13Mesh_triangles_iff.mp ht13).2
  have h23 := (C.mem_side23Mesh_triangles_iff.mp ht23).2
  obtain ⟨p, hp⟩ := M.interior_triangleCarrier_nonempty
    ⟨t, (C.mem_side13Mesh_triangles_iff.mp ht13).1⟩
  exact Set.disjoint_left.mp G.disjoint_interior13_interior23 (h13 hp) (h23 hp)

theorem side13_triangles_nonempty : C.side13Mesh.triangles.Nonempty := by
  obtain ⟨p, hp⟩ := G.J13.isConnected_interiorRegion.nonempty
  have hpSupport : p ∈ C.side13Mesh.toPlaneComplex.support := by
    rw [C.side13Mesh_support, G.J13.closedRegion_eq_union]
    exact Or.inl hp
  rw [TriangleMesh.toPlaneComplex_support] at hpSupport
  simp only [Set.mem_iUnion] at hpSupport
  obtain ⟨t, ht, -⟩ := hpSupport
  exact ⟨t, ht⟩

theorem side23_triangles_nonempty : C.side23Mesh.triangles.Nonempty := by
  obtain ⟨p, hp⟩ := G.J23.isConnected_interiorRegion.nonempty
  have hpSupport : p ∈ C.side23Mesh.toPlaneComplex.support := by
    rw [C.side23Mesh_support, G.J23.closedRegion_eq_union]
    exact Or.inl hp
  rw [TriangleMesh.toPlaneComplex_support] at hpSupport
  simp only [Set.mem_iUnion] at hpSupport
  obtain ⟨t, ht, -⟩ := hpSupport
  exact ⟨t, ht⟩

/-- Each side of a proper realized crosscut has strictly fewer maximal triangles. -/
theorem card_side13_triangles_lt :
    C.side13Mesh.triangles.card < M.triangles.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro t ht
    exact (C.mem_side13Mesh_triangles_iff.mp ht).1
  · intro heq
    obtain ⟨t, ht23⟩ := C.side23_triangles_nonempty
    have htM := (C.mem_side23Mesh_triangles_iff.mp ht23).1
    have ht13 : t ∈ C.side13Mesh.triangles := by rwa [heq]
    exact Finset.disjoint_left.mp C.disjoint_side_triangles ht13 ht23

theorem card_side23_triangles_lt :
    C.side23Mesh.triangles.card < M.triangles.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro t ht
    exact (C.mem_side23Mesh_triangles_iff.mp ht).1
  · intro heq
    obtain ⟨t, ht13⟩ := C.side13_triangles_nonempty
    have htM := (C.mem_side13Mesh_triangles_iff.mp ht13).1
    have ht23 : t ∈ C.side23Mesh.triangles := by rwa [heq]
    exact Finset.disjoint_left.mp C.disjoint_side_triangles ht13 ht23

end MeshCrosscut

end PolygonalTheta

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
