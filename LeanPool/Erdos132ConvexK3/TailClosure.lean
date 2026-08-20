/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.UseSite
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-!
# Maximal-gap tail closure

This file ports the counting and elementary geometry in Lemma 4.1 of the
accepted convex `k = 3` paper proof.  The argument splits the neighbors of
the maximal-gap vertex at the first counterclockwise neighbor of `x + 3`:
the head has at most four offsets, while strict edge--diagonal comparison
and same-half-plane two-circle uniqueness leave at most two tail slots (one
under the strict anchor).
-/

namespace LeanPool.Erdos132ConvexK3

/-- Strict cyclic convexity makes the labelled boundary map injective. -/
theorem cyclic_strict_convex_injective
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (hn : 3 ≤ n) : Function.Injective P := by
  intro i j hij
  by_contra hne
  by_cases hnext : j = cyclicNext i
  · subst j
    exact (cyclic_strict_convex_boundary_points_ne hConvex hn i hij).elim
  · have hturn := hConvex i j (Ne.symm hne) hnext
    rw [← hij] at hturn
    simp [turn] at hturn

/-- Four increasing offsets in one turn form a strict convex quadrilateral. -/
theorem cyclic_strict_convex_quad_zero_offsets
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n)
    {b c d : ℕ} (hb : 0 < b) (hbc : b < c) (hcd : c < d) (hdn : d < n) :
    StrictConvexQuad
      (P base) (P (cyclicAdvance base b))
      (P (cyclicAdvance base c)) (P (cyclicAdvance base d)) := by
  have hzero : cyclicAdvance base 0 = base := cyclicAdvance_zero base
  have hperiodZero : cyclicAdvance base n = base := by
    simpa using cyclicAdvance_period base 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := cyclic_strict_convex_turn_unwrapped hConvex base
      (a := 0) (b := b) (c := c) hb hbc (by omega)
    simpa [hzero] using h
  · have h := cyclic_strict_convex_turn_unwrapped hConvex base
      (a := 0) (b := b) (c := d) hb (by omega) (by omega)
    simpa [hzero] using h
  · exact cyclic_strict_convex_turn_unwrapped hConvex base hbc hcd (by omega)
  · have h := cyclic_strict_convex_turn_unwrapped hConvex base
      (a := c) (b := d) (c := n) hcd hdn (by omega)
    simpa [hperiodZero] using h

/-- Every positive offset past the next vertex is in the common open
half-plane of the consecutive centers `base, base + 1`. -/
theorem cyclic_offset_in_left_open_half_plane
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n) {k : ℕ}
    (hk : 1 < k) (hkn : k < n) :
    InLeftOpenHalfPlane (P base) (P (cyclicAdvance base 1))
      (P (cyclicAdvance base k)) := by
  have h := cyclic_strict_convex_turn_unwrapped hConvex base
    (a := 0) (b := 1) (c := k) (by omega) hk (by omega)
  simpa [InLeftOpenHalfPlane] using h

/-- A fixed ordered pair of radii contributes at most one cyclic offset in
the open half-plane beyond the next vertex. -/
theorem cyclic_fixed_radii_offset_card_le_one
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (hn : 3 ≤ n) (base : Fin n)
    {S : Finset (Fin n)} {radiusBase radiusNext : ℝ}
    (hlower : ∀ k ∈ S, 1 < k.val)
    (hradii : ∀ k ∈ S,
      sqDist (P base) (P (cyclicAdvance base k.val)) = radiusBase ∧
      sqDist (P (cyclicAdvance base 1))
        (P (cyclicAdvance base k.val)) = radiusNext) :
    S.card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro k ell hk hell
  have hcenters : P base ≠ P (cyclicAdvance base 1) := by
    rw [cyclicAdvance_one_eq_next]
    exact cyclic_strict_convex_boundary_points_ne hConvex hn base
  have hkData := hradii k hk
  have hellData := hradii ell hell
  have hpoint : P (cyclicAdvance base k.val) =
      P (cyclicAdvance base ell.val) := by
    apply same_half_plane_two_circle_unique hcenters
    · exact hkData.1.trans hellData.1.symm
    · exact hkData.2.trans hellData.2.symm
    · exact cyclic_offset_in_left_open_half_plane hConvex base
        (hlower k hk) k.isLt
    · exact cyclic_offset_in_left_open_half_plane hConvex base
        (hlower ell hell) ell.isLt
  have hlabel : cyclicAdvance base k.val = cyclicAdvance base ell.val :=
    cyclic_strict_convex_injective hConvex hn hpoint
  have hkCast := fin_ofNat_val k
  have hellCast := fin_ofNat_val ell
  unfold cyclicAdvance at hlabel
  rw [hkCast, hellCast] at hlabel
  exact add_left_cancel hlabel

/-- A counterclockwise neighbor cannot pass the offset representing the
first clockwise neighbor. -/
theorem ccw_neighbor_offset_le_clockwise_boundary
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v k : Fin n}
    (hdegree : 0 < vertexDegree P d₁ d₂ d₃ v)
    (hk : k ∈ ccwNeighborOffsets P d₁ d₂ d₃ v) :
    k.val + (firstClockwiseNeighborOffset P d₁ d₂ d₃ v).val ≤ n := by
  classical
  have hcw := cwNeighborOffsets_nonempty_of_degree_pos hdegree
  have hkData := (Finset.mem_filter.mp hk).2
  let ell : Fin n := -k
  have hell0 : ell ≠ 0 := by
    dsimp [ell]
    exact neg_ne_zero.mpr hkData.1
  have hretreat : cyclicRetreat v ell.val = cyclicAdvance v k.val := by
    have hellCast := fin_ofNat_val ell
    have hkCast := fin_ofNat_val k
    unfold cyclicRetreat cyclicAdvance
    rw [hellCast, hkCast]
    dsimp [ell]
    abel
  have hellmem : ell ∈ cwNeighborOffsets P d₁ d₂ d₃ v := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hell0, by
      rw [hretreat]
      exact hkData.2⟩
  have hle : firstClockwiseNeighborOffset P d₁ d₂ d₃ v ≤ ell :=
    firstClockwiseNeighborOffset_le_of_mem hcw hellmem
  have hellVal : ell.val = n - k.val := by
    dsimp [ell]
    rw [Fin.val_neg, ite_eq_right hkData.1]
  have hleVal : (firstClockwiseNeighborOffset P d₁ d₂ d₃ v).val ≤ ell.val := hle
  rw [hellVal] at hleVal
  omega

/-- Equality of squared distances is equality of ordinary Euclidean
distances. -/
theorem euclideanDist_eq_of_sqDist_eq
    {a b c d : Point ℝ} (h : sqDist a b = sqDist c d) :
    euclideanDist a b = euclideanDist c d := by
  have habSq := euclideanDist_sq a b
  have hcdSq := euclideanDist_sq c d
  have habNonneg : 0 ≤ euclideanDist a b := dist_nonneg
  have hcdNonneg : 0 ≤ euclideanDist c d := dist_nonneg
  nlinarith

/-- The second strict edge--diagonal inequality, obtained by rotating the
four cyclic vertices once. -/
theorem edge_diagonal_inequality_rotated
    {x p u r : Point ℝ} (hquad : StrictConvexQuad x p u r) :
    euclideanDist p u + euclideanDist x r <
      euclideanDist p r + euclideanDist x u := by
  have hrot : StrictConvexQuad p u r x := by
    refine ⟨hquad.2.2.1, ?_, hquad.2.2.2, ?_⟩
    · have h := hquad.1
      rw [turn_cyclic x p u] at h
      exact h
    · have h := hquad.2.1
      rw [turn_cyclic x p r, turn_cyclic p r x] at h
      exact h
  have hed := edge_diagonal_inequality hrot
  simpa [euclideanDist, dist_comm] using hed

/-- If the anchor from the first center is no longer than the anchor from
the next center, strict edge--diagonal comparison reverses that order at a
point on the far arc. -/
theorem far_arc_strict_center_comparison
    {x p u r : Point ℝ} (hquad : StrictConvexQuad x p u r)
    (hanchor : sqDist x u ≤ sqDist p u) : sqDist x r < sqDist p r := by
  have hed := edge_diagonal_inequality_rotated hquad
  have hxuSq := euclideanDist_sq x u
  have hpuSq := euclideanDist_sq p u
  have hxrSq := euclideanDist_sq x r
  have hprSq := euclideanDist_sq p r
  have hxuNonneg : 0 ≤ euclideanDist x u := dist_nonneg
  have hpuNonneg : 0 ≤ euclideanDist p u := dist_nonneg
  have hxrNonneg : 0 ≤ euclideanDist x r := dist_nonneg
  have hprNonneg : 0 ≤ euclideanDist p r := dist_nonneg
  have hxuLe : euclideanDist x u ≤ euclideanDist p u := by
    nlinarith
  have hdist : euclideanDist x r < euclideanDist p r := by linarith
  nlinarith

/-- With exactly three ranked distances, a strict comparison has only the
three ordered radius slots used in the paper proof. -/
theorem strict_top_three_rank_slots
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {x p r : Fin n}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (hxr : TopThreeAdjacent P d₁ d₂ d₃ x r)
    (hpr : TopThreeAdjacent P d₁ d₂ d₃ p r)
    (hlt : sqDist (P x) (P r) < sqDist (P p) (P r)) :
    (sqDist (P x) (P r) = d₂ ∧ sqDist (P p) (P r) = d₁) ∨
      (sqDist (P x) (P r) = d₃ ∧ sqDist (P p) (P r) = d₁) ∨
      (sqDist (P x) (P r) = d₃ ∧ sqDist (P p) (P r) = d₂) := by
  have hd₃d₂ := hClasses.1
  have hd₂d₁ := hClasses.2.1
  rcases hxr.2 with hx₁ | hx₂ | hx₃
  · rcases hpr.2 with hp₁ | hp₂ | hp₃ <;> linarith
  · rcases hpr.2 with hp₁ | hp₂ | hp₃
    · exact Or.inl ⟨hx₂, hp₁⟩
    · linarith
    · linarith
  · rcases hpr.2 with hp₁ | hp₂ | hp₃
    · exact Or.inr (Or.inl ⟨hx₃, hp₁⟩)
    · exact Or.inr (Or.inr ⟨hx₃, hp₂⟩)
    · linarith

private theorem d3_d1_tail_slot_empty
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃)
    (p z : Fin n) (zoff : ℕ) (tail slot : Finset (Fin n))
    (hp : p = cyclicAdvance S.x 1)
    (hzoffEq : zoff = n -
      (firstClockwiseNeighborOffset P d₁ d₂ d₃ S.x).val)
    (hzoffn : zoff < n) (hzIndex : z = cyclicAdvance S.x zoff)
    (htailN : ∀ k ∈ tail, k ∈ ccwNeighborOffsets P d₁ d₂ d₃ S.x)
    (htailLower : ∀ k ∈ tail, 1 < k.val)
    (hslot : ∀ k ∈ slot, k ∈ tail ∧
      sqDist (P S.x) (P (cyclicAdvance S.x k.val)) = d₃ ∧
      sqDist (P p) (P (cyclicAdvance S.x k.val)) = d₁)
    (hxz : sqDist (P S.x) (P z) = d₃)
    (hpz : sqDist (P p) (P z) = d₂) : slot = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hkSlot := hslot k hk
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ S.x := by
    have := S.highDegree S.x
    omega
  have hkUpperRaw := ccw_neighbor_offset_le_clockwise_boundary hxdeg
    (htailN k hkSlot.1)
  have hkUpper : k.val ≤ zoff := by omega
  by_cases hkz : k.val = zoff
  · have hrz : cyclicAdvance S.x k.val = z := by
      rw [hzIndex, hkz]
    have hd₁d₂ : d₁ = d₂ := by
      calc
        d₁ = sqDist (P p) (P (cyclicAdvance S.x k.val)) := hkSlot.2.2.symm
        _ = sqDist (P p) (P z) := by rw [hrz]
        _ = d₂ := hpz
    linarith [S.classes.2.1]
  · have hkltz : k.val < zoff := by omega
    have hquad := cyclic_strict_convex_quad_zero_offsets S.convex S.x
      (b := 1) (c := k.val) (d := zoff) (by omega)
      (htailLower k hkSlot.1) hkltz hzoffn
    have hed := edge_diagonal_inequality_rotated hquad
    rw [← hzIndex] at hed
    have hed' : euclideanDist (P p) (P (cyclicAdvance S.x k.val)) +
        euclideanDist (P S.x) (P z) <
        euclideanDist (P p) (P z) +
          euclideanDist (P S.x) (P (cyclicAdvance S.x k.val)) := by
      simpa [hp] using hed
    have hsameD₃ : euclideanDist (P S.x) (P z) =
        euclideanDist (P S.x) (P (cyclicAdvance S.x k.val)) :=
      euclideanDist_eq_of_sqDist_eq (hxz.trans hkSlot.2.1.symm)
    have hdist : euclideanDist (P p) (P (cyclicAdvance S.x k.val)) <
        euclideanDist (P p) (P z) := by linarith
    have hprSq := euclideanDist_sq (P p) (P (cyclicAdvance S.x k.val))
    have hpzSq := euclideanDist_sq (P p) (P z)
    have hprNonneg : 0 ≤ euclideanDist (P p)
        (P (cyclicAdvance S.x k.val)) := dist_nonneg
    have hpzNonneg : 0 ≤ euclideanDist (P p) (P z) := dist_nonneg
    have hsquared : sqDist (P p) (P (cyclicAdvance S.x k.val)) <
        sqDist (P p) (P z) := by nlinarith
    rw [hkSlot.2.2, hpz] at hsquared
    linarith [S.classes.2.1]

/-- **Maximal-gap tail lemma (paper Lemma 4.1).**  Suppose `p = x + 1`,
`u` is the first counterclockwise neighbor of `x + 3`, and `z` is the first
clockwise neighbor of `x`.  Under the three displayed ladder colors, an
`xu = d₁` anchor gives degree at most six, while `xu = d₂` gives degree at
most five. -/
theorem maximal_gap_tail_degree_bounds
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃)
    (hpu : sqDist (P (cyclicAdvance S.x 1))
      (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3))) = d₁)
    (hxz : sqDist (P S.x)
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₃)
    (hpz : sqDist (P (cyclicAdvance S.x 1))
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₂) :
    (sqDist (P S.x)
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3))) = d₁ →
      vertexDegree P d₁ d₂ d₃ S.x ≤ 6) ∧
    (sqDist (P S.x)
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3))) = d₂ →
      vertexDegree P d₁ d₂ d₃ S.x ≤ 5) := by
  classical
  let p := cyclicAdvance S.x 1
  let t := cyclicAdvance S.x 3
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ t
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ S.x
  let gx := firstNeighborGap P d₁ d₂ d₃ S.x
  let hx := (firstClockwiseNeighborOffset P d₁ d₂ d₃ S.x).val
  let gt := firstNeighborGap P d₁ d₂ d₃ t
  let uoff := 3 + gt
  let zoff := n - hx
  change sqDist (P p) (P u) = d₁ at hpu
  change sqDist (P S.x) (P z) = d₃ at hxz
  change sqDist (P p) (P z) = d₂ at hpz
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (S.highDegree S.x)
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ S.x := by
    have := S.highDegree S.x
    omega
  have htdeg : 0 < vertexDegree P d₁ d₂ d₃ t := by
    have := S.highDegree t
    omega
  have hgxpos : 0 < gx := firstNeighborGap_pos_of_degree_pos hxdeg
  have hgtpos : 0 < gt := firstNeighborGap_pos_of_degree_pos htdeg
  have hhxpos : 0 < hx :=
    firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  have hgtgx : gt ≤ gx := by
    simpa [gt, gx] using S.maximalGap t
  have hxbudget : gx + hx + 6 ≤ n := by
    simpa [gx, hx] using first_neighbor_gap_cw_budget (v := S.x) (S.highDegree S.x)
  have huoffn : uoff < n := by
    dsimp [uoff]
    omega
  have huoffpos : 1 < uoff := by
    dsimp [uoff]
    omega
  have huz : uoff < zoff := by
    dsimp [uoff, zoff]
    omega
  have hzoffn : zoff < n := by
    dsimp [zoff]
    omega
  have huIndex : u = cyclicAdvance S.x uoff := by
    change cyclicAdvance (cyclicAdvance S.x 3) gt = cyclicAdvance S.x uoff
    rw [cyclicAdvance_add]
  have hzIndex : z = cyclicAdvance S.x zoff := by
    change cyclicRetreat S.x hx = cyclicAdvance S.x zoff
    exact cyclicRetreat_eq_advance_complement S.x hhxpos (by omega)
  let g := firstNeighborOffset P d₁ d₂ d₃ S.x
  let N := ccwNeighborOffsets P d₁ d₂ d₃ S.x
  let head := N.filter fun k ↦ k.val ≤ uoff
  let tail := N.filter fun k ↦ uoff < k.val
  let upper : Fin n := ⟨uoff, huoffn⟩
  have hccw := ccwNeighborOffsets_nonempty_of_degree_pos hxdeg
  have hheadSub : head ⊆ Finset.Icc g upper := by
    intro k hk
    have hkData := Finset.mem_filter.mp hk
    exact Finset.mem_Icc.mpr
      ⟨firstNeighborOffset_le_of_mem hccw hkData.1, hkData.2⟩
  have hheadRaw := Finset.card_le_card hheadSub
  rw [Fin.card_Icc] at hheadRaw
  have hgval : g.val = gx := rfl
  have hupperval : upper.val = uoff := rfl
  rw [hgval, hupperval] at hheadRaw
  have hheadCard : head.card ≤ 4 := by omega
  have hNSub : N ⊆ head ∪ tail := by
    intro k hk
    by_cases hle : k.val ≤ uoff
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, hle⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, by omega⟩)
  have hdegreeEq : N.card = vertexDegree P d₁ d₂ d₃ S.x := by
    simpa [N] using ccwNeighborOffsets_card_eq_vertexDegree P d₁ d₂ d₃ S.x
  let slot21 := tail.filter fun k ↦
    sqDist (P S.x) (P (cyclicAdvance S.x k.val)) = d₂ ∧
      sqDist (P p) (P (cyclicAdvance S.x k.val)) = d₁
  let slot31 := tail.filter fun k ↦
    sqDist (P S.x) (P (cyclicAdvance S.x k.val)) = d₃ ∧
      sqDist (P p) (P (cyclicAdvance S.x k.val)) = d₁
  let slot32 := tail.filter fun k ↦
    sqDist (P S.x) (P (cyclicAdvance S.x k.val)) = d₃ ∧
      sqDist (P p) (P (cyclicAdvance S.x k.val)) = d₂
  have htailSub (hanchor : sqDist (P S.x) (P u) ≤ sqDist (P p) (P u)) :
      tail ⊆ slot21 ∪ slot31 ∪ slot32 := by
    intro k hk
    have hkTail := Finset.mem_filter.mp hk
    have hkN := hkTail.1
    have hquad := cyclic_strict_convex_quad_zero_offsets S.convex S.x
      (b := 1) (c := uoff) (d := k.val) (by omega) huoffpos hkTail.2 k.isLt
    have hanchor' :
        sqDist (P S.x) (P (cyclicAdvance S.x uoff)) ≤
          sqDist (P (cyclicAdvance S.x 1)) (P (cyclicAdvance S.x uoff)) := by
      rw [← huIndex]
      simpa [p] using hanchor
    have hcompare := far_arc_strict_center_comparison hquad hanchor'
    have hxr : TopThreeAdjacent P d₁ d₂ d₃ S.x
        (cyclicAdvance S.x k.val) :=
      (Finset.mem_filter.mp hkN).2.2
    have hpr : TopThreeAdjacent P d₁ d₂ d₃ p
        (cyclicAdvance S.x k.val) := by
      apply top_three_adjacent_of_strictly_longer S.classes hxr
      simpa [p] using hcompare
    have hslots := strict_top_three_rank_slots S.classes hxr hpr (by
      simpa [p] using hcompare)
    rcases hslots with h21 | h31 | h32
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, h21⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, h31⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, h32⟩)
  have hslot21Card : slot21.card ≤ 1 := by
    apply cyclic_fixed_radii_offset_card_le_one S.convex (by omega) S.x
    · intro k hk
      have hkTail := (Finset.mem_filter.mp hk).1
      have hkLower := (Finset.mem_filter.mp hkTail).2
      omega
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
  have hslot32Card : slot32.card ≤ 1 := by
    apply cyclic_fixed_radii_offset_card_le_one S.convex (by omega) S.x
    · intro k hk
      have hkTail := (Finset.mem_filter.mp hk).1
      have hkLower := (Finset.mem_filter.mp hkTail).2
      omega
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
  have hslot31Empty : slot31 = ∅ := by
    apply d3_d1_tail_slot_empty S p z zoff tail slot31
    · rfl
    · rfl
    · exact hzoffn
    · exact hzIndex
    · intro k hk
      exact (Finset.mem_filter.mp hk).1
    · intro k hk
      have hkLower := (Finset.mem_filter.mp hk).2
      omega
    · intro k hk
      exact Finset.mem_filter.mp hk
    · exact hxz
    · exact hpz
  constructor
  · intro hxu
    change sqDist (P S.x) (P u) = d₁ at hxu
    have hanchor : sqDist (P S.x) (P u) ≤ sqDist (P p) (P u) := by
      rw [hxu, hpu]
    have htailSub' := htailSub hanchor
    rw [hslot31Empty] at htailSub'
    simp only [Finset.union_empty] at htailSub'
    have htailCard : tail.card ≤ 2 := by
      calc
        tail.card ≤ (slot21 ∪ slot32).card := Finset.card_le_card htailSub'
        _ ≤ slot21.card + slot32.card := Finset.card_union_le _ _
        _ ≤ 2 := by omega
    calc
      vertexDegree P d₁ d₂ d₃ S.x = N.card := hdegreeEq.symm
      _ ≤ (head ∪ tail).card := Finset.card_le_card hNSub
      _ ≤ head.card + tail.card := Finset.card_union_le _ _
      _ ≤ 6 := by omega
  · intro hxu
    change sqDist (P S.x) (P u) = d₂ at hxu
    have hanchor : sqDist (P S.x) (P u) ≤ sqDist (P p) (P u) := by
      rw [hxu, hpu]
      exact le_of_lt S.classes.2.1
    have hslot21Empty : slot21 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      have hkSlot := Finset.mem_filter.mp hk
      have hkTail := Finset.mem_filter.mp hkSlot.1
      have hquad := cyclic_strict_convex_quad_zero_offsets S.convex S.x
        (b := 1) (c := uoff) (d := k.val) (by omega) huoffpos hkTail.2 k.isLt
      have hed := edge_diagonal_inequality_rotated hquad
      rw [← huIndex] at hed
      have hed' : euclideanDist (P p) (P u) +
          euclideanDist (P S.x) (P (cyclicAdvance S.x k.val)) <
          euclideanDist (P p) (P (cyclicAdvance S.x k.val)) +
            euclideanDist (P S.x) (P u) := by
        simpa [p] using hed
      have hd₁eq : euclideanDist (P p) (P u) =
          euclideanDist (P p) (P (cyclicAdvance S.x k.val)) :=
        euclideanDist_eq_of_sqDist_eq (hpu.trans hkSlot.2.2.symm)
      have hd₂eq : euclideanDist (P S.x) (P (cyclicAdvance S.x k.val)) =
          euclideanDist (P S.x) (P u) :=
        euclideanDist_eq_of_sqDist_eq (hkSlot.2.1.trans hxu.symm)
      linarith
    have htailSub' := htailSub hanchor
    rw [hslot21Empty, hslot31Empty] at htailSub'
    simp only [Finset.empty_union] at htailSub'
    have htailCard' : tail.card ≤ slot32.card := Finset.card_le_card htailSub'
    have htailCard : tail.card ≤ 1 := htailCard'.trans hslot32Card
    calc
      vertexDegree P d₁ d₂ d₃ S.x = N.card := hdegreeEq.symm
      _ ≤ (head ∪ tail).card := Finset.card_le_card hNSub
      _ ≤ head.card + tail.card := Finset.card_union_le _ _
      _ ≤ 5 := by omega

/-- The four vertices `x, x+1, u, z` used by the tail lemma occur in strict
cyclic order at every maximal-gap degree-seven use site. -/
theorem erlv_x_p_u_z_strict_convex_quad
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) :
    StrictConvexQuad
      (P S.x) (P (cyclicAdvance S.x 1))
      (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3)))
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) := by
  let gx := firstNeighborGap P d₁ d₂ d₃ S.x
  let hx := (firstClockwiseNeighborOffset P d₁ d₂ d₃ S.x).val
  let t := cyclicAdvance S.x 3
  let gt := firstNeighborGap P d₁ d₂ d₃ t
  let uoff := 3 + gt
  let zoff := n - hx
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ t
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ S.x
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ S.x := by
    have := S.highDegree S.x
    omega
  have htdeg : 0 < vertexDegree P d₁ d₂ d₃ t := by
    have := S.highDegree t
    omega
  have hgtpos : 0 < gt := firstNeighborGap_pos_of_degree_pos htdeg
  have hhxpos : 0 < hx :=
    firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  have hgtgx : gt ≤ gx := by
    simpa [gt, gx] using S.maximalGap t
  have hxbudget : gx + hx + 6 ≤ n := by
    simpa [gx, hx] using first_neighbor_gap_cw_budget (v := S.x) (S.highDegree S.x)
  have huoffn : uoff < n := by
    dsimp [uoff]
    omega
  have huoffpos : 1 < uoff := by
    dsimp [uoff]
    omega
  have huz : uoff < zoff := by
    dsimp [uoff, zoff]
    omega
  have hzoffn : zoff < n := by
    dsimp [zoff]
    omega
  have huIndex : u = cyclicAdvance S.x uoff := by
    change cyclicAdvance (cyclicAdvance S.x 3) gt = cyclicAdvance S.x uoff
    rw [cyclicAdvance_add]
  have hzIndex : z = cyclicAdvance S.x zoff := by
    change cyclicRetreat S.x hx = cyclicAdvance S.x zoff
    exact cyclicRetreat_eq_advance_complement S.x hhxpos (by omega)
  have hquad := cyclic_strict_convex_quad_zero_offsets S.convex S.x
    (b := 1) (c := uoff) (d := zoff) (by omega) huoffpos huz hzoffn
  rw [← huIndex, ← hzIndex] at hquad
  exact hquad

/-- If the opposite sides `pu,zx` have ranks `d₁,d₃` and the diagonal
`pz` has rank `d₂`, strict ED forces the other diagonal `xu` into
`d₁ ∨ d₂`. -/
theorem d1_d3_opposite_sides_force_xu_top_two
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {x p u z : Fin n}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (hquad : StrictConvexQuad (P x) (P p) (P u) (P z))
    (hxzAdj : TopThreeAdjacent P d₁ d₂ d₃ x z)
    (hpu : sqDist (P p) (P u) = d₁)
    (hxz : sqDist (P x) (P z) = d₃)
    (hpz : sqDist (P p) (P z) = d₂) :
    sqDist (P x) (P u) = d₁ ∨ sqDist (P x) (P u) = d₂ := by
  have hed := edge_diagonal_inequality_rotated hquad
  have hpuSq := euclideanDist_sq (P p) (P u)
  have hpzSq := euclideanDist_sq (P p) (P z)
  have hpuNonneg : 0 ≤ euclideanDist (P p) (P u) := dist_nonneg
  have hpzNonneg : 0 ≤ euclideanDist (P p) (P z) := dist_nonneg
  have hpzLtPu : euclideanDist (P p) (P z) < euclideanDist (P p) (P u) := by
    nlinarith [hClasses.2.1]
  have hxzLtXu : euclideanDist (P x) (P z) < euclideanDist (P x) (P u) := by
    linarith
  have hxzSq := euclideanDist_sq (P x) (P z)
  have hxuSq := euclideanDist_sq (P x) (P u)
  have hxzNonneg : 0 ≤ euclideanDist (P x) (P z) := dist_nonneg
  have hxuNonneg : 0 ≤ euclideanDist (P x) (P u) := dist_nonneg
  have hsqGrow : sqDist (P x) (P z) < sqDist (P x) (P u) := by nlinarith
  have hxuAdj := top_three_adjacent_of_strictly_longer hClasses hxzAdj hsqGrow
  rcases hxuAdj.2 with h₁ | h₂ | h₃
  · exact Or.inl h₁
  · exact Or.inr h₂
  · linarith

/-- The rigid `(2,2)` ladders supply every hypothesis of the tail lemma and
force `xu` into one of its two clauses. -/
theorem erlv_case22_tail_rank_data
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (h22 : S.Case22) :
    let z := firstClockwiseNeighbor P d₁ d₂ d₃ S.x
    let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃
      (cyclicAdvance S.x 3)
    sqDist (P (cyclicAdvance S.x 1)) (P u) = d₁ ∧
      sqDist (P S.x) (P z) = d₃ ∧
      sqDist (P (cyclicAdvance S.x 1)) (P z) = d₂ ∧
      (sqDist (P S.x) (P u) = d₁ ∨ sqDist (P S.x) (P u) = d₂) := by
  dsimp only
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (S.highDegree S.x)
  have hB : S.pair.first.leftMoves = 0 := by
    have hBudget := S.pair.first.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case22] at h22
    omega
  have hBeta : S.pair.second.rightMoves = 0 := by
    have hBudget := S.pair.second.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case22] at h22
    omega
  have hFirstPath : K3CoverSequence P
      (firstClockwiseNeighbor P d₁ d₂ d₃ S.x) S.x 0 2 :=
    hB ▸ h22.1 ▸ S.pair.first.path
  have hSecondPath : K3CoverSequence P (cyclicAdvance S.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance S.x 3)) 2 0 :=
    h22.2 ▸ hBeta ▸ S.pair.second.path
  have hFirstRanks := right_right_cover_rank_ladder S.classes
    S.first_start_adjacent hFirstPath
  have hSecondRanks := left_left_cover_rank_ladder S.classes
    S.second_start_adjacent hSecondPath
  have hretreatTwo :
      cyclicRetreat (cyclicAdvance S.x 3) 2 = cyclicAdvance S.x 1 := by
    simpa using cyclicRetreat_advance S.x (k := 3) (m := 2) (by omega) (by omega)
  have hpu : sqDist (P (cyclicAdvance S.x 1))
      (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3))) = d₁ := by
    simpa only [hretreatTwo] using hSecondRanks.2.2
  have hxz : sqDist (P S.x)
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₃ := by
    simpa only [sqDist_comm] using hFirstRanks.1
  have hpz : sqDist (P (cyclicAdvance S.x 1))
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₂ := by
    simpa only [sqDist_comm] using hFirstRanks.2.1
  have hquad := erlv_x_p_u_z_strict_convex_quad S
  have hxzAdj : TopThreeAdjacent P d₁ d₂ d₃ S.x
      (firstClockwiseNeighbor P d₁ d₂ d₃ S.x) :=
    topThreeAdjacent_symm S.first_start_adjacent
  have hxu := d1_d3_opposite_sides_force_xu_top_two
    S.classes hquad hxzAdj hpu hxz hpz
  exact ⟨hpu, hxz, hpz, hxu⟩

/-- The maximal-gap tail lemma closes the whole rigid `(2,2)` branch. -/
theorem erlv_at_vertex_case22_impossible_of_tail :
    ErLVAtVertexCase22Impossible := by
  intro n _ P d₁ d₂ d₃ S h22
  rcases erlv_case22_tail_rank_data S h22 with ⟨hpu, hxz, hpz, hxu⟩
  have hbounds := maximal_gap_tail_degree_bounds S hpu hxz hpz
  rcases hxu with hxuD₁ | hxuD₂
  · have hdegree := hbounds.1 hxuD₁
    have hhigh := S.highDegree S.x
    omega
  · have hdegree := hbounds.2 hxuD₂
    have hhigh := S.highDegree S.x
    omega

/-- Session-9 obligation 5/8, discharged by unconditional branch closure. -/
theorem erlv_at_vertex_case22_zt_d1_impossible_of_tail :
    ErLVAtVertexCase22ZTD1Impossible := by
  intro n _ P d₁ d₂ d₃ S h22 _
  exact erlv_at_vertex_case22_impossible_of_tail P d₁ d₂ d₃ S h22

/-- Session-9 obligation 6/8, discharged by unconditional branch closure. -/
theorem erlv_at_vertex_case22_zt_d2_impossible_of_tail :
    ErLVAtVertexCase22ZTD2Impossible := by
  intro n _ P d₁ d₂ d₃ S h22 _
  exact erlv_at_vertex_case22_impossible_of_tail P d₁ d₂ d₃ S h22

/-- Session-9 obligation 7/8, discharged by unconditional branch closure. -/
theorem erlv_at_vertex_case22_xu_d1_impossible_of_tail :
    ErLVAtVertexCase22XUD1Impossible := by
  intro n _ P d₁ d₂ d₃ S h22 _
  exact erlv_at_vertex_case22_impossible_of_tail P d₁ d₂ d₃ S h22

/-- Session-9 obligation 8/8, discharged by unconditional branch closure. -/
theorem erlv_at_vertex_case22_xu_d2_impossible_of_tail :
    ErLVAtVertexCase22XUD2Impossible := by
  intro n _ P d₁ d₂ d₃ S h22 _
  exact erlv_at_vertex_case22_impossible_of_tail P d₁ d₂ d₃ S h22

namespace K3CoverSequence

/-- A path with one left and one right cover has made two strict rank
increases, regardless of their order, so it ends in `d₁`. -/
theorem one_left_one_right_end_at_d1
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hStart : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (path : K3CoverSequence P i j 1 1) :
    sqDist (P (cyclicRetreat i 1)) (P (cyclicAdvance j 1)) = d₁ := by
  cases path with
  | left hLeft tail =>
      cases tail with
      | right hRight _ =>
          have hMid := left_cover_top_three_adjacent hClasses hStart hLeft
          have hEnd := right_cover_top_three_adjacent hClasses hMid hRight
          exact two_covers_end_at_d₁ hClasses hStart hMid hEnd hLeft hRight
  | right hRight tail =>
      cases tail with
      | left hLeft _ =>
          have hMid := right_cover_top_three_adjacent hClasses hStart hRight
          have hEnd := left_cover_top_three_adjacent hClasses hMid hLeft
          exact two_covers_end_at_d₁ hClasses hStart hMid hEnd hRight hLeft

end K3CoverSequence

/-- The tail lemma closes the `(1,2)` shared-tip subcase whose other
terminal edge has color `d₂`. -/
theorem erlv_at_vertex_case12_other_d2_impossible_of_tail :
    ErLVAtVertexCase12OtherD2Impossible := by
  intro n _ P d₁ d₂ d₃ S h12 hOther
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ S.x
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃
    (cyclicAdvance S.x 3)
  let p := cyclicAdvance S.x 1
  change sqDist
    (P (cyclicRetreat z S.pair.first.leftMoves)) (P p) = d₂ at hOther
  have hBLe : S.pair.first.leftMoves ≤ 1 := by
    have hBudget := S.pair.first.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case12] at h12
    omega
  have hBZero : S.pair.first.leftMoves = 0 := by
    by_contra hne
    have hBOne : S.pair.first.leftMoves = 1 := by omega
    have hPath : K3CoverSequence P z S.x 1 1 := by
      simpa only [z, hBOne, h12.1] using S.pair.first.path
    have hEnd := K3CoverSequence.one_left_one_right_end_at_d1
      S.classes S.first_start_adjacent hPath
    rw [hBOne] at hOther
    linarith [S.classes.2.1]
  rw [hBZero, cyclicRetreat_zero] at hOther
  have hpz : sqDist (P p) (P z) = d₂ := by
    simpa only [sqDist_comm] using hOther
  have hFirstPath : K3CoverSequence P z S.x 0 1 := by
    simpa only [z, hBZero, h12.1] using S.pair.first.path
  have hCover : IsRightCover P z S.x := by
    cases hFirstPath with
    | right h _ => exact h
  have hxz : sqDist (P S.x) (P z) = d₃ := by
    have hStart := S.first_start_adjacent
    change sqDist (P z) (P S.x) < sqDist (P z) (P p) at hCover
    rcases hStart.2 with h₁ | h₂ | h₃
    · linarith [S.classes.2.1]
    · linarith
    · simpa only [sqDist_comm] using h₃
  have hData := erlv_case12_shared_tip_rank_data S h12
  have hpu : sqDist (P p) (P u) = d₁ := by
    simpa [p, u] using hData.1
  have hquad := erlv_x_p_u_z_strict_convex_quad S
  have hxzAdj : TopThreeAdjacent P d₁ d₂ d₃ S.x z := by
    simpa [z] using topThreeAdjacent_symm S.first_start_adjacent
  have hxu := d1_d3_opposite_sides_force_xu_top_two
    S.classes (by simpa [p, u, z] using hquad) hxzAdj hpu hxz hpz
  have hbounds := maximal_gap_tail_degree_bounds S
    (by simpa [p, u] using hpu)
    (by simpa [z] using hxz)
    (by simpa [p, z] using hpz)
  rcases hxu with hxuD₁ | hxuD₂
  · have hdegree := hbounds.1 (by simpa [u] using hxuD₁)
    have hhigh := S.highDegree S.x
    omega
  · have hdegree := hbounds.2 (by simpa [u] using hxuD₂)
    have hhigh := S.highDegree S.x
    omega

/-- Session-11 boundary: after the maximal-gap tail port, only the three
shared-tip colors `(1,2)-d₁`, `(2,1)-d₁`, and `(2,1)-d₂` remain. -/
theorem erlv_at_vertex_exceptional_branches_impossible_of_remaining_three
    (h12D1 : ErLVAtVertexCase12OtherD1Impossible)
    (h21D1 : ErLVAtVertexCase21OtherD1Impossible)
    (h21D2 : ErLVAtVertexCase21OtherD2Impossible) :
    ErLVAtVertexExceptionalBranchesImpossible :=
  erlv_at_vertex_exceptional_branches_impossible_of_color_cases
    h12D1 erlv_at_vertex_case12_other_d2_impossible_of_tail
    h21D1 h21D2
    erlv_at_vertex_case22_zt_d1_impossible_of_tail
    erlv_at_vertex_case22_zt_d2_impossible_of_tail
    erlv_at_vertex_case22_xu_d1_impossible_of_tail
    erlv_at_vertex_case22_xu_d2_impossible_of_tail

end LeanPool.Erdos132ConvexK3
