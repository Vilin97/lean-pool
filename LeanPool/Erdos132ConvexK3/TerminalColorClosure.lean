/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.TailClosure
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-!
# Terminal-color closure at the maximal-gap use site

This file ports Sections 6--8 of the accepted convex `k = 3` paper proof.
It closes the three terminal-color obligations left after `TailClosure.lean`:
`(1,2)-d₁`, `(2,1)-d₁`, and `(2,1)-d₂`.
-/

namespace LeanPool.Erdos132ConvexK3

/-- Strict order of squared Euclidean distances is strict order of distances. -/
theorem euclideanDist_lt_of_sqDist_lt
    {a b c d : Point ℝ} (h : sqDist a b < sqDist c d) :
    euclideanDist a b < euclideanDist c d := by
  have habSq := euclideanDist_sq a b
  have hcdSq := euclideanDist_sq c d
  have habNonneg : 0 ≤ euclideanDist a b := dist_nonneg
  have hcdNonneg : 0 ≤ euclideanDist c d := dist_nonneg
  nlinarith

/-- Weak order of squared Euclidean distances is weak order of distances. -/
theorem euclideanDist_le_of_sqDist_le
    {a b c d : Point ℝ} (h : sqDist a b ≤ sqDist c d) :
    euclideanDist a b ≤ euclideanDist c d := by
  have habSq := euclideanDist_sq a b
  have hcdSq := euclideanDist_sq c d
  have habNonneg : 0 ≤ euclideanDist a b := dist_nonneg
  have hcdNonneg : 0 ≤ euclideanDist c d := dist_nonneg
  nlinarith

/-- Strict order of Euclidean distances is strict order of their squares. -/
theorem sqDist_lt_of_euclideanDist_lt
    {a b c d : Point ℝ} (h : euclideanDist a b < euclideanDist c d) :
    sqDist a b < sqDist c d := by
  have habSq := euclideanDist_sq a b
  have hcdSq := euclideanDist_sq c d
  have habNonneg : 0 ≤ euclideanDist a b := dist_nonneg
  have hcdNonneg : 0 ≤ euclideanDist c d := dist_nonneg
  nlinarith

/-- Four increasing offsets, not necessarily starting at zero, form a
strict convex quadrilateral. -/
theorem cyclic_strict_convex_quad_offsets
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n)
    {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hdn : d < n) :
    StrictConvexQuad
      (P (cyclicAdvance base a)) (P (cyclicAdvance base b))
      (P (cyclicAdvance base c)) (P (cyclicAdvance base d)) := by
  have h := cyclic_strict_convex_quad_zero_offsets hConvex
    (cyclicAdvance base a) (b := b - a) (c := c - a) (d := d - a)
    (by omega) (by omega) (by omega) (by omega)
  rw [cyclicAdvance_add, cyclicAdvance_add, cyclicAdvance_add] at h
  have hab' : a + (b - a) = b := by omega
  have hac' : a + (c - a) = c := by omega
  have had' : a + (d - a) = d := by omega
  simpa only [hab', hac', had'] using h

/-- Every later offset lies in the inward open half-plane of any preceding
consecutive boundary pair. -/
theorem cyclic_offset_in_consecutive_left_open_half_plane
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n) {a k : ℕ}
    (hak : a + 1 < k) (hkn : k < n) :
    InLeftOpenHalfPlane
      (P (cyclicAdvance base a)) (P (cyclicAdvance base (a + 1)))
      (P (cyclicAdvance base k)) := by
  have h := cyclic_offset_in_left_open_half_plane hConvex
    (cyclicAdvance base a) (k := k - a) (by omega) (by omega)
  rw [cyclicAdvance_add, cyclicAdvance_add] at h
  have ha1 : a + 1 = a + (1 : ℕ) := rfl
  have hak' : a + (k - a) = k := by omega
  simpa only [ha1, hak'] using h

/-- Equal radii from the first vertex of a strict convex quadrilateral are
strictly ordered from its consecutive second vertex.  This is the kernel
form of paper Lemma 3.4. -/
theorem equal_radius_arc_strict_order
    {a b r₁ r₂ : Point ℝ}
    (hquad : StrictConvexQuad a b r₁ r₂)
    (heq : sqDist a r₁ = sqDist a r₂) :
    sqDist b r₁ < sqDist b r₂ := by
  have hed := edge_diagonal_inequality_rotated hquad
  have harEq : euclideanDist a r₁ = euclideanDist a r₂ :=
    euclideanDist_eq_of_sqDist_eq heq
  have hdist : euclideanDist b r₁ < euclideanDist b r₂ := by
    simpa only [harEq, add_lt_add_iff_right] using hed
  exact sqDist_lt_of_euclideanDist_lt hdist

/-- Fixed radii from two centers determine at most one cyclic offset when
all candidate points lie in the same open half-plane. -/
theorem fixed_radii_offset_card_le_one
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hInjective : Function.Injective P) (base a b : Fin n)
    (hab : P a ≠ P b) {S : Finset (Fin n)} {radiusA radiusB : ℝ}
    (hhalf : ∀ k ∈ S, InLeftOpenHalfPlane (P a) (P b)
      (P (cyclicAdvance base k.val)))
    (hradii : ∀ k ∈ S,
      sqDist (P a) (P (cyclicAdvance base k.val)) = radiusA ∧
      sqDist (P b) (P (cyclicAdvance base k.val)) = radiusB) :
    S.card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro k ell hk hell
  have hkData := hradii k hk
  have hellData := hradii ell hell
  have hpoint : P (cyclicAdvance base k.val) =
      P (cyclicAdvance base ell.val) := by
    apply same_half_plane_two_circle_unique hab
    · exact hkData.1.trans hellData.1.symm
    · exact hkData.2.trans hellData.2.symm
    · exact hhalf k hk
    · exact hhalf ell hell
  have hlabel : cyclicAdvance base k.val = cyclicAdvance base ell.val :=
    hInjective hpoint
  have hkCast := fin_ofNat_val k
  have hellCast := fin_ofNat_val ell
  unfold cyclicAdvance at hlabel
  rw [hkCast, hellCast] at hlabel
  exact add_left_cancel hlabel

/-- Two allowed fixed-radius pairs give at most two cyclic offsets. -/
theorem two_fixed_radius_pairs_card_le_two
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hInjective : Function.Injective P) (base a b : Fin n)
    (hab : P a ≠ P b) {S : Finset (Fin n)}
    {a₁ b₁ a₂ b₂ : ℝ}
    (hhalf : ∀ k ∈ S, InLeftOpenHalfPlane (P a) (P b)
      (P (cyclicAdvance base k.val)))
    (hpairs : ∀ k ∈ S,
      (sqDist (P a) (P (cyclicAdvance base k.val)) = a₁ ∧
        sqDist (P b) (P (cyclicAdvance base k.val)) = b₁) ∨
      (sqDist (P a) (P (cyclicAdvance base k.val)) = a₂ ∧
        sqDist (P b) (P (cyclicAdvance base k.val)) = b₂)) :
    S.card ≤ 2 := by
  classical
  let A := S.filter fun k ↦
    sqDist (P a) (P (cyclicAdvance base k.val)) = a₁ ∧
      sqDist (P b) (P (cyclicAdvance base k.val)) = b₁
  let B := S.filter fun k ↦
    sqDist (P a) (P (cyclicAdvance base k.val)) = a₂ ∧
      sqDist (P b) (P (cyclicAdvance base k.val)) = b₂
  have hcover : S ⊆ A ∪ B := by
    intro k hk
    rcases hpairs k hk with hkA | hkB
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, hkA⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hkB⟩)
  have hA : A.card ≤ 1 := by
    apply fixed_radii_offset_card_le_one hInjective base a b hab
    · intro k hk
      exact hhalf k (Finset.mem_filter.mp hk).1
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
  have hB : B.card ≤ 1 := by
    apply fixed_radii_offset_card_le_one hInjective base a b hab
    · intro k hk
      exact hhalf k (Finset.mem_filter.mp hk).1
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
  calc
    S.card ≤ (A ∪ B).card := Finset.card_le_card hcover
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

/-- Three allowed fixed-radius pairs give at most three cyclic offsets. -/
theorem three_fixed_radius_pairs_card_le_three
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hInjective : Function.Injective P) (base a b : Fin n)
    (hab : P a ≠ P b) {S : Finset (Fin n)}
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (hhalf : ∀ k ∈ S, InLeftOpenHalfPlane (P a) (P b)
      (P (cyclicAdvance base k.val)))
    (hpairs : ∀ k ∈ S,
      (sqDist (P a) (P (cyclicAdvance base k.val)) = a₁ ∧
        sqDist (P b) (P (cyclicAdvance base k.val)) = b₁) ∨
      (sqDist (P a) (P (cyclicAdvance base k.val)) = a₂ ∧
        sqDist (P b) (P (cyclicAdvance base k.val)) = b₂) ∨
      (sqDist (P a) (P (cyclicAdvance base k.val)) = a₃ ∧
        sqDist (P b) (P (cyclicAdvance base k.val)) = b₃)) :
    S.card ≤ 3 := by
  classical
  let A := S.filter fun k ↦
    sqDist (P a) (P (cyclicAdvance base k.val)) = a₁ ∧
      sqDist (P b) (P (cyclicAdvance base k.val)) = b₁
  let B := S.filter fun k ↦
    sqDist (P a) (P (cyclicAdvance base k.val)) = a₂ ∧
      sqDist (P b) (P (cyclicAdvance base k.val)) = b₂
  let C := S.filter fun k ↦
    sqDist (P a) (P (cyclicAdvance base k.val)) = a₃ ∧
      sqDist (P b) (P (cyclicAdvance base k.val)) = b₃
  have hcover : S ⊆ A ∪ B ∪ C := by
    intro k hk
    rcases hpairs k hk with hkA | hkB | hkC
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, hkA⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hkB⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hkC⟩)
  have hA : A.card ≤ 1 := by
    apply fixed_radii_offset_card_le_one hInjective base a b hab
    · intro k hk
      exact hhalf k (Finset.mem_filter.mp hk).1
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
  have hB : B.card ≤ 1 := by
    apply fixed_radii_offset_card_le_one hInjective base a b hab
    · intro k hk
      exact hhalf k (Finset.mem_filter.mp hk).1
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
  have hC : C.card ≤ 1 := by
    apply fixed_radii_offset_card_le_one hInjective base a b hab
    · intro k hk
      exact hhalf k (Finset.mem_filter.mp hk).1
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
  calc
    S.card ≤ (A ∪ B ∪ C).card := Finset.card_le_card hcover
    _ ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    _ ≤ (A.card + B.card) + C.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 3 := by omega

/-- Offset of the first counterclockwise neighbor of `x+3`, measured from
the selected maximal-gap vertex `x`. -/
noncomputable def erlvUOffset
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) : ℕ :=
  3 + firstNeighborGap P d₁ d₂ d₃ (cyclicAdvance S.x 3)

/-- Offset of the first clockwise neighbor of `x`, measured
counterclockwise from `x`. -/
noncomputable def erlvZOffset
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) : ℕ :=
  n - (firstClockwiseNeighborOffset P d₁ d₂ d₃ S.x).val

/-- The maximal-gap budget locates `u` and `z` with three spare boundary
sides between them. -/
theorem erlv_u_z_offset_data
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) :
    3 < erlvUOffset S ∧ erlvUOffset S + 3 ≤ erlvZOffset S ∧
      erlvZOffset S < n ∧
      firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3) = cyclicAdvance S.x (erlvUOffset S) ∧
      firstClockwiseNeighbor P d₁ d₂ d₃ S.x =
        cyclicAdvance S.x (erlvZOffset S) := by
  let gx := firstNeighborGap P d₁ d₂ d₃ S.x
  let hx := (firstClockwiseNeighborOffset P d₁ d₂ d₃ S.x).val
  let gt := firstNeighborGap P d₁ d₂ d₃ (cyclicAdvance S.x 3)
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ S.x := by
    have := S.highDegree S.x
    omega
  have htdeg : 0 < vertexDegree P d₁ d₂ d₃ (cyclicAdvance S.x 3) := by
    have := S.highDegree (cyclicAdvance S.x 3)
    omega
  have hgtpos : 0 < gt := firstNeighborGap_pos_of_degree_pos htdeg
  have hhxpos : 0 < hx :=
    firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  have hgtgx : gt ≤ gx := by
    simpa [gt, gx] using S.maximalGap (cyclicAdvance S.x 3)
  have hbudget : gx + hx + 6 ≤ n := by
    simpa [gx, hx] using first_neighbor_gap_cw_budget (v := S.x)
      (S.highDegree S.x)
  have hzlt : erlvZOffset S < n := by
    dsimp [erlvZOffset, hx]
    omega
  have huIndex : firstCounterclockwiseNeighbor P d₁ d₂ d₃
      (cyclicAdvance S.x 3) = cyclicAdvance S.x (erlvUOffset S) := by
    change cyclicAdvance (cyclicAdvance S.x 3) gt =
      cyclicAdvance S.x (3 + gt)
    rw [cyclicAdvance_add]
  have hzIndex : firstClockwiseNeighbor P d₁ d₂ d₃ S.x =
      cyclicAdvance S.x (erlvZOffset S) := by
    change cyclicRetreat S.x hx = cyclicAdvance S.x (n - hx)
    exact cyclicRetreat_eq_advance_complement S.x hhxpos (by omega)
  exact ⟨by dsimp [erlvUOffset]; omega,
    by dsimp [erlvUOffset, erlvZOffset, gx, hx, gt]; omega,
    hzlt, huIndex, hzIndex⟩

/-- At most `4+β` neighbors of the maximal-gap vertex occur through the
offset `u+β`, for `β≤1`. -/
theorem erlv_x_head_card_le
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (β : ℕ) (hβ : β ≤ 1) :
    ((ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter fun k ↦
      k.val ≤ erlvUOffset S + β).card ≤ 4 + β := by
  classical
  let gx := firstNeighborGap P d₁ d₂ d₃ S.x
  let g := firstNeighborOffset P d₁ d₂ d₃ S.x
  let N := ccwNeighborOffsets P d₁ d₂ d₃ S.x
  let m := erlvUOffset S + β
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ S.x := by
    have := S.highDegree S.x
    omega
  have hccw := ccwNeighborOffsets_nonempty_of_degree_pos hxdeg
  have hm_lt_n : m < n := by
    have hdata := erlv_u_z_offset_data S
    dsimp [m]
    omega
  let upper : Fin n := ⟨m, hm_lt_n⟩
  have hsub : N.filter (fun k ↦ k.val ≤ m) ⊆ Finset.Icc g upper := by
    intro k hk
    have hkData := Finset.mem_filter.mp hk
    exact Finset.mem_Icc.mpr
      ⟨firstNeighborOffset_le_of_mem hccw hkData.1, hkData.2⟩
  have hcard : (N.filter (fun k ↦ k.val ≤ m)).card ≤ m + 1 - gx := by
    calc
      (N.filter (fun k ↦ k.val ≤ m)).card ≤ (Finset.Icc g upper).card :=
        Finset.card_le_card hsub
      _ = m + 1 - gx := by
        simp [Fin.card_Icc, upper, g, gx, firstNeighborGap]
  have hgtgx := S.maximalGap (cyclicAdvance S.x 3)
  have hbound : (N.filter (fun k ↦ k.val ≤ m)).card ≤ 4 + β := by
    apply hcard.trans
    dsimp [m, erlvUOffset, gx] at hgtgx ⊢
    omega
  simpa [N, m, erlvUOffset] using hbound

/-- A bound on the offsets after `u+β` combines with the maximal-gap head
count to bound the degree of `x`. -/
theorem erlv_x_degree_le_of_tail_card
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (β tailCap : ℕ)
    (hβ : β ≤ 1)
    (htail : ((ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter fun k ↦
      erlvUOffset S + β < k.val).card ≤ tailCap) :
    vertexDegree P d₁ d₂ d₃ S.x ≤ 4 + β + tailCap := by
  classical
  let N := ccwNeighborOffsets P d₁ d₂ d₃ S.x
  let head := N.filter fun k ↦ k.val ≤ erlvUOffset S + β
  let tail := N.filter fun k ↦ erlvUOffset S + β < k.val
  have hcover : N ⊆ head ∪ tail := by
    intro k hk
    by_cases hle : k.val ≤ erlvUOffset S + β
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, hle⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hk, by omega⟩)
  have hhead : head.card ≤ 4 + β := by
    simpa [head, N] using erlv_x_head_card_le S β hβ
  have htail' : tail.card ≤ tailCap := by simpa [tail, N] using htail
  have hdegree : N.card = vertexDegree P d₁ d₂ d₃ S.x := by
    simpa [N] using ccwNeighborOffsets_card_eq_vertexDegree P d₁ d₂ d₃ S.x
  calc
    vertexDegree P d₁ d₂ d₃ S.x = N.card := hdegree.symm
    _ ≤ (head ∪ tail).card := Finset.card_le_card hcover
    _ ≤ head.card + tail.card := Finset.card_union_le _ _
    _ ≤ 4 + β + tailCap := by omega

/-- The first-neighbor `u` has offset `uoff-1` from `p=x+1`. -/
noncomputable def erlvPUOffset
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) : ℕ := erlvUOffset S - 1

theorem erlv_p_u_offset_data
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) :
    2 < erlvPUOffset S ∧ erlvPUOffset S < n ∧
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance S.x 3) =
        cyclicAdvance (cyclicAdvance S.x 1) (erlvPUOffset S) := by
  have hOffsets := erlv_u_z_offset_data S
  have huoffn : erlvUOffset S < n := by omega
  have hadd : 1 + erlvPUOffset S = erlvUOffset S := by
    dsimp [erlvPUOffset]
    omega
  refine ⟨by dsimp [erlvPUOffset]; omega, by dsimp [erlvPUOffset]; omega, ?_⟩
  rw [cyclicAdvance_add, hadd]
  exact hOffsets.2.2.2.1

/-- Splitting all `p`-neighbor offsets at `u` converts two open-arc bounds
and the single endpoint bound into a degree bound. -/
theorem erlv_p_degree_le_of_arc_cards
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃)
    (leftCap tipCap rightCap : ℕ)
    (hleft : ((ccwNeighborOffsets P d₁ d₂ d₃ (cyclicAdvance S.x 1)).filter
      fun k ↦ k.val < erlvPUOffset S).card ≤ leftCap)
    (htip : ((ccwNeighborOffsets P d₁ d₂ d₃ (cyclicAdvance S.x 1)).filter
      fun k ↦ k.val = erlvPUOffset S).card ≤ tipCap)
    (hright : ((ccwNeighborOffsets P d₁ d₂ d₃ (cyclicAdvance S.x 1)).filter
      fun k ↦ erlvPUOffset S < k.val).card ≤ rightCap) :
    vertexDegree P d₁ d₂ d₃ (cyclicAdvance S.x 1) ≤
      leftCap + tipCap + rightCap := by
  classical
  let p := cyclicAdvance S.x 1
  let N := ccwNeighborOffsets P d₁ d₂ d₃ p
  let left := N.filter fun k ↦ k.val < erlvPUOffset S
  let tip := N.filter fun k ↦ k.val = erlvPUOffset S
  let right := N.filter fun k ↦ erlvPUOffset S < k.val
  have hcover : N ⊆ (left ∪ tip) ∪ right := by
    intro k hk
    rcases lt_trichotomy k.val (erlvPUOffset S) with hlt | heq | hgt
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, hlt⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, heq⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hgt⟩)
  have hdegree : N.card = vertexDegree P d₁ d₂ d₃ p := by
    simpa [N] using ccwNeighborOffsets_card_eq_vertexDegree P d₁ d₂ d₃ p
  calc
    vertexDegree P d₁ d₂ d₃ (cyclicAdvance S.x 1) = N.card := by
      simpa [p] using hdegree.symm
    _ ≤ ((left ∪ tip) ∪ right).card := Finset.card_le_card hcover
    _ ≤ (left ∪ tip).card + right.card := Finset.card_union_le _ _
    _ ≤ (left.card + tip.card) + right.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ leftCap + tipCap + rightCap := by
      have hleft' : left.card ≤ leftCap := by simpa [left, N, p] using hleft
      have htip' : tip.card ≤ tipCap := by simpa [tip, N, p] using htip
      have hright' : right.card ≤ rightCap := by simpa [right, N, p] using hright
      omega

private theorem high_degree_le_six_false
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (v : Fin n)
    (hdegree : vertexDegree P d₁ d₂ d₃ v ≤ 6) : False := by
  have hhigh := S.highDegree v
  omega

private structure Case21D2Prepared
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) : Prop where
  tu : sqDist (P (cyclicAdvance S.x 3))
    (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
      (cyclicAdvance S.x 3))) = d₃
  xz : sqDist (P S.x)
    (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₃
  pz : sqDist (P (cyclicAdvance S.x 1))
    (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₂
  qz : sqDist (P (cyclicAdvance S.x 2))
    (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₁
  qu : sqDist (P (cyclicAdvance S.x 2))
    (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
      (cyclicAdvance S.x 3))) = d₂
  pu_le : sqDist (P (cyclicAdvance S.x 1))
    (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
      (cyclicAdvance S.x 3))) ≤ d₂
  p_ne_u : cyclicAdvance S.x 1 ≠
    firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance S.x 3)
  uoff_lt : erlvUOffset S < n
  u_index : firstCounterclockwiseNeighbor P d₁ d₂ d₃
    (cyclicAdvance S.x 3) = cyclicAdvance S.x (erlvUOffset S)
  pu_index : firstCounterclockwiseNeighbor P d₁ d₂ d₃
    (cyclicAdvance S.x 3) =
      cyclicAdvance (cyclicAdvance S.x 1) (erlvPUOffset S)
  points_injective : Function.Injective P
  x_p_ne : P S.x ≠ P (cyclicAdvance S.x 1)
  left_half : ∀ k ∈
      (ccwNeighborOffsets P d₁ d₂ d₃ (cyclicAdvance S.x 1)).filter
        (fun k ↦ k.val < erlvPUOffset S),
      InLeftOpenHalfPlane (P S.x) (P (cyclicAdvance S.x 1))
        (P (cyclicAdvance (cyclicAdvance S.x 1) k.val))
  right_card : ((ccwNeighborOffsets P d₁ d₂ d₃
      (cyclicAdvance S.x 1)).filter
        fun k ↦ erlvPUOffset S < k.val).card ≤ 3
  tip_card : ((ccwNeighborOffsets P d₁ d₂ d₃
      (cyclicAdvance S.x 1)).filter
        fun k ↦ k.val = erlvPUOffset S).card ≤ 1
  xtail_card : sqDist (P S.x)
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3))) ≤
      sqDist (P (cyclicAdvance S.x 1))
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3))) →
    ((ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
      fun k ↦ erlvUOffset S < k.val).card ≤ 2

private theorem case12_bzero_false_of_tail_card_le_two
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃)
    (htail : ((ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
      fun k ↦ erlvUOffset S < k.val).card ≤ 2) : False := by
  have hdegree := erlv_x_degree_le_of_tail_card S 0 2 (by omega) htail
  have hhigh := S.highDegree S.x
  omega

private theorem case12_bzero_d3_d1_tail_card_le_two
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (uoff zoff : ℕ)
    (huoff3 : 3 < uoff) (hzoffn : zoff < n)
    (huIndex : firstCounterclockwiseNeighbor P d₁ d₂ d₃
      (cyclicAdvance S.x 3) = cyclicAdvance S.x uoff)
    (hzIndex : firstClockwiseNeighbor P d₁ d₂ d₃ S.x =
      cyclicAdvance S.x zoff)
    (hpu : sqDist (P (cyclicAdvance S.x 1))
      (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3))) = d₁)
    (hqu : sqDist (P (cyclicAdvance S.x 2))
      (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3))) = d₂)
    (hpz : sqDist (P (cyclicAdvance S.x 1))
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₁)
    (hqz : sqDist (P (cyclicAdvance S.x 2))
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₁)
    (hxuD₁ : sqDist (P S.x)
      (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3))) = d₁)
    (hxzD₃ : sqDist (P S.x)
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₃)
    (htailUpper : ∀ k ∈ (ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
        (fun k ↦ uoff < k.val), k.val ≤ zoff)
    (htailHalf : ∀ k ∈ (ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
        (fun k ↦ uoff < k.val),
      InLeftOpenHalfPlane (P S.x) (P (cyclicAdvance S.x 1))
        (P (cyclicAdvance S.x k.val))) :
    ((ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
      fun k ↦ uoff < k.val).card ≤ 2 := by
  classical
  let x := S.x
  let p := cyclicAdvance x 1
  let q := cyclicAdvance x 2
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3)
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
  let tail := (ccwNeighborOffsets P d₁ d₂ d₃ x).filter
    fun k ↦ uoff < k.val
  have hInjective : Function.Injective P :=
    cyclic_strict_convex_injective S.convex (by
      exact eight_le_card_of_degree_seven (S.highDegree S.x) |>.trans' (by omega))
  have hxp : P x ≠ P p := by
    have h := cyclic_strict_convex_boundary_points_ne S.convex (by
      exact eight_le_card_of_degree_seven (S.highDegree S.x) |>.trans' (by omega)) x
    simpa [p, cyclicAdvance_one_eq_next] using h
  have htailHalf' : ∀ k ∈ tail,
      InLeftOpenHalfPlane (P x) (P p) (P (cyclicAdvance x k.val)) := by
    simpa [tail, x, p] using htailHalf
  refine two_fixed_radius_pairs_card_le_two hInjective x x p hxp
    (a₁ := d₃) (b₁ := d₁) (a₂ := d₃) (b₂ := d₂) htailHalf' ?_
  intro k hk
  have hkData := Finset.mem_filter.mp hk
  have hRAdj := (Finset.mem_filter.mp hkData.1).2.2
  have hquadRaw := cyclic_strict_convex_quad_offsets S.convex x
    (a := 0) (b := 1) (c := uoff) (d := k.val)
    (by omega) (by omega) (by omega) k.isLt
  rw [← huIndex] at hquadRaw
  have hquad : StrictConvexQuad (P x) (P p) (P u)
      (P (cyclicAdvance x k.val)) := by
    simpa [x, p, u] using hquadRaw
  have hanchor : sqDist (P x) (P u) ≤ sqDist (P p) (P u) := by
    rw [show sqDist (P x) (P u) = d₁ by simpa [x, u] using hxuD₁,
      show sqDist (P p) (P u) = d₁ by simpa [x, p, u] using hpu]
  have hcompare := far_arc_strict_center_comparison hquad hanchor
  have hpAdj := top_three_adjacent_of_strictly_longer S.classes hRAdj hcompare
  have hslots := strict_top_three_rank_slots S.classes hRAdj hpAdj hcompare
  rcases hslots with h21 | h31 | h32
  · exfalso
    have hkUpper : k.val ≤ zoff := by
      simpa [tail, x] using htailUpper k hk
    have hkNeZ : k.val ≠ zoff := by
      intro hkz
      have hRz : cyclicAdvance x k.val = z := by
        dsimp [x, z]
        rw [hzIndex, hkz]
      have : d₂ = d₃ := by
        calc
          d₂ = sqDist (P x) (P (cyclicAdvance x k.val)) := h21.1.symm
          _ = sqDist (P x) (P z) := by rw [hRz]
          _ = d₃ := by simpa [x, z] using hxzD₃
      linarith [S.classes.1]
    have hklt : k.val < zoff := by omega
    have hquadPUA := cyclic_strict_convex_quad_offsets S.convex x
      (a := 1) (b := 2) (c := uoff) (d := k.val)
      (by omega) (by omega) (by omega) k.isLt
    rw [← huIndex] at hquadPUA
    have hradial₁ := equal_radius_arc_strict_order hquadPUA (by
      simpa [x, p, u] using hpu.trans h21.2.symm)
    have hquadPAZ := cyclic_strict_convex_quad_offsets S.convex x
      (a := 1) (b := 2) (c := k.val) (d := zoff)
      (by omega) (by omega) hklt hzoffn
    rw [← hzIndex] at hquadPAZ
    have hradial₂ := equal_radius_arc_strict_order hquadPAZ (by
      simpa [x, p, z] using h21.2.trans hpz.symm)
    have hqRNe : q ≠ cyclicAdvance x k.val :=
      cyclicAdvance_ne_of_lt x (by omega) k.isLt (by omega)
    have hbound := top_three_class_bounds_of_ne S.classes hqRNe
    have hltD₁ : sqDist (P q) (P (cyclicAdvance x k.val)) < d₁ := by
      rw [← show sqDist (P q) (P z) = d₁ by simpa [x, q, z] using hqz]
      simpa [q] using hradial₂
    have hleD₂ := hbound.2.1 hltD₁
    have hD₂lt : d₂ < sqDist (P q) (P (cyclicAdvance x k.val)) := by
      rw [← show sqDist (P q) (P u) = d₂ by simpa [x, q, u] using hqu]
      simpa [q] using hradial₁
    linarith
  · exact Or.inl h31
  · exact Or.inr h32

private theorem case12_tail_offset_geometry
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) :
    (∀ k ∈ (ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
        (fun k ↦ erlvUOffset S < k.val), k.val ≤ erlvZOffset S) ∧
      ∀ k ∈ (ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
        (fun k ↦ erlvUOffset S < k.val),
        InLeftOpenHalfPlane (P S.x) (P (cyclicAdvance S.x 1))
          (P (cyclicAdvance S.x k.val)) := by
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ S.x := by
    have := S.highDegree S.x
    omega
  constructor
  · intro k hk
    have hraw := ccw_neighbor_offset_le_clockwise_boundary hxdeg
      (Finset.mem_filter.mp hk).1
    dsimp [erlvZOffset]
    omega
  · intro k hk
    have h := cyclic_offset_in_left_open_half_plane S.convex S.x
      (k := k.val) (by
        have hU := (erlv_u_z_offset_data S).1
        have hkLower := (Finset.mem_filter.mp hk).2
        omega) k.isLt
    simpa using h

/-- Section 6.1: the no-outer-move part of terminal color `(1,2)-d₁`. -/
theorem erlv_case12_other_d1_bzero_impossible
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (h12 : S.Case12)
    (hOther : sqDist
      (P (cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)
        S.pair.first.leftMoves))
      (P (cyclicAdvance S.x 1)) = d₁)
    (hBZero : S.pair.first.leftMoves = 0) : False := by
  classical
  let x := S.x
  let p := cyclicAdvance x 1
  let q := cyclicAdvance x 2
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3)
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
  let uoff := erlvUOffset S
  let zoff := erlvZOffset S
  let N := ccwNeighborOffsets P d₁ d₂ d₃ x
  let tail := N.filter fun k ↦ uoff < k.val
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (S.highDegree S.x)
  have hOffsets := erlv_u_z_offset_data S
  have huoff3 : 3 < uoff := by simpa [uoff] using hOffsets.1
  have huz : uoff + 3 ≤ zoff := by simpa [uoff, zoff] using hOffsets.2.1
  have hzoffn : zoff < n := by simpa [zoff] using hOffsets.2.2.1
  have huoffn : uoff < n := by omega
  have huIndex : u = cyclicAdvance x uoff := by
    simpa [u, x, uoff] using hOffsets.2.2.2.1
  have hzIndex : z = cyclicAdvance x zoff := by
    simpa [z, x, zoff] using hOffsets.2.2.2.2
  have hData := erlv_case12_shared_tip_rank_data S h12
  have hpu : sqDist (P p) (P u) = d₁ := by
    simpa [p, u, x] using hData.1
  have hqu : sqDist (P q) (P u) = d₂ := by
    simpa [q, u, x] using hData.2.2
  have hpz : sqDist (P p) (P z) = d₁ := by
    rw [hBZero, cyclicRetreat_zero] at hOther
    simpa only [p, z, x, sqDist_comm] using hOther
  have hquNe : q ≠ u := by
    rw [huIndex]
    exact cyclicAdvance_ne_of_lt x (by omega) huoffn (by omega)
  have hquAdj : TopThreeAdjacent P d₁ d₂ d₃ q u :=
    ⟨hquNe, Or.inr (Or.inl hqu)⟩
  have hquadPQUZ : StrictConvexQuad (P p) (P q) (P u) (P z) := by
    have hquad := cyclic_strict_convex_quad_offsets S.convex x
      (a := 1) (b := 2) (c := uoff) (d := zoff)
      (by omega) (by omega) (by omega) hzoffn
    rw [← huIndex, ← hzIndex] at hquad
    simpa [p, q] using hquad
  have hqz : sqDist (P q) (P z) = d₁ := by
    have hed := edge_diagonal_inequality_rotated hquadPQUZ
    have hpsEq : euclideanDist (P p) (P z) = euclideanDist (P p) (P u) :=
      euclideanDist_eq_of_sqDist_eq (hpz.trans hpu.symm)
    have hdist : euclideanDist (P q) (P u) < euclideanDist (P q) (P z) := by
      linarith
    have hgrow : sqDist (P q) (P u) < sqDist (P q) (P z) :=
      sqDist_lt_of_euclideanDist_lt hdist
    have hqzAdj := top_three_adjacent_of_strictly_longer S.classes hquAdj hgrow
    rcases hqzAdj.2 with h₁ | h₂ | h₃
    · exact h₁
    · linarith [S.classes.2.1]
    · linarith [S.classes.1]
  have hFirstPath : K3CoverSequence P z x 0 1 := by
    simpa only [z, x, hBZero, h12.1] using S.pair.first.path
  have hCover : IsRightCover P z x := by
    cases hFirstPath with
    | right h _ => exact h
  have hxzCases : sqDist (P x) (P z) = d₂ ∨ sqDist (P x) (P z) = d₃ := by
    have hzxStart : TopThreeAdjacent P d₁ d₂ d₃ z x := by
      simpa [z, x] using S.first_start_adjacent
    have hstrict : sqDist (P z) (P x) < sqDist (P z) (P p) := by
      simpa only [IsRightCover, p, x] using hCover
    have hpz' : sqDist (P z) (P p) = d₁ := by
      simpa only [sqDist_comm] using hpz
    rcases hzxStart.2 with h₁ | h₂ | h₃
    · linarith
    · exact Or.inl (by simpa only [sqDist_comm] using h₂)
    · exact Or.inr (by simpa only [sqDist_comm] using h₃)
  have hquadXPUZ : StrictConvexQuad (P x) (P p) (P u) (P z) := by
    simpa [x, p, u, z] using erlv_x_p_u_z_strict_convex_quad S
  have hxzLtXu : sqDist (P x) (P z) < sqDist (P x) (P u) := by
    have hed := edge_diagonal_inequality_rotated hquadXPUZ
    have hpuEq : euclideanDist (P p) (P u) = euclideanDist (P p) (P z) :=
      euclideanDist_eq_of_sqDist_eq (hpu.trans hpz.symm)
    have hdist : euclideanDist (P x) (P z) < euclideanDist (P x) (P u) := by
      linarith
    exact sqDist_lt_of_euclideanDist_lt hdist
  have hxzAdj : TopThreeAdjacent P d₁ d₂ d₃ x z := by
    simpa [x, z] using topThreeAdjacent_symm S.first_start_adjacent
  have hxuAdj : TopThreeAdjacent P d₁ d₂ d₃ x u :=
    top_three_adjacent_of_strictly_longer S.classes hxzAdj hxzLtXu
  have hInjective : Function.Injective P :=
    cyclic_strict_convex_injective S.convex (by omega)
  have hxp : P x ≠ P p := by
    have h := cyclic_strict_convex_boundary_points_ne S.convex (by omega) x
    simpa [p, cyclicAdvance_one_eq_next] using h
  have hTailGeometry := case12_tail_offset_geometry S
  have htailUpper : ∀ k ∈ tail, k.val ≤ zoff := by
    simpa [tail, N, uoff, zoff, x] using hTailGeometry.1
  have htailHalf : ∀ k ∈ tail, InLeftOpenHalfPlane (P x) (P p)
      (P (cyclicAdvance x k.val)) := by
    simpa [tail, N, uoff, x, p] using hTailGeometry.2
  rcases hxzCases with hxzD₂ | hxzD₃
  · have hxuD₁ : sqDist (P x) (P u) = d₁ := by
      rcases hxuAdj.2 with h₁ | h₂ | h₃
      · exact h₁
      · linarith
      · linarith [S.classes.1]
    have htailCard : tail.card ≤ 2 := by
      refine two_fixed_radius_pairs_card_le_two hInjective x x p hxp
        (a₁ := d₂) (b₁ := d₁) (a₂ := d₃) (b₂ := d₂) htailHalf ?_
      intro k hk
      have hkData := Finset.mem_filter.mp hk
      have hRAdj := (Finset.mem_filter.mp hkData.1).2.2
      have hquadRaw := cyclic_strict_convex_quad_offsets S.convex x
        (a := 0) (b := 1) (c := uoff) (d := k.val)
        (by omega) (by omega) (by omega) k.isLt
      rw [← huIndex] at hquadRaw
      have hquad : StrictConvexQuad (P x) (P p) (P u)
          (P (cyclicAdvance x k.val)) := by
        simpa [p] using hquadRaw
      have hcompare := far_arc_strict_center_comparison hquad (by
        rw [hxuD₁, hpu])
      have hpAdj := top_three_adjacent_of_strictly_longer S.classes hRAdj hcompare
      have hslots := strict_top_three_rank_slots S.classes hRAdj hpAdj hcompare
      rcases hslots with h21 | h31 | h32
      · exact Or.inl h21
      · exfalso
        have hkUpper := htailUpper k hk
        by_cases hkz : k.val = zoff
        · have hRz : cyclicAdvance x k.val = z := by rw [hzIndex, hkz]
          have : d₃ = d₂ := by
            calc
              d₃ = sqDist (P x) (P (cyclicAdvance x k.val)) := h31.1.symm
              _ = sqDist (P x) (P z) := by rw [hRz]
              _ = d₂ := hxzD₂
          linarith [S.classes.1]
        · have hklt : k.val < zoff := by omega
          have hquadRZ := cyclic_strict_convex_quad_offsets S.convex x
            (a := 0) (b := 1) (c := k.val) (d := zoff)
            (by omega) (by omega) hklt hzoffn
          rw [← hzIndex] at hquadRZ
          have hed := edge_diagonal_inequality_rotated hquadRZ
          have hpEq : euclideanDist (P p) (P (cyclicAdvance x k.val)) =
              euclideanDist (P p) (P z) :=
            euclideanDist_eq_of_sqDist_eq (h31.2.trans hpz.symm)
          have hforced : euclideanDist (P x) (P z) <
              euclideanDist (P x) (P (cyclicAdvance x k.val)) := by
            simpa only [cyclicAdvance_zero, p, hpEq, add_lt_add_iff_left] using hed
          have hreverse : euclideanDist (P x) (P (cyclicAdvance x k.val)) <
              euclideanDist (P x) (P z) :=
            euclideanDist_lt_of_sqDist_lt (by
              rw [h31.1, hxzD₂]
              exact S.classes.1)
          linarith
      · exact Or.inr h32
    exact case12_bzero_false_of_tail_card_le_two S (by
      simpa [tail, N, uoff, x] using htailCard)
  · have hxuCases : sqDist (P x) (P u) = d₁ ∨
        sqDist (P x) (P u) = d₂ := by
      rcases hxuAdj.2 with h₁ | h₂ | h₃
      · exact Or.inl h₁
      · exact Or.inr h₂
      · linarith
    rcases hxuCases with hxuD₁ | hxuD₂
    · have htailCard : tail.card ≤ 2 := by
        simpa [tail, N, x] using
          case12_bzero_d3_d1_tail_card_le_two S uoff zoff huoff3 hzoffn
            (by simpa [x, u] using huIndex) (by simpa [x, z] using hzIndex)
            (by simpa [x, p, u] using hpu) (by simpa [x, q, u] using hqu)
            (by simpa [x, p, z] using hpz) (by simpa [x, q, z] using hqz)
            (by simpa [x, u] using hxuD₁) (by simpa [x, z] using hxzD₃)
            (by simpa [tail, N, x] using htailUpper)
            (by simpa [tail, N, x, p] using htailHalf)
      exact case12_bzero_false_of_tail_card_le_two S (by
        simpa [tail, N, uoff, x] using htailCard)
    · have htailCard : tail.card ≤ 2 := by
        refine two_fixed_radius_pairs_card_le_two hInjective x x p hxp
          (a₁ := d₃) (b₁ := d₁) (a₂ := d₃) (b₂ := d₂) htailHalf ?_
        intro k hk
        have hkData := Finset.mem_filter.mp hk
        have hRAdj := (Finset.mem_filter.mp hkData.1).2.2
        have hquadRaw := cyclic_strict_convex_quad_offsets S.convex x
          (a := 0) (b := 1) (c := uoff) (d := k.val)
          (by omega) (by omega) (by omega) k.isLt
        rw [← huIndex] at hquadRaw
        have hquad : StrictConvexQuad (P x) (P p) (P u)
            (P (cyclicAdvance x k.val)) := by
          simpa [p] using hquadRaw
        have hcompare := far_arc_strict_center_comparison hquad (by
          rw [hxuD₂, hpu]
          exact le_of_lt S.classes.2.1)
        have hpAdj := top_three_adjacent_of_strictly_longer S.classes hRAdj hcompare
        have hslots := strict_top_three_rank_slots S.classes hRAdj hpAdj hcompare
        rcases hslots with h21 | h31 | h32
        · exfalso
          have hed := edge_diagonal_inequality_rotated hquad
          have hpuD₁ : euclideanDist (P p) (P u) =
              euclideanDist (P p) (P (cyclicAdvance x k.val)) :=
            euclideanDist_eq_of_sqDist_eq (hpu.trans h21.2.symm)
          have hxuD₂' : euclideanDist (P x) (P (cyclicAdvance x k.val)) =
              euclideanDist (P x) (P u) :=
            euclideanDist_eq_of_sqDist_eq (h21.1.trans hxuD₂.symm)
          linarith
        · exact Or.inl h31
        · exact Or.inr h32
      exact case12_bzero_false_of_tail_card_le_two S (by
        simpa [tail, N, uoff, x] using htailCard)

/-- Section 6.2: the one-outer-move part of terminal color `(1,2)-d₁`. -/
theorem erlv_case12_other_d1_bone_impossible
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (h12 : S.Case12)
    (hOther : sqDist
      (P (cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)
        S.pair.first.leftMoves))
      (P (cyclicAdvance S.x 1)) = d₁)
    (hBOne : S.pair.first.leftMoves = 1) : False := by
  classical
  let x := S.x
  let p := cyclicAdvance x 1
  let q := cyclicAdvance x 2
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3)
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
  let s := cyclicRetreat z 1
  let uoff := erlvUOffset S
  let zoff := erlvZOffset S
  let soff := zoff - 1
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (S.highDegree S.x)
  have hOffsets := erlv_u_z_offset_data S
  have huoff3 : 3 < uoff := by simpa [uoff] using hOffsets.1
  have huz : uoff + 3 ≤ zoff := by simpa [uoff, zoff] using hOffsets.2.1
  have hzoffn : zoff < n := by simpa [zoff] using hOffsets.2.2.1
  have huoffn : uoff < n := by omega
  have hsoffn : soff < n := by dsimp [soff]; omega
  have huS : uoff < soff := by dsimp [soff]; omega
  have hsZ : soff < zoff := by dsimp [soff]; omega
  have huIndex : u = cyclicAdvance x uoff := by
    simpa [u, x, uoff] using hOffsets.2.2.2.1
  have hzIndex : z = cyclicAdvance x zoff := by
    simpa [z, x, zoff] using hOffsets.2.2.2.2
  have hsIndex : s = cyclicAdvance x soff := by
    dsimp [s]
    rw [hzIndex]
    have h := cyclicRetreat_advance x (k := zoff) (m := 1) (by omega) hzoffn
    simpa [soff] using h
  have hData := erlv_case12_shared_tip_rank_data S h12
  have hpu : sqDist (P p) (P u) = d₁ := by
    simpa [p, u, x] using hData.1
  have hqu : sqDist (P q) (P u) = d₂ := by
    simpa [q, u, x] using hData.2.2
  have hsp : sqDist (P s) (P p) = d₁ := by
    rw [hBOne] at hOther
    simpa [s, z, p, x] using hOther
  have hps : sqDist (P p) (P s) = d₁ := by
    simpa only [sqDist_comm] using hsp
  have hquNe : q ≠ u := by
    rw [huIndex]
    exact cyclicAdvance_ne_of_lt x (by omega) huoffn (by omega)
  have hquAdj : TopThreeAdjacent P d₁ d₂ d₃ q u :=
    ⟨hquNe, Or.inr (Or.inl hqu)⟩
  have hquadPQUS : StrictConvexQuad (P p) (P q) (P u) (P s) := by
    have hquad := cyclic_strict_convex_quad_offsets S.convex x
      (a := 1) (b := 2) (c := uoff) (d := soff)
      (by omega) (by omega) huS hsoffn
    rw [← huIndex, ← hsIndex] at hquad
    simpa [p, q] using hquad
  have hqs : sqDist (P q) (P s) = d₁ := by
    have hed := edge_diagonal_inequality_rotated hquadPQUS
    have hpsEq : euclideanDist (P p) (P s) = euclideanDist (P p) (P u) :=
      euclideanDist_eq_of_sqDist_eq (hps.trans hpu.symm)
    have hdist : euclideanDist (P q) (P u) < euclideanDist (P q) (P s) := by
      linarith
    have hgrow : sqDist (P q) (P u) < sqDist (P q) (P s) :=
      sqDist_lt_of_euclideanDist_lt hdist
    have hqsAdj := top_three_adjacent_of_strictly_longer S.classes hquAdj hgrow
    rcases hqsAdj.2 with h₁ | h₂ | h₃
    · exact h₁
    · linarith [S.classes.2.1]
    · linarith [S.classes.1]
  have hFirstPath : K3CoverSequence P z x 1 1 := by
    simpa only [z, x, hBOne, h12.1] using S.pair.first.path
  have hStart : TopThreeAdjacent P d₁ d₂ d₃ z x := by
    simpa [z, x] using S.first_start_adjacent
  cases hFirstPath with
  | left hLeft tailPath =>
      cases tailPath with
      | right hRight _ =>
          have hMid : TopThreeAdjacent P d₁ d₂ d₃ s x := by
            have h := left_cover_top_three_adjacent S.classes hStart hLeft
            simpa [s] using h
          have hzxD₃ : sqDist (P z) (P x) = d₃ := by
            have hGrow₁ : sqDist (P z) (P x) < sqDist (P s) (P x) := by
              simpa only [IsLeftCover, s] using hLeft
            have hGrow₂ : sqDist (P s) (P x) < sqDist (P s) (P p) := by
              simpa only [IsRightCover, p, x] using hRight
            rcases hStart.2 with h₁ | h₂ | h₃ <;>
              rcases hMid.2 with hm₁ | hm₂ | hm₃ <;>
                linarith [S.classes.1, S.classes.2.1]
          have hsxD₂ : sqDist (P s) (P x) = d₂ := by
            have hGrow₁ : sqDist (P z) (P x) < sqDist (P s) (P x) := by
              simpa only [IsLeftCover, s] using hLeft
            have hGrow₂ : sqDist (P s) (P x) < sqDist (P s) (P p) := by
              simpa only [IsRightCover, p, x] using hRight
            rcases hMid.2 with hm₁ | hm₂ | hm₃ <;>
              linarith [S.classes.1, S.classes.2.1]
          have hxz : sqDist (P x) (P z) = d₃ := by
            simpa only [sqDist_comm] using hzxD₃
          have hxs : sqDist (P x) (P s) = d₂ := by
            simpa only [sqDist_comm] using hsxD₂
          have hquadXPUS : StrictConvexQuad (P x) (P p) (P u) (P s) := by
            have hquad := cyclic_strict_convex_quad_offsets S.convex x
              (a := 0) (b := 1) (c := uoff) (d := soff)
              (by omega) (by omega) huS hsoffn
            rw [← huIndex, ← hsIndex] at hquad
            simpa [p] using hquad
          have hxsLtXu : sqDist (P x) (P s) < sqDist (P x) (P u) := by
            have hed := edge_diagonal_inequality_rotated hquadXPUS
            have hpEq : euclideanDist (P p) (P u) =
                euclideanDist (P p) (P s) :=
              euclideanDist_eq_of_sqDist_eq (hpu.trans hps.symm)
            have hdist : euclideanDist (P x) (P s) < euclideanDist (P x) (P u) := by
              linarith
            exact sqDist_lt_of_euclideanDist_lt hdist
          have hxsAdj : TopThreeAdjacent P d₁ d₂ d₃ x s :=
            topThreeAdjacent_symm hMid
          have hxuAdj := top_three_adjacent_of_strictly_longer
            S.classes hxsAdj hxsLtXu
          have hxu : sqDist (P x) (P u) = d₁ := by
            rcases hxuAdj.2 with h₁ | h₂ | h₃
            · exact h₁
            · linarith
            · linarith [S.classes.1]
          have hquadXPUZ : StrictConvexQuad (P x) (P p) (P u) (P z) := by
            simpa [x, p, u, z] using erlv_x_p_u_z_strict_convex_quad S
          have hxzLtPz : sqDist (P x) (P z) < sqDist (P p) (P z) :=
            far_arc_strict_center_comparison hquadXPUZ (by rw [hxu, hpu])
          have hpzAdj := top_three_adjacent_of_strictly_longer
            S.classes (topThreeAdjacent_symm hStart) hxzLtPz
          have hpzCases : sqDist (P p) (P z) = d₁ ∨
              sqDist (P p) (P z) = d₂ := by
            rcases hpzAdj.2 with h₁ | h₂ | h₃
            · exact Or.inl h₁
            · exact Or.inr h₂
            · linarith
          have hpz : sqDist (P p) (P z) = d₂ := by
            rcases hpzCases with hpzD₁ | hpzD₂
            · have hquadPQSZ : StrictConvexQuad (P p) (P q) (P s) (P z) := by
                have hquad := cyclic_strict_convex_quad_offsets S.convex x
                  (a := 1) (b := 2) (c := soff) (d := zoff)
                  (by omega) (by omega) hsZ hzoffn
                rw [← hsIndex, ← hzIndex] at hquad
                simpa [p, q] using hquad
              have hed := edge_diagonal_inequality_rotated hquadPQSZ
              have hqzNe : q ≠ z := by
                rw [hzIndex]
                exact cyclicAdvance_ne_of_lt x (by omega) hzoffn (by omega)
              have hqzBound := top_three_class_bounds_of_ne S.classes hqzNe
              dsimp only at hqzBound
              have hqzLe : euclideanDist (P q) (P z) ≤
                  euclideanDist (P p) (P s) :=
                euclideanDist_le_of_sqDist_le (by rw [hps]; exact hqzBound.1)
              have hqsEq : euclideanDist (P q) (P s) =
                  euclideanDist (P p) (P s) :=
                euclideanDist_eq_of_sqDist_eq (hqs.trans hps.symm)
              have hpzEq : euclideanDist (P p) (P z) =
                  euclideanDist (P p) (P s) :=
                euclideanDist_eq_of_sqDist_eq (hpzD₁.trans hps.symm)
              linarith
            · exact hpzD₂
          have hbounds := maximal_gap_tail_degree_bounds S
            (by simpa [p, u, x] using hpu)
            (by simpa [z, x] using hxz)
            (by simpa [p, z, x] using hpz)
          have hdegree := hbounds.1 (by simpa [u, x] using hxu)
          exact high_degree_le_six_false S S.x hdegree
  | right hRight tailPath =>
      cases tailPath with
      | left hLeft _ =>
          have hMid : TopThreeAdjacent P d₁ d₂ d₃ z p := by
            have h := right_cover_top_three_adjacent S.classes hStart hRight
            simpa [p, x] using h
          have hzxD₃ : sqDist (P z) (P x) = d₃ := by
            have hGrow₁ : sqDist (P z) (P x) < sqDist (P z) (P p) := by
              simpa only [IsRightCover, p, x] using hRight
            have hGrow₂ : sqDist (P z) (P p) < sqDist (P s) (P p) := by
              simpa only [IsLeftCover, s] using hLeft
            rcases hStart.2 with h₁ | h₂ | h₃ <;>
              rcases hMid.2 with hm₁ | hm₂ | hm₃ <;>
                linarith [S.classes.1, S.classes.2.1]
          have hzpD₂ : sqDist (P z) (P p) = d₂ := by
            have hGrow₁ : sqDist (P z) (P x) < sqDist (P z) (P p) := by
              simpa only [IsRightCover, p, x] using hRight
            have hGrow₂ : sqDist (P z) (P p) < sqDist (P s) (P p) := by
              simpa only [IsLeftCover, s] using hLeft
            rcases hMid.2 with hm₁ | hm₂ | hm₃ <;>
              linarith [S.classes.1, S.classes.2.1]
          have hxz : sqDist (P x) (P z) = d₃ := by
            simpa only [sqDist_comm] using hzxD₃
          have hpz : sqDist (P p) (P z) = d₂ := by
            simpa only [sqDist_comm] using hzpD₂
          have hquad := erlv_x_p_u_z_strict_convex_quad S
          have hxzAdj : TopThreeAdjacent P d₁ d₂ d₃ S.x
              (firstClockwiseNeighbor P d₁ d₂ d₃ S.x) :=
            topThreeAdjacent_symm S.first_start_adjacent
          have hxu := d1_d3_opposite_sides_force_xu_top_two S.classes hquad
            hxzAdj (by simpa [p, u, x] using hpu)
            (by simpa [z, x] using hxz) (by simpa [p, z, x] using hpz)
          have hbounds := maximal_gap_tail_degree_bounds S
            (by simpa [p, u, x] using hpu)
            (by simpa [z, x] using hxz)
            (by simpa [p, z, x] using hpz)
          rcases hxu with hxuD₁ | hxuD₂
          · have hdegree := hbounds.1 hxuD₁
            exact high_degree_le_six_false S S.x hdegree
          · have hdegree := hbounds.2 hxuD₂
            exact high_degree_le_six_false S S.x (hdegree.trans (by omega))

/-- Session-9 obligation 1/8: terminal color `(1,2)-d₁`. -/
theorem erlv_at_vertex_case12_other_d1_impossible_of_tail :
    ErLVAtVertexCase12OtherD1Impossible := by
  intro n _ P d₁ d₂ d₃ S h12 hOther
  have hBLe : S.pair.first.leftMoves ≤ 1 := by
    have hBudget := S.pair.first.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case12] at h12
    omega
  by_cases hBZero : S.pair.first.leftMoves = 0
  · exact erlv_case12_other_d1_bzero_impossible S h12 hOther hBZero
  · have hBOne : S.pair.first.leftMoves = 1 := by omega
    exact erlv_case12_other_d1_bone_impossible S h12 hOther hBOne

private theorem case21_d1_tail_slot31_impossible
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (roff zoff : ℕ)
    (hroff1 : 1 < roff) (hzoffn : zoff < n)
    (hzIndex : firstClockwiseNeighbor P d₁ d₂ d₃ S.x =
      cyclicAdvance S.x zoff)
    (hxz : sqDist (P S.x)
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₃)
    (hpz : sqDist (P (cyclicAdvance S.x 1))
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₂)
    (htailUpper : ∀ k ∈ (ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
      (fun k ↦ roff < k.val), k.val ≤ zoff)
    (k : Fin n)
    (hk : k ∈ (ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
      (fun k ↦ roff < k.val))
    (h31 : sqDist (P S.x) (P (cyclicAdvance S.x k.val)) = d₃ ∧
      sqDist (P (cyclicAdvance S.x 1))
        (P (cyclicAdvance S.x k.val)) = d₁) : False := by
  let x := S.x
  let p := cyclicAdvance x 1
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
  have hkUpper : k.val ≤ zoff := htailUpper k hk
  by_cases hkz : k.val = zoff
  · have hRz : cyclicAdvance x k.val = z := by
      dsimp [x, z]
      rw [hzIndex, hkz]
    have : d₁ = d₂ := by
      calc
        d₁ = sqDist (P p) (P (cyclicAdvance x k.val)) := by
          simpa [x, p] using h31.2.symm
        _ = sqDist (P p) (P z) := by rw [hRz]
        _ = d₂ := by simpa [x, p, z] using hpz
    linarith [S.classes.2.1]
  · have hklt : k.val < zoff := by omega
    have hquadRZ := cyclic_strict_convex_quad_offsets S.convex x
      (a := 0) (b := 1) (c := k.val) (d := zoff)
      (by omega) (by
        have hkLower := (Finset.mem_filter.mp hk).2
        omega) hklt hzoffn
    rw [← hzIndex] at hquadRZ
    have hed := edge_diagonal_inequality_rotated hquadRZ
    have hxEq : euclideanDist (P x) (P (cyclicAdvance x k.val)) =
        euclideanDist (P x) (P z) :=
      euclideanDist_eq_of_sqDist_eq (by
        simpa [x, z] using h31.1.trans hxz.symm)
    have hforced : euclideanDist (P p) (P (cyclicAdvance x k.val)) <
        euclideanDist (P p) (P z) := by
      simpa [x, p, z, hxEq, add_lt_add_iff_right] using hed
    have hreverse : euclideanDist (P p) (P z) <
        euclideanDist (P p) (P (cyclicAdvance x k.val)) :=
      euclideanDist_lt_of_sqDist_lt (by
        rw [show sqDist (P p) (P z) = d₂ by simpa [x, p, z] using hpz,
          show sqDist (P p) (P (cyclicAdvance x k.val)) = d₁ by
            simpa [x, p] using h31.2]
        exact S.classes.2.1)
    linarith

private theorem case21_d1_false_of_tail_card_le_one
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (β : ℕ) (hβ : β ≤ 1)
    (htail : ((ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
      fun k ↦ erlvUOffset S + β < k.val).card ≤ 1) : False := by
  have hdegree := erlv_x_degree_le_of_tail_card S β 1 hβ htail
  exact high_degree_le_six_false S S.x (hdegree.trans (by omega))

/-- Session-9 obligation 3/8: terminal color `(2,1)-d₁` (paper Section 7). -/
theorem erlv_at_vertex_case21_other_d1_impossible_of_tail :
    ErLVAtVertexCase21OtherD1Impossible := by
  intro n _ P d₁ d₂ d₃ S h21 hOther
  classical
  let x := S.x
  let p := cyclicAdvance x 1
  let q := cyclicAdvance x 2
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3)
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
  let β := S.pair.second.rightMoves
  let r := cyclicAdvance u β
  let uoff := erlvUOffset S
  let roff := uoff + β
  let zoff := erlvZOffset S
  let N := ccwNeighborOffsets P d₁ d₂ d₃ x
  let tail := N.filter fun k ↦ roff < k.val
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (S.highDegree S.x)
  have hβ : β ≤ 1 := by
    have hBudget := S.pair.second.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case21] at h21
    dsimp [β]
    omega
  have hBZero : S.pair.first.leftMoves = 0 := by
    have hBudget := S.pair.first.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case21] at h21
    omega
  have hOffsets := erlv_u_z_offset_data S
  have huoff3 : 3 < uoff := by simpa [uoff] using hOffsets.1
  have huz : uoff + 3 ≤ zoff := by simpa [uoff, zoff] using hOffsets.2.1
  have hzoffn : zoff < n := by simpa [zoff] using hOffsets.2.2.1
  have hroffn : roff < n := by dsimp [roff]; omega
  have hrz : roff < zoff := by dsimp [roff]; omega
  have huIndex : u = cyclicAdvance x uoff := by
    simpa [u, x, uoff] using hOffsets.2.2.2.1
  have hzIndex : z = cyclicAdvance x zoff := by
    simpa [z, x, zoff] using hOffsets.2.2.2.2
  have hrIndex : r = cyclicAdvance x roff := by
    dsimp [r]
    rw [huIndex, cyclicAdvance_add]
  have hFirstPath : K3CoverSequence P z x 0 2 := by
    simpa only [z, x, hBZero, h21.1] using S.pair.first.path
  have hFirstRanks := right_right_cover_rank_ladder S.classes
    (by simpa [z, x] using S.first_start_adjacent) hFirstPath
  have hxz : sqDist (P x) (P z) = d₃ := by
    simpa only [sqDist_comm] using hFirstRanks.1
  have hpz : sqDist (P p) (P z) = d₂ := by
    simpa only [p, x, sqDist_comm] using hFirstRanks.2.1
  have hqz : sqDist (P q) (P z) = d₁ := by
    simpa only [q, x, sqDist_comm] using hFirstRanks.2.2
  have hqr : sqDist (P q) (P r) = d₁ := by
    simpa [q, r, u, β, x] using hOther
  have hquadPQRZ : StrictConvexQuad (P p) (P q) (P r) (P z) := by
    have hquad := cyclic_strict_convex_quad_offsets S.convex x
      (a := 1) (b := 2) (c := roff) (d := zoff)
      (by omega) (by omega) hrz hzoffn
    rw [← hrIndex, ← hzIndex] at hquad
    simpa [p, q] using hquad
  have hpzNe : p ≠ z := by
    rw [hzIndex]
    exact cyclicAdvance_ne_of_lt x (by omega) hzoffn (by omega)
  have hpzAdj : TopThreeAdjacent P d₁ d₂ d₃ p z :=
    ⟨hpzNe, Or.inr (Or.inl hpz)⟩
  have hpr : sqDist (P p) (P r) = d₁ := by
    have hed := edge_diagonal_inequality_rotated hquadPQRZ
    have hqEq : euclideanDist (P q) (P r) = euclideanDist (P q) (P z) :=
      euclideanDist_eq_of_sqDist_eq (hqr.trans hqz.symm)
    have hdist : euclideanDist (P p) (P z) < euclideanDist (P p) (P r) := by
      linarith
    have hgrow : sqDist (P p) (P z) < sqDist (P p) (P r) :=
      sqDist_lt_of_euclideanDist_lt hdist
    have hprAdj := top_three_adjacent_of_strictly_longer S.classes hpzAdj hgrow
    rcases hprAdj.2 with h₁ | h₂ | h₃
    · exact h₁
    · linarith
    · linarith [S.classes.1]
  have hquadXPRZ : StrictConvexQuad (P x) (P p) (P r) (P z) := by
    have hquad := cyclic_strict_convex_quad_offsets S.convex x
      (a := 0) (b := 1) (c := roff) (d := zoff)
      (by omega) (by omega) hrz hzoffn
    rw [← hrIndex, ← hzIndex] at hquad
    simpa [p] using hquad
  have hxzLtXr : sqDist (P x) (P z) < sqDist (P x) (P r) := by
    have hed := edge_diagonal_inequality_rotated hquadXPRZ
    have hpzLtPr : euclideanDist (P p) (P z) < euclideanDist (P p) (P r) :=
      euclideanDist_lt_of_sqDist_lt (by rw [hpz, hpr]; exact S.classes.2.1)
    have hdist : euclideanDist (P x) (P z) < euclideanDist (P x) (P r) := by
      linarith
    exact sqDist_lt_of_euclideanDist_lt hdist
  have hxzAdj : TopThreeAdjacent P d₁ d₂ d₃ x z := by
    simpa [x, z] using topThreeAdjacent_symm S.first_start_adjacent
  have hxrAdj := top_three_adjacent_of_strictly_longer S.classes hxzAdj hxzLtXr
  have hxrCases : sqDist (P x) (P r) = d₁ ∨
      sqDist (P x) (P r) = d₂ := by
    rcases hxrAdj.2 with h₁ | h₂ | h₃
    · exact Or.inl h₁
    · exact Or.inr h₂
    · linarith
  have hInjective : Function.Injective P :=
    cyclic_strict_convex_injective S.convex (by omega)
  have hxp : P x ≠ P p := by
    have h := cyclic_strict_convex_boundary_points_ne S.convex (by omega) x
    simpa [p, cyclicAdvance_one_eq_next] using h
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ x := by
    have := S.highDegree x
    omega
  have htailUpper : ∀ k ∈ tail, k.val ≤ zoff := by
    intro k hk
    have hkN := (Finset.mem_filter.mp hk).1
    have hraw := ccw_neighbor_offset_le_clockwise_boundary hxdeg hkN
    have hraw' : k.val +
        (firstClockwiseNeighborOffset P d₁ d₂ d₃ S.x).val ≤ n := by
      simpa [x] using hraw
    dsimp [zoff, erlvZOffset]
    omega
  have htailHalf : ∀ k ∈ tail, InLeftOpenHalfPlane (P x) (P p)
      (P (cyclicAdvance x k.val)) := by
    intro k hk
    have hkLower := (Finset.mem_filter.mp hk).2
    have h := cyclic_offset_in_left_open_half_plane S.convex x
      (k := k.val) (by dsimp [roff] at hkLower; omega) k.isLt
    simpa [p] using h
  have hNo31 : ∀ k ∈ tail,
      sqDist (P x) (P (cyclicAdvance x k.val)) = d₃ ∧
        sqDist (P p) (P (cyclicAdvance x k.val)) = d₁ → False := by
    intro k hk h31
    exact case21_d1_tail_slot31_impossible S roff zoff (by
      dsimp [roff]
      omega) hzoffn (by simpa [x, z] using hzIndex)
      (by simpa [x, z] using hxz) (by simpa [x, p, z] using hpz)
      (by simpa [tail, N, x] using htailUpper) k
      (by simpa [tail, N, x] using hk) (by simpa [x, p] using h31)
  rcases hxrCases with hxrD₁ | hxrD₂
  · have htailCard : tail.card ≤ 1 := by
      refine fixed_radii_offset_card_le_one hInjective x x p hxp
        (radiusA := d₃) (radiusB := d₂) htailHalf ?_
      intro k hk
      have hkData := Finset.mem_filter.mp hk
      have hRAdj := (Finset.mem_filter.mp hkData.1).2.2
      have hquadRaw := cyclic_strict_convex_quad_offsets S.convex x
        (a := 0) (b := 1) (c := roff) (d := k.val)
        (by omega) (by omega) (by omega) k.isLt
      rw [← hrIndex] at hquadRaw
      have hquad : StrictConvexQuad (P x) (P p) (P r)
          (P (cyclicAdvance x k.val)) := by simpa [p] using hquadRaw
      have hcompare := far_arc_strict_center_comparison hquad (by rw [hxrD₁, hpr])
      have hpAdj := top_three_adjacent_of_strictly_longer S.classes hRAdj hcompare
      have hslots := strict_top_three_rank_slots S.classes hRAdj hpAdj hcompare
      rcases hslots with h21 | h31 | h32
      · exfalso
        have hquadPQR := cyclic_strict_convex_quad_offsets S.convex x
          (a := 1) (b := 2) (c := roff) (d := k.val)
          (by omega) (by omega) (by omega) k.isLt
        rw [← hrIndex] at hquadPQR
        have hpqCompare := far_arc_strict_center_comparison hquadPQR (by
          rw [hpr, hqr])
        have hqRNe : q ≠ cyclicAdvance x k.val :=
          cyclicAdvance_ne_of_lt x (by omega) k.isLt (by omega)
        have hqBound := top_three_class_bounds_of_ne S.classes hqRNe
        dsimp only at hqBound
        linarith [h21.2, hqBound.1]
      · exact (hNo31 k hk h31).elim
      · exact h32
    exact case21_d1_false_of_tail_card_le_one S β hβ (by
      simpa [tail, N, roff, uoff, β, x] using htailCard)
  · have htailCard : tail.card ≤ 1 := by
      refine fixed_radii_offset_card_le_one hInjective x x p hxp
        (radiusA := d₃) (radiusB := d₂) htailHalf ?_
      intro k hk
      have hkData := Finset.mem_filter.mp hk
      have hRAdj := (Finset.mem_filter.mp hkData.1).2.2
      have hquadRaw := cyclic_strict_convex_quad_offsets S.convex x
        (a := 0) (b := 1) (c := roff) (d := k.val)
        (by omega) (by omega) (by omega) k.isLt
      rw [← hrIndex] at hquadRaw
      have hquad : StrictConvexQuad (P x) (P p) (P r)
          (P (cyclicAdvance x k.val)) := by simpa [p] using hquadRaw
      have hcompare := far_arc_strict_center_comparison hquad (by
        rw [hxrD₂, hpr]
        exact le_of_lt S.classes.2.1)
      have hpAdj := top_three_adjacent_of_strictly_longer S.classes hRAdj hcompare
      have hslots := strict_top_three_rank_slots S.classes hRAdj hpAdj hcompare
      rcases hslots with h21 | h31 | h32
      · exfalso
        have hed := edge_diagonal_inequality_rotated hquad
        have hprEq : euclideanDist (P p) (P r) =
            euclideanDist (P p) (P (cyclicAdvance x k.val)) :=
          euclideanDist_eq_of_sqDist_eq (hpr.trans h21.2.symm)
        have hxrEq : euclideanDist (P x) (P (cyclicAdvance x k.val)) =
            euclideanDist (P x) (P r) :=
          euclideanDist_eq_of_sqDist_eq (h21.1.trans hxrD₂.symm)
        linarith
      · exact (hNo31 k hk h31).elim
      · exact h32
    exact case21_d1_false_of_tail_card_le_one S β hβ (by
      simpa [tail, N, roff, uoff, β, x] using htailCard)

private theorem case21_d2_xtail_card_le_two
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃)
    (hxz : sqDist (P S.x)
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₃)
    (hpz : sqDist (P (cyclicAdvance S.x 1))
      (P (firstClockwiseNeighbor P d₁ d₂ d₃ S.x)) = d₂)
    (hanchor : sqDist (P S.x)
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3))) ≤
      sqDist (P (cyclicAdvance S.x 1))
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3)))) :
    ((ccwNeighborOffsets P d₁ d₂ d₃ S.x).filter
      fun k ↦ erlvUOffset S < k.val).card ≤ 2 := by
  classical
  let x := S.x
  let p := cyclicAdvance x 1
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3)
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
  let uoff := erlvUOffset S
  let zoff := erlvZOffset S
  let N := ccwNeighborOffsets P d₁ d₂ d₃ x
  let tail := N.filter fun k ↦ uoff < k.val
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (S.highDegree S.x)
  have hOffsets := erlv_u_z_offset_data S
  have huoff3 : 3 < uoff := by simpa [uoff] using hOffsets.1
  have hzoffn : zoff < n := by simpa [zoff] using hOffsets.2.2.1
  have huIndex : u = cyclicAdvance x uoff := by
    simpa [u, x, uoff] using hOffsets.2.2.2.1
  have hzIndex : z = cyclicAdvance x zoff := by
    simpa [z, x, zoff] using hOffsets.2.2.2.2
  have hInjective : Function.Injective P :=
    cyclic_strict_convex_injective S.convex (by omega)
  have hxp : P x ≠ P p := by
    have h := cyclic_strict_convex_boundary_points_ne S.convex (by omega) x
    simpa [p, cyclicAdvance_one_eq_next] using h
  have hTailGeometry := case12_tail_offset_geometry S
  have htailUpper : ∀ k ∈ tail, k.val ≤ zoff := by
    simpa [tail, N, uoff, zoff, x] using hTailGeometry.1
  have htailHalf : ∀ k ∈ tail, InLeftOpenHalfPlane (P x) (P p)
      (P (cyclicAdvance x k.val)) := by
    simpa [tail, N, uoff, x, p] using hTailGeometry.2
  refine two_fixed_radius_pairs_card_le_two hInjective x x p hxp
    (a₁ := d₂) (b₁ := d₁) (a₂ := d₃) (b₂ := d₂) htailHalf ?_
  intro k hk
  have hkData := Finset.mem_filter.mp hk
  have hRAdj := (Finset.mem_filter.mp hkData.1).2.2
  have hquadRaw := cyclic_strict_convex_quad_offsets S.convex x
    (a := 0) (b := 1) (c := uoff) (d := k.val)
    (by omega) (by omega) (by omega) k.isLt
  rw [← huIndex] at hquadRaw
  have hquad : StrictConvexQuad (P x) (P p) (P u)
      (P (cyclicAdvance x k.val)) := by simpa [p] using hquadRaw
  have hcompare := far_arc_strict_center_comparison hquad (by
    simpa [x, p, u] using hanchor)
  have hpAdj := top_three_adjacent_of_strictly_longer S.classes hRAdj hcompare
  have hslots := strict_top_three_rank_slots S.classes hRAdj hpAdj hcompare
  rcases hslots with h21 | h31 | h32
  · exact Or.inl h21
  · exfalso
    exact case21_d1_tail_slot31_impossible S uoff zoff (by omega) hzoffn
      (by simpa [x, z] using hzIndex) hxz hpz
      (by simpa [tail, N, x] using htailUpper) k
      (by simpa [tail, N, x] using hk) (by simpa [x, p] using h31)
  · exact Or.inr h32

private theorem case21_d2_above_impossible
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (D : Case21D2Prepared S)
    (hpuAbove : d₃ < sqDist (P (cyclicAdvance S.x 1))
      (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3)))) : False := by
  classical
  let x := S.x
  let p := cyclicAdvance x 1
  let t := cyclicAdvance x 3
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ t
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
  let uoff := erlvUOffset S
  let puoff := erlvPUOffset S
  let Np := ccwNeighborOffsets P d₁ d₂ d₃ p
  let left := Np.filter fun k ↦ k.val < puoff
  let tip := Np.filter fun k ↦ k.val = puoff
  let right := Np.filter fun k ↦ puoff < k.val
  have hpuoff2 : 2 < puoff := by
    simpa [puoff] using (erlv_p_u_offset_data S).1
  have hleftHalf : ∀ k ∈ left, InLeftOpenHalfPlane (P x) (P p)
      (P (cyclicAdvance p k.val)) := by
    simpa [left, Np, x, p, puoff] using D.left_half
  have hrightCard : right.card ≤ 3 := by
    simpa [right, Np, p, puoff] using D.right_card
  have htipOne : tip.card ≤ 1 := by
    simpa [tip, Np, p, puoff] using D.tip_card
  have htuAdj : TopThreeAdjacent P d₁ d₂ d₃ t u := by
    simpa [t, u] using S.second_start_adjacent
  have hpuAdj : TopThreeAdjacent P d₁ d₂ d₃ p u :=
    top_three_adjacent_of_strictly_longer S.classes htuAdj (by
      rw [show sqDist (P t) (P u) = d₃ by simpa [x, t, u] using D.tu]
      simpa [x, p, u] using hpuAbove)
  have hpu : sqDist (P p) (P u) = d₂ := by
    rcases hpuAdj.2 with h₁ | h₂ | h₃
    · have hle : sqDist (P p) (P u) ≤ d₂ := by simpa [x, p, u] using D.pu_le
      linarith [S.classes.2.1]
    · exact h₂
    · linarith
  have hquadXPUZ : StrictConvexQuad (P x) (P p) (P u) (P z) := by
    simpa [x, p, u, z] using erlv_x_p_u_z_strict_convex_quad S
  have hxzLtXu : sqDist (P x) (P z) < sqDist (P x) (P u) := by
    have hed := edge_diagonal_inequality_rotated hquadXPUZ
    have hpEq : euclideanDist (P p) (P u) = euclideanDist (P p) (P z) :=
      euclideanDist_eq_of_sqDist_eq (hpu.trans (by simpa [x, p, z] using D.pz.symm))
    have hdist : euclideanDist (P x) (P z) < euclideanDist (P x) (P u) := by
      linarith
    exact sqDist_lt_of_euclideanDist_lt hdist
  have hxzAdj : TopThreeAdjacent P d₁ d₂ d₃ x z := by
    simpa [x, z] using topThreeAdjacent_symm S.first_start_adjacent
  have hxuAdj := top_three_adjacent_of_strictly_longer S.classes hxzAdj hxzLtXu
  have hxuCases : sqDist (P x) (P u) = d₁ ∨
      sqDist (P x) (P u) = d₂ := by
    rcases hxuAdj.2 with h₁ | h₂ | h₃
    · exact Or.inl h₁
    · exact Or.inr h₂
    · have hxz' : sqDist (P x) (P z) = d₃ := by
        simpa [x, z] using D.xz
      linarith
  rcases hxuCases with hxuD₁ | hxuD₂
  · have hleftCard : left.card ≤ 2 := by
      refine two_fixed_radius_pairs_card_le_two D.points_injective p x p
        (by simpa [x, p] using D.x_p_ne) (a₁ := d₁) (b₁ := d₃)
        (a₂ := d₂) (b₂ := d₃) hleftHalf ?_
      intro k hk
      have hkData := Finset.mem_filter.mp hk
      have hpRAdj := (Finset.mem_filter.mp hkData.1).2.2
      have hpoint : cyclicAdvance p k.val = cyclicAdvance x (1 + k.val) := by
        simp [p, cyclicAdvance_add]
      have hquadRaw := cyclic_strict_convex_quad_offsets S.convex x
        (a := 0) (b := 1) (c := 1 + k.val) (d := uoff)
        (by omega) (by
          have hk0 := (Finset.mem_filter.mp hkData.1).2.1
          exact Nat.add_lt_add_left (Fin.pos_iff_ne_zero.mpr hk0) 1)
        (by
          have hpuAdd : 1 + puoff = uoff := by
            have huPos : 0 < erlvUOffset S := by
              have hu3 := (erlv_u_z_offset_data S).1
              omega
            dsimp [puoff, erlvPUOffset, uoff]
            omega
          omega) (by simpa [uoff] using D.uoff_lt)
      rw [← hpoint, ← D.u_index] at hquadRaw
      have hquad : StrictConvexQuad (P x) (P p)
          (P (cyclicAdvance p k.val)) (P u) := by simpa [x, p, u] using hquadRaw
      have hed := edge_diagonal_inequality_rotated hquad
      have hxuGtPu : euclideanDist (P p) (P u) < euclideanDist (P x) (P u) :=
        euclideanDist_lt_of_sqDist_lt (by rw [hpu, hxuD₁]; exact S.classes.2.1)
      have hcompare : sqDist (P p) (P (cyclicAdvance p k.val)) <
          sqDist (P x) (P (cyclicAdvance p k.val)) := by
        apply sqDist_lt_of_euclideanDist_lt
        linarith
      have hxRAdj := top_three_adjacent_of_strictly_longer
        S.classes hpRAdj hcompare
      have hslots := strict_top_three_rank_slots S.classes hpRAdj hxRAdj hcompare
      rcases hslots with h21 | h31 | h32
      · exfalso
        have hxuEq : euclideanDist (P x) (P u) =
            euclideanDist (P x) (P (cyclicAdvance p k.val)) :=
          euclideanDist_eq_of_sqDist_eq (hxuD₁.trans h21.2.symm)
        have hpuEq : euclideanDist (P p) (P (cyclicAdvance p k.val)) =
            euclideanDist (P p) (P u) :=
          euclideanDist_eq_of_sqDist_eq (h21.1.trans hpu.symm)
        linarith
      · exact Or.inl ⟨h31.2, h31.1⟩
      · exact Or.inr ⟨h32.2, h32.1⟩
    have hdegree := erlv_p_degree_le_of_arc_cards S 2 1 3
      (by simpa [left, Np, p, puoff] using hleftCard)
      (by simpa [tip, Np, p, puoff] using htipOne)
      (by simpa [right, Np, p, puoff] using hrightCard)
    exact high_degree_le_six_false S (cyclicAdvance S.x 1) hdegree
  · have htailCard := D.xtail_card (by
      simpa [x, p, u] using show sqDist (P x) (P u) ≤ sqDist (P p) (P u) by
        rw [hxuD₂, hpu])
    exact case12_bzero_false_of_tail_card_le_two S htailCard

private theorem case21_d2_equal_d3_pivot_impossible
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (D : Case21D2Prepared S)
    (hpu : sqDist (P (cyclicAdvance S.x 1))
      (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3))) = d₃)
    (hpuLtXu : sqDist (P (cyclicAdvance S.x 1))
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3))) <
      sqDist (P S.x) (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3)))) : False := by
  classical
  let x := S.x
  let p := cyclicAdvance x 1
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3)
  let uoff := erlvUOffset S
  let puoff := erlvPUOffset S
  let Np := ccwNeighborOffsets P d₁ d₂ d₃ p
  let left := Np.filter fun k ↦ k.val < puoff
  let tip := Np.filter fun k ↦ k.val = puoff
  let right := Np.filter fun k ↦ puoff < k.val
  have hleftHalf : ∀ k ∈ left, InLeftOpenHalfPlane (P x) (P p)
      (P (cyclicAdvance p k.val)) := by
    simpa [left, Np, x, p, puoff] using D.left_half
  have hrightCard : right.card ≤ 3 := by
    simpa [right, Np, p, puoff] using D.right_card
  have htipOne : tip.card ≤ 1 := by
    simpa [tip, Np, p, puoff] using D.tip_card
  have hpuAdj : TopThreeAdjacent P d₁ d₂ d₃ p u := by
    refine ⟨?_, Or.inr (Or.inr ?_)⟩
    · simpa [x, p, u] using D.p_ne_u
    · simpa [x, p, u] using hpu
  have hxuAdj := top_three_adjacent_of_strictly_longer S.classes hpuAdj (by
    simpa [x, p, u] using hpuLtXu)
  have hxuCases : sqDist (P x) (P u) = d₁ ∨
      sqDist (P x) (P u) = d₂ := by
    rcases hxuAdj.2 with h₁ | h₂ | h₃
    · exact Or.inl h₁
    · exact Or.inr h₂
    · linarith
  rcases hxuCases with hxuD₁ | hxuD₂
  · have hleftZero : left.card ≤ 0 := by
      have hleftEmpty : left = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hkData := Finset.mem_filter.mp hk
        have hpRAdj := (Finset.mem_filter.mp hkData.1).2.2
        have hpoint : cyclicAdvance p k.val = cyclicAdvance x (1 + k.val) := by
          simp [p, cyclicAdvance_add]
        have hquadRaw := cyclic_strict_convex_quad_offsets S.convex x
          (a := 0) (b := 1) (c := 1 + k.val) (d := uoff)
          (by omega) (by
            have hk0 := (Finset.mem_filter.mp hkData.1).2.1
            exact Nat.add_lt_add_left (Fin.pos_iff_ne_zero.mpr hk0) 1)
          (by
            have hpuAdd : 1 + puoff = uoff := by
              have huPos : 0 < erlvUOffset S := by
                have hu3 := (erlv_u_z_offset_data S).1
                omega
              dsimp [puoff, erlvPUOffset, uoff]
              omega
            omega) (by simpa [uoff] using D.uoff_lt)
        rw [← hpoint, ← D.u_index] at hquadRaw
        have hquad : StrictConvexQuad (P x) (P p)
            (P (cyclicAdvance p k.val)) (P u) := by simpa [x, p, u] using hquadRaw
        have hed := edge_diagonal_inequality_rotated hquad
        have hcompare : sqDist (P p) (P (cyclicAdvance p k.val)) <
            sqDist (P x) (P (cyclicAdvance p k.val)) := by
          apply sqDist_lt_of_euclideanDist_lt
          have hxuGtPu : euclideanDist (P p) (P u) <
              euclideanDist (P x) (P u) :=
            euclideanDist_lt_of_sqDist_lt (by simpa [x, p, u] using hpuLtXu)
          linarith
        have hxRAdj := top_three_adjacent_of_strictly_longer
          S.classes hpRAdj hcompare
        have hslots := strict_top_three_rank_slots S.classes hpRAdj hxRAdj hcompare
        rcases hslots with h21 | h31 | h32
        · have hxuEq : euclideanDist (P x) (P u) =
              euclideanDist (P x) (P (cyclicAdvance p k.val)) :=
            euclideanDist_eq_of_sqDist_eq (hxuD₁.trans h21.2.symm)
          have hpuLtPR : euclideanDist (P p) (P u) <
              euclideanDist (P p) (P (cyclicAdvance p k.val)) :=
            euclideanDist_lt_of_sqDist_lt (by
              rw [show sqDist (P p) (P u) = d₃ by simpa [x, p, u] using hpu,
                h21.1]
              exact S.classes.1)
          linarith
        · have hxuEq : euclideanDist (P x) (P u) =
              euclideanDist (P x) (P (cyclicAdvance p k.val)) :=
            euclideanDist_eq_of_sqDist_eq (hxuD₁.trans h31.2.symm)
          have hpuEq : euclideanDist (P p) (P u) =
              euclideanDist (P p) (P (cyclicAdvance p k.val)) :=
            euclideanDist_eq_of_sqDist_eq (by
              simpa [x, p, u] using hpu.trans h31.1.symm)
          linarith
        · have hxuGtXR : euclideanDist (P x) (P (cyclicAdvance p k.val)) <
              euclideanDist (P x) (P u) :=
            euclideanDist_lt_of_sqDist_lt (by rw [h32.2, hxuD₁]; exact S.classes.2.1)
          have hpuEq : euclideanDist (P p) (P u) =
              euclideanDist (P p) (P (cyclicAdvance p k.val)) :=
            euclideanDist_eq_of_sqDist_eq (by
              simpa [x, p, u] using hpu.trans h32.1.symm)
          linarith
      simp [hleftEmpty]
    have hdegree := erlv_p_degree_le_of_arc_cards S 0 1 3
      (by simpa [left, Np, p, puoff] using hleftZero)
      (by simpa [tip, Np, p, puoff] using htipOne)
      (by simpa [right, Np, p, puoff] using hrightCard)
    exact high_degree_le_six_false S (cyclicAdvance S.x 1) (hdegree.trans (by omega))
  · have hleftCard : left.card ≤ 2 := by
      refine two_fixed_radius_pairs_card_le_two D.points_injective p x p
        (by simpa [x, p] using D.x_p_ne) (a₁ := d₁) (b₁ := d₂)
        (a₂ := d₁) (b₂ := d₃) hleftHalf ?_
      intro k hk
      have hkData := Finset.mem_filter.mp hk
      have hpRAdj := (Finset.mem_filter.mp hkData.1).2.2
      have hpoint : cyclicAdvance p k.val = cyclicAdvance x (1 + k.val) := by
        simp [p, cyclicAdvance_add]
      have hquadRaw := cyclic_strict_convex_quad_offsets S.convex x
        (a := 0) (b := 1) (c := 1 + k.val) (d := uoff)
        (by omega) (by
          have hk0 := (Finset.mem_filter.mp hkData.1).2.1
          exact Nat.add_lt_add_left (Fin.pos_iff_ne_zero.mpr hk0) 1)
        (by
          have hpuAdd : 1 + puoff = uoff := by
            have huPos : 0 < erlvUOffset S := by
              have hu3 := (erlv_u_z_offset_data S).1
              omega
            dsimp [puoff, erlvPUOffset, uoff]
            omega
          omega) (by simpa [uoff] using D.uoff_lt)
      rw [← hpoint, ← D.u_index] at hquadRaw
      have hquad : StrictConvexQuad (P x) (P p)
          (P (cyclicAdvance p k.val)) (P u) := by simpa [x, p, u] using hquadRaw
      have hed := edge_diagonal_inequality_rotated hquad
      have hcompare : sqDist (P p) (P (cyclicAdvance p k.val)) <
          sqDist (P x) (P (cyclicAdvance p k.val)) := by
        apply sqDist_lt_of_euclideanDist_lt
        have hxuGtPu : euclideanDist (P p) (P u) <
            euclideanDist (P x) (P u) :=
          euclideanDist_lt_of_sqDist_lt (by simpa [x, p, u] using hpuLtXu)
        linarith
      have hxRAdj := top_three_adjacent_of_strictly_longer
        S.classes hpRAdj hcompare
      have hslots := strict_top_three_rank_slots S.classes hpRAdj hxRAdj hcompare
      rcases hslots with h21 | h31 | h32
      · exact Or.inl ⟨h21.2, h21.1⟩
      · exact Or.inr ⟨h31.2, h31.1⟩
      · exfalso
        have hxuEq : euclideanDist (P x) (P u) =
            euclideanDist (P x) (P (cyclicAdvance p k.val)) :=
          euclideanDist_eq_of_sqDist_eq (hxuD₂.trans h32.2.symm)
        have hpuEq : euclideanDist (P p) (P u) =
            euclideanDist (P p) (P (cyclicAdvance p k.val)) :=
          euclideanDist_eq_of_sqDist_eq (by
            simpa [x, p, u] using hpu.trans h32.1.symm)
        linarith
    have hdegree := erlv_p_degree_le_of_arc_cards S 2 1 3
      (by simpa [left, Np, p, puoff] using hleftCard)
      (by simpa [tip, Np, p, puoff] using htipOne)
      (by simpa [right, Np, p, puoff] using hrightCard)
    exact high_degree_le_six_false S (cyclicAdvance S.x 1) hdegree

private theorem case21_d2_low_pivot_impossible
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) (D : Case21D2Prepared S)
    (hpuLow : sqDist (P (cyclicAdvance S.x 1))
      (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3))) ≤ d₃)
    (hpuLtXu : sqDist (P (cyclicAdvance S.x 1))
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3))) <
      sqDist (P S.x) (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance S.x 3)))) : False := by
  classical
  let x := S.x
  let p := cyclicAdvance x 1
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3)
  let uoff := erlvUOffset S
  let puoff := erlvPUOffset S
  let Np := ccwNeighborOffsets P d₁ d₂ d₃ p
  let left := Np.filter fun k ↦ k.val < puoff
  let tip := Np.filter fun k ↦ k.val = puoff
  let right := Np.filter fun k ↦ puoff < k.val
  have hleftHalf : ∀ k ∈ left, InLeftOpenHalfPlane (P x) (P p)
      (P (cyclicAdvance p k.val)) := by
    simpa [left, Np, x, p, puoff] using D.left_half
  have hrightCard : right.card ≤ 3 := by
    simpa [right, Np, p, puoff] using D.right_card
  have hleftCardThree : left.card ≤ 3 := by
    refine three_fixed_radius_pairs_card_le_three D.points_injective p x p
      (by simpa [x, p] using D.x_p_ne) (a₁ := d₁) (b₁ := d₂)
      (a₂ := d₁) (b₂ := d₃) (a₃ := d₂) (b₃ := d₃) hleftHalf ?_
    intro k hk
    have hkData := Finset.mem_filter.mp hk
    have hpRAdj := (Finset.mem_filter.mp hkData.1).2.2
    have hpoint : cyclicAdvance p k.val = cyclicAdvance x (1 + k.val) := by
      simp [p, cyclicAdvance_add]
    have hquadRaw := cyclic_strict_convex_quad_offsets S.convex x
      (a := 0) (b := 1) (c := 1 + k.val) (d := uoff)
      (by omega) (by
        have hk0 := (Finset.mem_filter.mp hkData.1).2.1
        exact Nat.add_lt_add_left (Fin.pos_iff_ne_zero.mpr hk0) 1)
      (by
        have hpuAdd : 1 + puoff = uoff := by
          have huPos : 0 < erlvUOffset S := by
            have hu3 := (erlv_u_z_offset_data S).1
            omega
          dsimp [puoff, erlvPUOffset, uoff]
          omega
        omega) (by simpa [uoff] using D.uoff_lt)
    rw [← hpoint, ← D.u_index] at hquadRaw
    have hquad : StrictConvexQuad (P x) (P p)
        (P (cyclicAdvance p k.val)) (P u) := by simpa [x, p, u] using hquadRaw
    have hed := edge_diagonal_inequality_rotated hquad
    have hcompare : sqDist (P p) (P (cyclicAdvance p k.val)) <
        sqDist (P x) (P (cyclicAdvance p k.val)) := by
      apply sqDist_lt_of_euclideanDist_lt
      have hxuGtPu : euclideanDist (P p) (P u) < euclideanDist (P x) (P u) :=
        euclideanDist_lt_of_sqDist_lt (by simpa [x, p, u] using hpuLtXu)
      linarith
    have hxRAdj := top_three_adjacent_of_strictly_longer
      S.classes hpRAdj hcompare
    have hslots := strict_top_three_rank_slots S.classes hpRAdj hxRAdj hcompare
    rcases hslots with h21 | h31 | h32
    · exact Or.inl ⟨h21.2, h21.1⟩
    · exact Or.inr (Or.inl ⟨h31.2, h31.1⟩)
    · exact Or.inr (Or.inr ⟨h32.2, h32.1⟩)
  by_cases hpuStrict : sqDist (P p) (P u) < d₃
  · have htipZero : tip.card ≤ 0 := by
      have htipEmpty : tip = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hkData := Finset.mem_filter.mp hk
        have hkRank := (Finset.mem_filter.mp hkData.1).2.2.2
        have hkPoint : cyclicAdvance p k.val = u := by
          dsimp [x, p, u]
          rw [hkData.2, ← D.pu_index]
        rcases hkRank with h₁ | h₂ | h₃
        · have hpuRank : sqDist (P p) (P u) = d₁ := by rw [← hkPoint]; exact h₁
          rw [hpuRank] at hpuStrict
          linarith [S.classes.1, S.classes.2.1]
        · have hpuRank : sqDist (P p) (P u) = d₂ := by rw [← hkPoint]; exact h₂
          rw [hpuRank] at hpuStrict
          linarith [S.classes.1]
        · have hpuRank : sqDist (P p) (P u) = d₃ := by rw [← hkPoint]; exact h₃
          linarith
      simp [htipEmpty]
    have hdegree := erlv_p_degree_le_of_arc_cards S 3 0 3
      (by simpa [left, Np, p, puoff] using hleftCardThree)
      (by simpa [tip, Np, p, puoff] using htipZero)
      (by simpa [right, Np, p, puoff] using hrightCard)
    exact high_degree_le_six_false S (cyclicAdvance S.x 1) hdegree
  · have hpu : sqDist (P (cyclicAdvance S.x 1))
        (P (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance S.x 3))) = d₃ :=
      le_antisymm hpuLow (le_of_not_gt (by simpa [x, p, u] using hpuStrict))
    exact case21_d2_equal_d3_pivot_impossible S D hpu hpuLtXu

private theorem case21_d2_left_half
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (S : ErLVAtVertexUseSite P d₁ d₂ d₃) :
    ∀ k ∈ (ccwNeighborOffsets P d₁ d₂ d₃
        (cyclicAdvance S.x 1)).filter (fun k ↦ k.val < erlvPUOffset S),
      InLeftOpenHalfPlane (P S.x) (P (cyclicAdvance S.x 1))
        (P (cyclicAdvance (cyclicAdvance S.x 1) k.val)) := by
  classical
  intro k hk
  have hkData := Finset.mem_filter.mp hk
  have hk0 := (Finset.mem_filter.mp hkData.1).2.1
  have hkpos : 0 < k.val := Fin.pos_iff_ne_zero.mpr hk0
  have hsum : 1 + k.val < n := by
    have hpuAdd : 1 + erlvPUOffset S = erlvUOffset S := by
      have huPos : 0 < erlvUOffset S := by
        have hu3 := (erlv_u_z_offset_data S).1
        omega
      dsimp [erlvPUOffset]
      omega
    have hOffsets := erlv_u_z_offset_data S
    omega
  have h := cyclic_offset_in_consecutive_left_open_half_plane S.convex S.x
    (a := 0) (k := 1 + k.val) (by omega) hsum
  have hpoint : cyclicAdvance (cyclicAdvance S.x 1) k.val =
      cyclicAdvance S.x (1 + k.val) := by simp [cyclicAdvance_add]
  rw [← hpoint] at h
  simpa using h

/-- Session-9 obligation 4/8: terminal color `(2,1)-d₂` (paper Section 8). -/
theorem erlv_at_vertex_case21_other_d2_impossible_of_tail :
    ErLVAtVertexCase21OtherD2Impossible := by
  intro n _ P d₁ d₂ d₃ S h21 hOther
  classical
  let x := S.x
  let p := cyclicAdvance x 1
  let q := cyclicAdvance x 2
  let t := cyclicAdvance x 3
  let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ t
  let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
  let β := S.pair.second.rightMoves
  let uoff := erlvUOffset S
  let puoff := erlvPUOffset S
  let zoff := erlvZOffset S
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (S.highDegree S.x)
  have hβLe : β ≤ 1 := by
    have hBudget := S.pair.second.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case21] at h21
    dsimp [β]
    omega
  have hβZero : β = 0 := by
    by_contra hne
    have hβOne : β = 1 := by omega
    have hPath : K3CoverSequence P t u 1 1 := by
      simpa only [t, u, β, hβOne, h21.2] using S.pair.second.path
    have hEnd := K3CoverSequence.one_left_one_right_end_at_d1
      S.classes (by simpa [t, u] using S.second_start_adjacent) hPath
    have hretreat : cyclicRetreat t 1 = q := by
      have h := cyclicRetreat_advance x (k := 3) (m := 1) (by omega) (by omega)
      simpa [t, q] using h
    have hOther' : sqDist (P q) (P (cyclicAdvance u 1)) = d₂ := by
      simpa [q, u, β, hβOne, x] using hOther
    rw [hretreat] at hEnd
    linarith [S.classes.2.1]
  have hOffsets := erlv_u_z_offset_data S
  have huoff3 : 3 < uoff := by simpa [uoff] using hOffsets.1
  have huz : uoff + 3 ≤ zoff := by simpa [uoff, zoff] using hOffsets.2.1
  have hzoffn : zoff < n := by simpa [zoff] using hOffsets.2.2.1
  have huoffn : uoff < n := by omega
  have huIndex : u = cyclicAdvance x uoff := by
    simpa [u, t, x, uoff] using hOffsets.2.2.2.1
  have hzIndex : z = cyclicAdvance x zoff := by
    simpa [z, x, zoff] using hOffsets.2.2.2.2
  have hPUOffsets := erlv_p_u_offset_data S
  have hpuoff2 : 2 < puoff := by simpa [puoff] using hPUOffsets.1
  have hpuoffn : puoff < n := by simpa [puoff] using hPUOffsets.2.1
  have huPIndex : u = cyclicAdvance p puoff := by
    simpa [u, t, p, x, puoff] using hPUOffsets.2.2
  have hBZero : S.pair.first.leftMoves = 0 := by
    have hBudget := S.pair.first.coverBudget
    dsimp only [ErLVAtVertexUseSite.Case21] at h21
    omega
  have hFirstPath : K3CoverSequence P z x 0 2 := by
    simpa only [z, x, hBZero, h21.1] using S.pair.first.path
  have hFirstRanks := right_right_cover_rank_ladder S.classes
    (by simpa [z, x] using S.first_start_adjacent) hFirstPath
  have hxz : sqDist (P x) (P z) = d₃ := by
    simpa only [sqDist_comm] using hFirstRanks.1
  have hpz : sqDist (P p) (P z) = d₂ := by
    simpa only [p, x, sqDist_comm] using hFirstRanks.2.1
  have hqz : sqDist (P q) (P z) = d₁ := by
    simpa only [q, x, sqDist_comm] using hFirstRanks.2.2
  have hqu : sqDist (P q) (P u) = d₂ := by
    simpa [q, u, β, hβZero, x] using hOther
  have hSecondPath : K3CoverSequence P t u 1 0 := by
    simpa only [t, u, β, hβZero, h21.2] using S.pair.second.path
  have hSecondCover : IsLeftCover P t u := by
    cases hSecondPath with
    | left h _ => exact h
  have htu : sqDist (P t) (P u) = d₃ := by
    have hStart : TopThreeAdjacent P d₁ d₂ d₃ t u := by
      simpa [t, u] using S.second_start_adjacent
    have hretreat : cyclicRetreat t 1 = q := by
      have h := cyclicRetreat_advance x (k := 3) (m := 1) (by omega) (by omega)
      simpa [t, q] using h
    have hGrow : sqDist (P t) (P u) < sqDist (P q) (P u) := by
      simpa only [IsLeftCover, hretreat] using hSecondCover
    rcases hStart.2 with h₁ | h₂ | h₃
    · linarith [S.classes.2.1]
    · linarith
    · exact h₃
  have hretreat : cyclicRetreat t 1 = q := by
    have h := cyclicRetreat_advance x (k := 3) (m := 1) (by omega) (by omega)
    simpa [t, q] using h
  have hTerminal : IsMajorant P q u := by
    have h := S.pair.second.terminal
    change IsMajorant P (cyclicRetreat t S.pair.second.leftMoves)
      (cyclicAdvance u β) at h
    rw [h21.2, hβZero, cyclicAdvance_zero, hretreat] at h
    exact h
  have hretreatQ : cyclicRetreat q 1 = p := by
    have h := cyclicRetreat_advance x (k := 2) (m := 1) (by omega) (by omega)
    simpa [q, p] using h
  have hpuLe : sqDist (P p) (P u) ≤ d₂ := by
    rw [← hqu]
    apply le_of_not_gt
    intro hgt
    apply hTerminal.1
    change sqDist (P q) (P u) < sqDist (P (cyclicRetreat q 1)) (P u)
    rw [hretreatQ]
    exact hgt
  have hpuNe : p ≠ u := by
    rw [huIndex]
    exact cyclicAdvance_ne_of_lt x (by omega) huoffn (by omega)
  have hInjective : Function.Injective P :=
    cyclic_strict_convex_injective S.convex (by omega)
  have hxp : P x ≠ P p := by
    have h := cyclic_strict_convex_boundary_points_ne S.convex (by omega) x
    simpa [p, cyclicAdvance_one_eq_next] using h
  have hpq : P p ≠ P q := by
    have h := cyclic_strict_convex_boundary_points_ne S.convex (by omega) p
    have hqFromP : q = cyclicAdvance p 1 := by
      simp [p, q, cyclicAdvance_add]
    simpa [hqFromP, cyclicAdvance_one_eq_next] using h
  let Nx := ccwNeighborOffsets P d₁ d₂ d₃ x
  let xtail := Nx.filter fun k ↦ uoff < k.val
  have hxtailCardTwo
      (hanchor : sqDist (P x) (P u) ≤ sqDist (P p) (P u)) :
      xtail.card ≤ 2 := by
    simpa [xtail, Nx, uoff, x] using case21_d2_xtail_card_le_two S
      (by simpa [x, z] using hxz) (by simpa [x, p, z] using hpz)
      (by simpa [x, p, u] using hanchor)
  let Np := ccwNeighborOffsets P d₁ d₂ d₃ p
  let left := Np.filter fun k ↦ k.val < puoff
  let tip := Np.filter fun k ↦ k.val = puoff
  let right := Np.filter fun k ↦ puoff < k.val
  have hleftHalf : ∀ k ∈ left, InLeftOpenHalfPlane (P x) (P p)
      (P (cyclicAdvance p k.val)) := by
    simpa [left, Np, x, p, puoff] using case21_d2_left_half S
  have hrightHalf : ∀ k ∈ right, InLeftOpenHalfPlane (P p) (P q)
      (P (cyclicAdvance p k.val)) := by
    intro k hk
    have hkLower := (Finset.mem_filter.mp hk).2
    have h := cyclic_offset_in_left_open_half_plane S.convex p
      (k := k.val) (by omega) k.isLt
    have hqFromP : q = cyclicAdvance p 1 := by
      simp [p, q, cyclicAdvance_add]
    simpa [q, hqFromP, cyclicAdvance_one_eq_next] using h
  have hrightCard : right.card ≤ 3 := by
    refine three_fixed_radius_pairs_card_le_three hInjective p p q hpq
      (a₁ := d₂) (b₁ := d₁) (a₂ := d₃) (b₂ := d₁)
      (a₃ := d₃) (b₃ := d₂) hrightHalf ?_
    intro k hk
    have hkData := Finset.mem_filter.mp hk
    have hpRAdj := (Finset.mem_filter.mp hkData.1).2.2
    have hquadRaw := cyclic_strict_convex_quad_offsets S.convex p
      (a := 0) (b := 1) (c := puoff) (d := k.val)
      (by omega) (by omega) (by omega) k.isLt
    rw [← huPIndex] at hquadRaw
    have hqFromP : q = cyclicAdvance p 1 := by
      simp [p, q, cyclicAdvance_add]
    have hquad : StrictConvexQuad (P p) (P q) (P u)
        (P (cyclicAdvance p k.val)) := by simpa [hqFromP] using hquadRaw
    have hcompare := far_arc_strict_center_comparison hquad (by
      rw [hqu]
      exact hpuLe)
    have hqRAdj := top_three_adjacent_of_strictly_longer S.classes hpRAdj hcompare
    exact strict_top_three_rank_slots S.classes hpRAdj hqRAdj hcompare
  have htipOne : tip.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro k ell hk hell
    have hkVal := (Finset.mem_filter.mp hk).2
    have hellVal := (Finset.mem_filter.mp hell).2
    apply Fin.ext
    omega
  let D : Case21D2Prepared S := {
    tu := by simpa [x, t, u] using htu
    xz := by simpa [x, z] using hxz
    pz := by simpa [x, p, z] using hpz
    qz := by simpa [x, q, z] using hqz
    qu := by simpa [x, q, u] using hqu
    pu_le := by simpa [x, p, u] using hpuLe
    p_ne_u := by simpa [x, p, u] using hpuNe
    uoff_lt := by simpa [uoff] using huoffn
    u_index := by simpa [x, u, uoff] using huIndex
    pu_index := by simpa [x, p, u, puoff] using huPIndex
    points_injective := hInjective
    x_p_ne := by simpa [x, p] using hxp
    left_half := by simpa [left, Np, x, p, puoff] using hleftHalf
    right_card := by simpa [right, Np, p, puoff] using hrightCard
    tip_card := by simpa [tip, Np, p, puoff] using htipOne
    xtail_card := by
      intro hanchor
      simpa [xtail, Nx, uoff, x] using hxtailCardTwo (by
        simpa [x, p, u] using hanchor) }
  by_cases hpuAbove : d₃ < sqDist (P p) (P u)
  · exact case21_d2_above_impossible S D (by simpa [x, p, u] using hpuAbove)
  · have hpuLow : sqDist (P p) (P u) ≤ d₃ := le_of_not_gt hpuAbove
    by_cases hxuLe : sqDist (P x) (P u) ≤ sqDist (P p) (P u)
    · have htailCard := D.xtail_card (by simpa [x, p, u] using hxuLe)
      exact case12_bzero_false_of_tail_card_le_two S htailCard
    · exact case21_d2_low_pivot_impossible S D
        (by simpa [x, p, u] using hpuLow)
        (by simpa [x, p, u] using lt_of_not_ge hxuLe)
/-- All eight terminal-color obligations are now kernel proofs. -/
theorem erlv_at_vertex_exceptional_branches_impossible_of_tail :
    ErLVAtVertexExceptionalBranchesImpossible :=
  erlv_at_vertex_exceptional_branches_impossible_of_remaining_three
    erlv_at_vertex_case12_other_d1_impossible_of_tail
    erlv_at_vertex_case21_other_d1_impossible_of_tail
    erlv_at_vertex_case21_other_d2_impossible_of_tail

/-- The closed eight-color gate proves the source's strict inner-endpoint
order without the formerly postulated coordinated exchange. -/
theorem erlv_inner_endpoint_separation_complete_of_tail :
    ErLVInnerEndpointSeparationComplete :=
  erlv_inner_endpoint_separation_complete_of_at_vertex_closure
    erlv_at_vertex_exceptional_branches_impossible_of_tail

/-- The full source-facing ErLV majorant arc-nesting proposition is now an
unconditional kernel theorem. -/
theorem erlv_majorant_arc_nesting_complete_of_tail :
    ErLVMajorantArcNestingComplete :=
  erlv_majorant_arc_nesting_complete_of_at_vertex_closure
    erlv_at_vertex_exceptional_branches_impossible_of_tail

end LeanPool.Erdos132ConvexK3
