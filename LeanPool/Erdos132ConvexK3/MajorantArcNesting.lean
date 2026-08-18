/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.GlobalReduction
import LeanPool.Erdos132ConvexK3.Geometry
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ErLV majorant arc nesting

This file formalizes the geometric core of Erdos--Lovasz--Vesztergombi's
Proposition 2.6 argument.  A terminal cover edge makes the two exterior
boundary angles acute.  If two such majorants were avoiding, cyclic
convexity propagates those local inequalities to all four angles of their
quadrilateral, contradicting `strict_convex_quad_not_all_acute`.
-/

namespace LeanPool.Erdos132ConvexK3

theorem dot_comm (u v : Point ℝ) : dot u v = dot v u := by
  simp [dot]
  ring

theorem sqDist_pos_of_ne {a b : Point ℝ} (h : a ≠ b) : 0 < sqDist a b := by
  by_contra hn
  have hle : sqDist a b ≤ 0 := le_of_not_gt hn
  have h1 : (b.1 - a.1) ^ 2 = 0 := by
    have hsq1 : 0 ≤ (b.1 - a.1) ^ 2 := sq_nonneg _
    have hsq2 : 0 ≤ (b.2 - a.2) ^ 2 := sq_nonneg _
    unfold sqDist at hle
    nlinarith
  have h2 : (b.2 - a.2) ^ 2 = 0 := by
    have hsq1 : 0 ≤ (b.1 - a.1) ^ 2 := sq_nonneg _
    have hsq2 : 0 ≤ (b.2 - a.2) ^ 2 := sq_nonneg _
    unfold sqDist at hle
    nlinarith
  apply h
  apply Prod.ext
  · exact (sub_eq_zero.mp (sq_eq_zero_iff.mp h1)).symm
  · exact (sub_eq_zero.mp (sq_eq_zero_iff.mp h2)).symm

/-- A failed endpoint cover gives a strict acute-angle dot product, provided
the polygon side used by that cover is nondegenerate. -/
theorem dot_pos_of_sqDist_le
    {a b p : Point ℝ} (hap : a ≠ p)
    (hshort : sqDist p b ≤ sqDist a b) :
    0 < dot (b - a) (p - a) := by
  have hap2 := sqDist_pos_of_ne hap
  have hid :
      2 * dot (b - a) (p - a) = sqDist a p + sqDist a b - sqDist p b := by
    simp [dot, sqDist]
    ring
  nlinarith

theorem dot_self_pos_of_cross_pos_left
    {u v : Point ℝ} (hcross : 0 < cross u v) : 0 < dot u u := by
  have h1 : 0 ≤ u.1 ^ 2 := sq_nonneg _
  have h2 : 0 ≤ u.2 ^ 2 := sq_nonneg _
  by_contra hn
  have hle : dot u u ≤ 0 := le_of_not_gt hn
  have hu1 : u.1 = 0 := by
    simp [dot] at hle
    nlinarith
  have hu2 : u.2 = 0 := by
    simp [dot] at hle
    nlinarith
  simp [cross, hu1, hu2] at hcross

theorem dot_self_pos_of_cross_pos_right
    {u v : Point ℝ} (hcross : 0 < cross u v) : 0 < dot v v := by
  have hneg : 0 < cross (-v) u := by
    dsimp [cross] at hcross ⊢
    nlinarith
  simpa [dot] using dot_self_pos_of_cross_pos_left hneg

/-- A ray strictly between two rays in an open half-plane is their positive
linear combination.  This determinant identity transfers an acute endpoint
inequality to the intermediate ray. -/
theorem dot_pos_of_cross_between_left
    {u w v : Point ℝ}
    (huw : 0 < cross u w) (hwv : 0 < cross w v) (huv : 0 < cross u v)
    (hacute : 0 < dot u v) : 0 < dot u w := by
  have huu := dot_self_pos_of_cross_pos_left huw
  have hsum : 0 < cross w v * dot u u + cross u w * dot u v :=
    add_pos (mul_pos hwv huu) (mul_pos huw hacute)
  have hid :
      cross u v * dot u w = cross w v * dot u u + cross u w * dot u v := by
    simp [cross, dot]
    ring
  rw [← hid] at hsum
  rcases mul_pos_iff.mp hsum with hpos | hneg
  · exact hpos.2
  · linarith

theorem dot_pos_of_cross_between_right
    {u w v : Point ℝ}
    (huw : 0 < cross u w) (hwv : 0 < cross w v) (huv : 0 < cross u v)
    (hacute : 0 < dot u v) : 0 < dot v w := by
  have hvv := dot_self_pos_of_cross_pos_right hwv
  have hsum : 0 < cross w v * dot v u + cross u w * dot v v := by
    have hsymm : dot v u = dot u v := by simp [dot]; ring
    rw [hsymm]
    exact add_pos (mul_pos hwv hacute) (mul_pos huw hvv)
  have hid :
      cross u v * dot v w = cross w v * dot v u + cross u w * dot v v := by
    simp [cross, dot]
    ring
  rw [← hid] at hsum
  rcases mul_pos_iff.mp hsum with hpos | hneg
  · exact hpos.2
  · linarith

theorem cross_trans_of_common_half_plane
    {e u v w : Point ℝ}
    (heu : 0 < cross e u) (hev : 0 < cross e v) (hew : 0 < cross e w)
    (huv : 0 < cross u v) (hvw : 0 < cross v w) : 0 < cross u w := by
  have hsum : 0 < cross e w * cross u v + cross e u * cross v w :=
    add_pos (mul_pos hew huv) (mul_pos heu hvw)
  have hid :
      cross e v * cross u w = cross e w * cross u v + cross e u * cross v w := by
    simp [cross]
    ring
  rw [← hid] at hsum
  rcases mul_pos_iff.mp hsum with hpos | hneg
  · exact hpos.2
  · linarith

/-- Positive consecutive turns are transitive while the whole chain stays in
one open half-plane. -/
theorem positive_cross_chain
    (V : ℕ → Point ℝ) (N : ℕ)
    (hbase : ∀ r, 1 < r → r ≤ N → 0 < cross (V 1) (V r))
    (hstep : ∀ r, 1 ≤ r → r < N → 0 < cross (V r) (V (r + 1)))
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) (hkN : k ≤ N) :
    0 < cross (V j) (V k) := by
  have hjk' : j + 1 ≤ k := by omega
  revert hkN
  induction k, hjk' using Nat.le_induction with
  | base =>
      intro hbound
      exact hstep j hj (by omega)
  | succ k hle ih =>
      intro hbound
      by_cases hj1 : j = 1
      · subst j
        exact hbase (k + 1) (by omega) hbound
      · apply cross_trans_of_common_half_plane (e := V 1) (v := V k)
        · exact hbase j (by omega) (by omega)
        · exact hbase k (by omega) (by omega)
        · exact hbase (k + 1) (by omega) hbound
        · exact ih (by omega) (by omega)
        · exact hstep k (by omega) (by omega)

/-- The boundary-half-plane definition of cyclic strict convexity implies
positive orientation for every three labels in increasing order from zero. -/
theorem cyclic_strict_convex_turn_zero_of_lt
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) {j k : Fin n}
    (hj : 0 < j) (hjk : j < k) : 0 < turn (P 0) (P j) (P k) := by
  have hn : 2 < n := by omega
  let V : ℕ → Point ℝ := fun r ↦ P (Fin.ofNat n r) - P 0
  have hbase : ∀ r, 1 < r → r ≤ n - 1 → 0 < cross (V 1) (V r) := by
    intro r hr1 hrN
    have hrn : r < n := by omega
    have h1n : 1 < n := by omega
    have hirVal : (Fin.ofNat n r).val = r := by
      simp [Fin.ofNat, Nat.mod_eq_of_lt hrn]
    have hi1Val : (Fin.ofNat n 1).val = 1 := by
      simp [Fin.ofNat, Nat.mod_eq_of_lt h1n]
    have hi1 : Fin.ofNat n 1 = cyclicNext (0 : Fin n) := by
      apply Fin.ext
      simp [cyclicNext, Nat.mod_eq_of_lt h1n]
    have hir0 : Fin.ofNat n r ≠ (0 : Fin n) := by
      intro heq
      have := congrArg Fin.val heq
      change (Fin.ofNat n r).val = 0 at this
      rw [hirVal] at this
      omega
    have hir1 : Fin.ofNat n r ≠ cyclicNext (0 : Fin n) := by
      rw [← hi1]
      intro heq
      have := congrArg Fin.val heq
      change (Fin.ofNat n r).val = (Fin.ofNat n 1).val at this
      rw [hirVal, hi1Val] at this
      omega
    have hturn := hConvex 0 (Fin.ofNat n r) hir0 hir1
    rw [← hi1] at hturn
    simpa [V, turn, cross] using hturn
  have hstep : ∀ r, 1 ≤ r → r < n - 1 → 0 < cross (V r) (V (r + 1)) := by
    intro r hr1 hrN
    have hrn : r < n := by omega
    have hrsn : r + 1 < n := by omega
    let ir : Fin n := ⟨r, hrn⟩
    let irs : Fin n := ⟨r + 1, hrsn⟩
    have hir : Fin.ofNat n r = ir := by
      apply Fin.ext
      simp [ir, Fin.ofNat, Nat.mod_eq_of_lt hrn]
    have hirs : Fin.ofNat n (r + 1) = irs := by
      apply Fin.ext
      simp [irs, Fin.ofNat, Nat.mod_eq_of_lt hrsn]
    have hnext : cyclicNext ir = irs := by
      apply Fin.ext
      simp [ir, irs, cyclicNext, Fin.add_def, Nat.mod_eq_of_lt hrsn]
    have hzero : (0 : Fin n) ≠ ir := by
      intro heq
      have := congrArg Fin.val heq
      simp [ir] at this
      omega
    have hzeroNext : (0 : Fin n) ≠ cyclicNext ir := by
      rw [hnext]
      intro heq
      have := congrArg Fin.val heq
      change 0 = r + 1 at this
      omega
    have hturn := hConvex ir 0 hzero hzeroNext
    rw [hnext, ← hir, ← hirs] at hturn
    rw [← turn_cyclic] at hturn
    simpa [V, turn, cross] using hturn
  have hjVal : (Fin.ofNat n j.val).val = j.val := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt j.isLt]
  have hkVal : (Fin.ofNat n k.val).val = k.val := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt k.isLt]
  have hjEq : Fin.ofNat n j.val = j := Fin.ext hjVal
  have hkEq : Fin.ofNat n k.val = k := Fin.ext hkVal
  have hcross := positive_cross_chain V (n - 1) hbase hstep
    (j := j.val) (k := k.val) (by omega) hjk (by omega)
  dsimp [V] at hcross
  simpa [turn, cross] using hcross

/-- Relabel a cyclic configuration so that `base` becomes index zero. -/
def cyclicRotate
    {K : Type*} {n : ℕ} [_nonzero : NeZero n]
    (P : Fin n → Point K) (base : Fin n) : Fin n → Point K :=
  fun i ↦ P (base + i)

theorem cyclic_strict_convex_rotate
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n) :
    CyclicStrictConvex (cyclicRotate P base) := by
  intro i j hji hjnext
  have hnext : base + cyclicNext i = cyclicNext (base + i) := by
    simp only [cyclicNext]
    abel
  change 0 < turn (P (base + i)) (P (base + cyclicNext i)) (P (base + j))
  rw [hnext]
  apply hConvex (base + i) (base + j)
  · intro heq
    exact hji (add_left_cancel heq)
  · intro heq
    apply hjnext
    apply add_left_cancel (a := base)
    rw [hnext]
    exact heq

/-- Positive orientation for any three vertices described by increasing
cyclic offsets from an arbitrary base vertex. -/
theorem cyclic_strict_convex_turn_from_offsets
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n) {j k : Fin n}
    (hj : 0 < j) (hjk : j < k) :
    0 < turn (P base) (P (base + j)) (P (base + k)) := by
  have h := cyclic_strict_convex_turn_zero_of_lt
    (cyclic_strict_convex_rotate hConvex base) hj hjk
  simpa [cyclicRotate] using h

theorem cyclic_strict_convex_turn_advance
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n) {j k : ℕ}
    (hj : 0 < j) (hjk : j < k) (hkn : k < n) :
    0 < turn (P base) (P (cyclicAdvance base j)) (P (cyclicAdvance base k)) := by
  have hjn : j < n := by omega
  have hjVal : (Fin.ofNat n j).val = j := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt hjn]
  have hkVal : (Fin.ofNat n k).val = k := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt hkn]
  apply cyclic_strict_convex_turn_from_offsets hConvex base
  · change 0 < (Fin.ofNat n j).val
    rw [hjVal]
    exact hj
  · change (Fin.ofNat n j).val < (Fin.ofNat n k).val
    rw [hjVal, hkVal]
    exact hjk

/-- Positive orientation for three increasing positions in one unwrapped
window of the cyclic order.  The last two positions may exceed `n`; their
`Fin` representatives wrap automatically. -/
theorem cyclic_strict_convex_turn_unwrapped
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hwindow : c < a + n) :
    0 < turn (P (cyclicAdvance base a)) (P (cyclicAdvance base b))
      (P (cyclicAdvance base c)) := by
  have h := cyclic_strict_convex_turn_advance hConvex (cyclicAdvance base a)
    (j := b - a) (k := c - a) (by omega) (by omega) (by omega)
  rw [cyclicAdvance_add, cyclicAdvance_add] at h
  have habEq : a + (b - a) = b := by omega
  have hacEq : a + (c - a) = c := by omega
  simpa [habEq, hacEq] using h

theorem cyclicAdvance_period
    {n : ℕ} [NeZero n] (i : Fin n) (k : ℕ) :
    cyclicAdvance i (k + n) = cyclicAdvance i k := by
  apply Fin.ext
  simp [cyclicAdvance, Fin.ofNat, Fin.val_add, Nat.add_mod]

theorem cyclicRetreat_advance_one
    {n : ℕ} [NeZero n] (i : Fin n) {k : ℕ}
    (hk : 0 < k) (hkn : k < n) :
    cyclicRetreat (cyclicAdvance i k) 1 = cyclicAdvance i (k - 1) := by
  have h1n : 1 < n := by omega
  have hcast : Fin.ofNat n (k - 1) + Fin.ofNat n 1 = Fin.ofNat n k := by
    apply Fin.ext
    have hkEq : k - 1 + 1 = k := by omega
    simp [Fin.ofNat, Fin.val_add, hkEq, Nat.mod_eq_of_lt hkn, Nat.mod_eq_of_lt h1n]
  unfold cyclicRetreat cyclicAdvance
  rw [← hcast]
  abel

theorem cyclicRetreat_advance
    {n : ℕ} [NeZero n] (i : Fin n) {k m : ℕ}
    (hmk : m ≤ k) (hkn : k < n) :
    cyclicRetreat (cyclicAdvance i k) m = cyclicAdvance i (k - m) := by
  have hmn : m < n := lt_of_le_of_lt hmk hkn
  have hsubn : k - m < n := by omega
  have hcast : Fin.ofNat n (k - m) + Fin.ofNat n m = Fin.ofNat n k := by
    apply Fin.ext
    have hkm : k - m + m = k := by omega
    simp [Fin.ofNat, Fin.val_add, Nat.mod_eq_of_lt hmn, Nat.mod_eq_of_lt hsubn,
      Nat.mod_eq_of_lt hkn, hkm]
  unfold cyclicRetreat cyclicAdvance
  rw [← hcast]
  abel

theorem cyclicRetreat_eq_advance_complement
    {n : ℕ} [NeZero n] (i : Fin n) {k : ℕ}
    (hk : 0 < k) (hkn : k < n) :
    cyclicRetreat i k = cyclicAdvance i (n - k) := by
  have hsubn : n - k < n := by omega
  have hsum : Fin.ofNat n k + Fin.ofNat n (n - k) = 0 := by
    apply Fin.ext
    have hadd : k + (n - k) = n := by omega
    simp [Fin.ofNat, Fin.val_add, Nat.mod_eq_of_lt hkn, Nat.mod_eq_of_lt hsubn,
      hadd]
  have hneg : -Fin.ofNat n k = Fin.ofNat n (n - k) := by
    calc
      -Fin.ofNat n k = (Fin.ofNat n k + Fin.ofNat n (n - k)) - Fin.ofNat n k := by
        rw [hsum]
        abel
      _ = Fin.ofNat n (n - k) := by abel
  unfold cyclicRetreat cyclicAdvance
  rw [sub_eq_add_neg, hneg]

theorem cyclicAdvance_one_eq_next
    {n : ℕ} [NeZero n] (i : Fin n) : cyclicAdvance i 1 = cyclicNext i := by
  unfold cyclicAdvance cyclicNext
  have hOne : Fin.ofNat n 1 = (1 : Fin n) := by
    apply Fin.ext
    simp
  rw [hOne]

theorem cyclicNext_retreat_one
    {n : ℕ} [NeZero n] (i : Fin n) : cyclicNext (cyclicRetreat i 1) = i := by
  simp only [cyclicNext, cyclicRetreat]
  have hOne : Fin.ofNat n 1 = (1 : Fin n) := by
    apply Fin.ext
    simp
  rw [hOne]
  abel

theorem cyclicAdvance_ne_of_lt
    {n : ℕ} [NeZero n] (i : Fin n) {a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cyclicAdvance i a ≠ cyclicAdvance i b := by
  intro heq
  unfold cyclicAdvance at heq
  have hoff : Fin.ofNat n a = Fin.ofNat n b := add_left_cancel heq
  have hval : a = b := by
    simpa [Fin.ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using
      congrArg Fin.val hoff
  exact hab hval

theorem cyclic_strict_convex_boundary_points_ne
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (hn : 3 ≤ n) (i : Fin n) :
    P i ≠ P (cyclicNext i) := by
  let j := cyclicAdvance i 2
  have h2n : 2 < n := by omega
  have h1n : 1 < n := by omega
  have hji : j ≠ i := by
    have h := cyclicAdvance_ne_of_lt i h2n (by omega : 0 < n) (by omega : 2 ≠ 0)
    simpa [j] using h
  have hjnext : j ≠ cyclicNext i := by
    rw [← cyclicAdvance_one_eq_next]
    exact cyclicAdvance_ne_of_lt i h2n h1n (by omega)
  have hturn := hConvex i j hji hjnext
  intro heq
  rw [← heq] at hturn
  simp [turn] at hturn

theorem majorant_left_local_acute
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (hConvex : CyclicStrictConvex P) (hn : 3 ≤ n) (hMajorant : IsMajorant P i j) :
    0 < dot (P j - P i) (P (cyclicRetreat i 1) - P i) := by
  have hside : P i ≠ P (cyclicRetreat i 1) := by
    have h := cyclic_strict_convex_boundary_points_ne hConvex hn (cyclicRetreat i 1)
    rw [cyclicNext_retreat_one] at h
    exact h.symm
  apply dot_pos_of_sqDist_le hside
  exact le_of_not_gt hMajorant.1

theorem majorant_right_local_acute
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (hConvex : CyclicStrictConvex P) (hn : 3 ≤ n) (hMajorant : IsMajorant P i j) :
    0 < dot (P i - P j) (P (cyclicAdvance j 1) - P j) := by
  have hside : P j ≠ P (cyclicAdvance j 1) := by
    rw [cyclicAdvance_one_eq_next]
    exact cyclic_strict_convex_boundary_points_ne hConvex hn j
  apply dot_pos_of_sqDist_le hside
  simpa only [sqDist_comm] using le_of_not_gt hMajorant.2

theorem vertexDegree_le_pred
    {n : ℕ} [_nonzero : NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) (v : Fin n) :
    vertexDegree P d₁ d₂ d₃ v ≤ n - 1 := by
  unfold vertexDegree
  calc
    ((Finset.univ.erase v).filter fun j ↦
        sqDist (P v) (P j) = d₁ ∨ sqDist (P v) (P j) = d₂ ∨
          sqDist (P v) (P j) = d₃).card ≤ (Finset.univ.erase v).card :=
      Finset.card_filter_le _ _
    _ = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
        Fintype.card_fin]

theorem eight_le_card_of_degree_seven
    {n : ℕ} [_nonzero : NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (hdegree : 7 ≤ vertexDegree P d₁ d₂ d₃ v) : 8 ≤ n := by
  have hbound := vertexDegree_le_pred P d₁ d₂ d₃ v
  omega

theorem fin_ofNat_val
    {n : ℕ} [NeZero n] (k : Fin n) : Fin.ofNat n k.val = k := by
  apply Fin.ext
  simp

theorem ccwNeighborOffsets_card_eq_vertexDegree
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) (v : Fin n) :
    (ccwNeighborOffsets P d₁ d₂ d₃ v).card = vertexDegree P d₁ d₂ d₃ v := by
  classical
  unfold vertexDegree
  apply Finset.card_bij (fun k _ ↦ cyclicAdvance v k.val)
  · intro k hk
    have hkData := (Finset.mem_filter.mp hk).2
    have hkCast := fin_ofNat_val k
    have hneq : cyclicAdvance v k.val ≠ v := by
      intro heq
      unfold cyclicAdvance at heq
      rw [hkCast] at heq
      apply hkData.1
      apply add_left_cancel (a := v)
      simpa using heq
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hneq, Finset.mem_univ _⟩,
      hkData.2.2⟩
  · intro k₁ hk₁ k₂ hk₂ heq
    have h₁ := fin_ofNat_val k₁
    have h₂ := fin_ofNat_val k₂
    unfold cyclicAdvance at heq
    rw [h₁, h₂] at heq
    exact add_left_cancel heq
  · intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjErase := Finset.mem_erase.mp hjData.1
    let k : Fin n := j - v
    have hk0 : k ≠ 0 := by
      dsimp [k]
      exact sub_ne_zero.mpr hjErase.1
    have hkCast := fin_ofNat_val k
    have hvk : cyclicAdvance v k.val = j := by
      unfold cyclicAdvance
      rw [hkCast]
      dsimp [k]
      abel
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0, ?_⟩, hvk⟩
    rw [hvk]
    exact ⟨hjErase.1.symm, hjData.2⟩

theorem firstNeighborOffset_le_of_mem
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v k : Fin n}
    (hnonempty : (ccwNeighborOffsets P d₁ d₂ d₃ v).Nonempty)
    (hk : k ∈ ccwNeighborOffsets P d₁ d₂ d₃ v) :
    firstNeighborOffset P d₁ d₂ d₃ v ≤ k := by
  unfold firstNeighborOffset
  dsimp only
  rw [dite_eq_left hnonempty]
  exact Finset.min'_le _ _ hk

theorem firstClockwiseNeighborOffset_le_of_mem
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v k : Fin n}
    (hnonempty : (cwNeighborOffsets P d₁ d₂ d₃ v).Nonempty)
    (hk : k ∈ cwNeighborOffsets P d₁ d₂ d₃ v) :
    firstClockwiseNeighborOffset P d₁ d₂ d₃ v ≤ k := by
  unfold firstClockwiseNeighborOffset
  dsimp only
  rw [dite_eq_left hnonempty]
  exact Finset.min'_le _ _ hk

theorem firstNeighborGap_pos_of_degree_pos
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (hdegree : 0 < vertexDegree P d₁ d₂ d₃ v) :
    0 < firstNeighborGap P d₁ d₂ d₃ v := by
  have hne := (firstNeighborOffset_spec_of_degree_pos hdegree).1
  unfold firstNeighborGap
  apply Nat.pos_of_ne_zero
  intro hval
  apply hne
  apply Fin.ext
  simpa using hval

theorem firstClockwiseNeighborOffset_pos_of_degree_pos
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (hdegree : 0 < vertexDegree P d₁ d₂ d₃ v) :
    0 < (firstClockwiseNeighborOffset P d₁ d₂ d₃ v).val := by
  classical
  have hnon := cwNeighborOffsets_nonempty_of_degree_pos hdegree
  have hmem := firstClockwiseNeighborOffset_mem hnon
  have hne := (Finset.mem_filter.mp hmem).2.1
  apply Nat.pos_of_ne_zero
  intro hval
  apply hne
  apply Fin.ext
  simpa using hval

/-- With degree at least seven, the two first-neighbor gaps leave at least six
polygon sides between their endpoints. -/
theorem first_neighbor_gap_cw_budget
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (hdegree : 7 ≤ vertexDegree P d₁ d₂ d₃ v) :
    firstNeighborGap P d₁ d₂ d₃ v +
        (firstClockwiseNeighborOffset P d₁ d₂ d₃ v).val + 6 ≤ n := by
  classical
  have hpos : 0 < vertexDegree P d₁ d₂ d₃ v := by omega
  have hccw := ccwNeighborOffsets_nonempty_of_degree_pos hpos
  have hcw := cwNeighborOffsets_nonempty_of_degree_pos hpos
  let g := firstNeighborOffset P d₁ d₂ d₃ v
  let h := firstClockwiseNeighborOffset P d₁ d₂ d₃ v
  have hgmem : g ∈ ccwNeighborOffsets P d₁ d₂ d₃ v := by
    exact firstNeighborOffset_mem hccw
  have hhmem : h ∈ cwNeighborOffsets P d₁ d₂ d₃ v := by
    exact firstClockwiseNeighborOffset_mem hcw
  have hg0 : g ≠ 0 := (Finset.mem_filter.mp hgmem).2.1
  have hh0 : h ≠ 0 := (Finset.mem_filter.mp hhmem).2.1
  have hhpos : 0 < h.val := by
    apply Nat.pos_of_ne_zero
    intro hval
    apply hh0
    apply Fin.ext
    simpa using hval
  have hupper : ∀ k ∈ ccwNeighborOffsets P d₁ d₂ d₃ v, h.val + k.val ≤ n := by
    intro k hk
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
    have hle : h ≤ ell := firstClockwiseNeighborOffset_le_of_mem hcw hellmem
    have hellVal : ell.val = n - k.val := by
      dsimp [ell]
      rw [Fin.val_neg, ite_eq_right hkData.1]
    have hleVal : h.val ≤ ell.val := hle
    rw [hellVal] at hleVal
    omega
  let upper : Fin n := ⟨n - h.val, by omega⟩
  have hsubset :
      ccwNeighborOffsets P d₁ d₂ d₃ v ⊆ Finset.Icc g upper := by
    intro k hk
    apply Finset.mem_Icc.mpr
    constructor
    · exact firstNeighborOffset_le_of_mem hccw hk
    · change k.val ≤ n - h.val
      have := hupper k hk
      omega
  have hcard := Finset.card_le_card hsubset
  rw [Fin.card_Icc] at hcard
  have hcardEq' := ccwNeighborOffsets_card_eq_vertexDegree P d₁ d₂ d₃ v
  rw [hcardEq'] at hcard
  change vertexDegree P d₁ d₂ d₃ v ≤ (n - h.val) + 1 - g.val at hcard
  change g.val + h.val + 6 ≤ n
  omega

/-- Offset form of ErLV Proposition 2.6's geometric step.  If the endpoints
of two terminal edges occur as `v < v' < s' < s` in one unwrapped cyclic
window, the edges are avoiding, which is impossible. -/
theorem erlv_terminal_majorants_not_avoiding_of_offsets
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} (hConvex : CyclicStrictConvex P)
    (base : Fin n) {v vp sp s : ℕ}
    (hvv : v < vp) (hvsp : vp < sp) (hsps : sp < s) (hsn : s < n)
    (hFirst : IsMajorant P (cyclicAdvance base s) (cyclicAdvance base v))
    (hSecond : IsMajorant P (cyclicAdvance base vp) (cyclicAdvance base sp)) : False := by
  have hn3 : 3 ≤ n := by omega
  have hvpn : vp < n := by omega
  have hspn : sp < n := by omega
  have hvn : v < n := by omega
  have hvppos : 0 < vp := by omega
  have hspos : 0 < s := by omega
  have hpredVp := cyclicRetreat_advance_one base hvppos hvpn
  have hpredS := cyclicRetreat_advance_one base hspos hsn
  have hnextSp := cyclicAdvance_add base sp 1
  have hnextV := cyclicAdvance_add base v 1
  have hSecondLeft := majorant_left_local_acute hConvex hn3 hSecond
  have hSecondRight := majorant_right_local_acute hConvex hn3 hSecond
  have hFirstLeft := majorant_left_local_acute hConvex hn3 hFirst
  have hFirstRight := majorant_right_local_acute hConvex hn3 hFirst
  rw [hpredVp] at hSecondLeft
  rw [hnextSp] at hSecondRight
  rw [hpredS] at hFirstLeft
  rw [hnextV] at hFirstRight
  have hperiodV := cyclicAdvance_period base v
  have hperiodVp := cyclicAdvance_period base vp
  have hperiodSp := cyclicAdvance_period base sp
  have hquad : StrictConvexQuad
      (P (cyclicAdvance base vp)) (P (cyclicAdvance base sp))
      (P (cyclicAdvance base s)) (P (cyclicAdvance base v)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact cyclic_strict_convex_turn_unwrapped hConvex base hvsp hsps (by omega)
    · have h := cyclic_strict_convex_turn_unwrapped hConvex base
          (a := vp) (b := sp) (c := v + n) hvsp (by omega) (by omega)
      simpa [hperiodV] using h
    · have h := cyclic_strict_convex_turn_unwrapped hConvex base
          (a := sp) (b := s) (c := v + n) hsps (by omega) (by omega)
      simpa [hperiodV] using h
    · have h := cyclic_strict_convex_turn_unwrapped hConvex base
          (a := s) (b := v + n) (c := vp + n) (by omega) (by omega) (by omega)
      simpa [hperiodV, hperiodVp] using h
  have ha : 0 < dot
      (P (cyclicAdvance base sp) - P (cyclicAdvance base vp))
      (P (cyclicAdvance base v) - P (cyclicAdvance base vp)) := by
    by_cases hadj : v = vp - 1
    · simpa [hadj] using hSecondLeft
    · have hvpred : v < vp - 1 := by omega
      apply dot_pos_of_cross_between_left
        (u := P (cyclicAdvance base sp) - P (cyclicAdvance base vp))
        (w := P (cyclicAdvance base v) - P (cyclicAdvance base vp))
        (v := P (cyclicAdvance base (vp - 1)) - P (cyclicAdvance base vp))
      · have h := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := vp) (b := sp) (c := v + n) hvsp (by omega) (by omega)
        rw [hperiodV] at h
        simpa [turn, cross] using h
      · have h := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := vp) (b := v + n) (c := vp - 1 + n) (by omega) (by omega) (by omega)
        rw [hperiodV, cyclicAdvance_period base (vp - 1)] at h
        simpa [turn, cross] using h
      · have h := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := vp) (b := sp) (c := vp - 1 + n) hvsp (by omega) (by omega)
        rw [cyclicAdvance_period base (vp - 1)] at h
        simpa [turn, cross] using h
      · exact hSecondLeft
  have hb : 0 < dot
      (P (cyclicAdvance base vp) - P (cyclicAdvance base sp))
      (P (cyclicAdvance base s) - P (cyclicAdvance base sp)) := by
    by_cases hadj : s = sp + 1
    · simpa [hadj] using hSecondRight
    · have hnextlt : sp + 1 < s := by omega
      apply dot_pos_of_cross_between_right
        (u := P (cyclicAdvance base (sp + 1)) - P (cyclicAdvance base sp))
        (w := P (cyclicAdvance base s) - P (cyclicAdvance base sp))
        (v := P (cyclicAdvance base vp) - P (cyclicAdvance base sp))
      · have h := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := sp) (b := sp + 1) (c := s) (by omega) hnextlt (by omega)
        simpa [turn, cross] using h
      · have h := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := sp) (b := s) (c := vp + n) hsps (by omega) (by omega)
        rw [hperiodVp] at h
        simpa [turn, cross] using h
      · have h := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := sp) (b := sp + 1) (c := vp + n) (by omega) (by omega) (by omega)
        rw [hperiodVp] at h
        simpa [turn, cross] using h
      · rw [dot_comm]
        exact hSecondRight
  have hc : 0 < dot
      (P (cyclicAdvance base sp) - P (cyclicAdvance base s))
      (P (cyclicAdvance base v) - P (cyclicAdvance base s)) := by
    by_cases hadj : sp = s - 1
    · rw [dot_comm]
      simpa [hadj] using hFirstLeft
    · have hsppred : sp < s - 1 := by omega
      have h := dot_pos_of_cross_between_left
        (u := P (cyclicAdvance base v) - P (cyclicAdvance base s))
        (w := P (cyclicAdvance base sp) - P (cyclicAdvance base s))
        (v := P (cyclicAdvance base (s - 1)) - P (cyclicAdvance base s))
        (by
          have ht := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := s) (b := v + n) (c := sp + n) (by omega) (by omega) (by omega)
          rw [hperiodV, hperiodSp] at ht
          simpa [turn, cross] using ht)
        (by
          have ht := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := s) (b := sp + n) (c := s - 1 + n) (by omega) (by omega) (by omega)
          rw [hperiodSp, cyclicAdvance_period base (s - 1)] at ht
          simpa [turn, cross] using ht)
        (by
          have ht := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := s) (b := v + n) (c := s - 1 + n) (by omega) (by omega) (by omega)
          rw [hperiodV, cyclicAdvance_period base (s - 1)] at ht
          simpa [turn, cross] using ht)
        hFirstLeft
      rw [dot_comm]
      exact h
  have hd : 0 < dot
      (P (cyclicAdvance base s) - P (cyclicAdvance base v))
      (P (cyclicAdvance base vp) - P (cyclicAdvance base v)) := by
    by_cases hadj : vp = v + 1
    · simpa [hadj] using hFirstRight
    · have hnextlt : v + 1 < vp := by omega
      apply dot_pos_of_cross_between_right
        (u := P (cyclicAdvance base (v + 1)) - P (cyclicAdvance base v))
        (w := P (cyclicAdvance base vp) - P (cyclicAdvance base v))
        (v := P (cyclicAdvance base s) - P (cyclicAdvance base v))
      · have h := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := v) (b := v + 1) (c := vp) (by omega) hnextlt (by omega)
        simpa [turn, cross] using h
      · have h := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := v) (b := vp) (c := s) hvv (by omega) (by omega)
        simpa [turn, cross] using h
      · have h := cyclic_strict_convex_turn_unwrapped hConvex base
            (a := v) (b := v + 1) (c := s) (by omega) (by omega) (by omega)
        simpa [turn, cross] using h
      · rw [dot_comm]
        exact hFirstRight
  exact strict_convex_quad_not_all_acute hquad ha hb hc hd

/-- The ErLV arc-nesting conclusion once the paper's undisplayed inner-end
separation `v < v'` is made explicit.  All remaining order facts, including
`u < s`, follow from maximality and the degree-seven gap budget. -/
theorem erlv_majorant_arc_nesting_of_inner_separation
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (hConvex : CyclicStrictConvex P)
    (hHigh : ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v)
    (x : Fin n)
    (hMax : ∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤
      firstNeighborGap P d₁ d₂ d₃ x)
    (first : K3MajorantWitness P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ x) x)
    (second : K3MajorantWitness P d₁ d₂ d₃
      (cyclicAdvance x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3)))
    (hInner : first.rightMoves + second.leftMoves < 3) :
    ∃ M : ℕ, M ≤ second.rightMoves ∧
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ x) first.leftMoves =
        cyclicAdvance
          (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3)) M := by
  let gx := firstNeighborGap P d₁ d₂ d₃ x
  let hx := (firstClockwiseNeighborOffset P d₁ d₂ d₃ x).val
  let t := cyclicAdvance x 3
  let gt := firstNeighborGap P d₁ d₂ d₃ t
  let ht := (firstClockwiseNeighborOffset P d₁ d₂ d₃ t).val
  let a := first.rightMoves
  let b := first.leftMoves
  let alpha := second.leftMoves
  let beta := second.rightMoves
  let vp := 3 - alpha
  let uoff := 3 + gt
  let spoff := uoff + beta
  let soff := n - hx - b
  have hn8 : 8 ≤ n := eight_le_card_of_degree_seven (hHigh x)
  have hxHigh := hHigh x
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ x := by omega
  have htdeg : 0 < vertexDegree P d₁ d₂ d₃ t := by
    have := hHigh t
    omega
  have hgxpos : 0 < gx := firstNeighborGap_pos_of_degree_pos hxdeg
  have hgtpos : 0 < gt := firstNeighborGap_pos_of_degree_pos htdeg
  have hhxpos : 0 < hx := firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  have hhtpos : 0 < ht := firstClockwiseNeighborOffset_pos_of_degree_pos htdeg
  have hxbudget := first_neighbor_gap_cw_budget (v := x) (hHigh x)
  have htbudget := first_neighbor_gap_cw_budget (v := t) (hHigh t)
  have hgtgx : gt ≤ gx := hMax t
  have hab : a + b ≤ 2 := by
    dsimp [a, b]
    simpa [Nat.add_comm] using first.coverBudget
  have halphabeta : alpha + beta ≤ 2 := by
    exact second.coverBudget
  have hah : a < vp := by
    dsimp [a, alpha, vp] at hInner ⊢
    omega
  have hvppos : 0 < vp := by omega
  have hvpu : vp < spoff := by
    dsimp [vp, uoff, spoff]
    omega
  have hus : uoff < soff := by
    dsimp [gx, hx, gt, a, b, uoff, soff] at hxbudget hgtgx hab ⊢
    omega
  have hspn : spoff < n := by
    dsimp [gt, ht, alpha, beta, uoff, spoff] at htbudget halphabeta ⊢
    omega
  have hsoffn : soff < n := by
    dsimp [soff]
    omega
  have hhxbn : hx + b < n := by
    dsimp [gx, hx, a, b] at hxbudget hab ⊢
    omega
  have hzIndex :
      firstClockwiseNeighbor P d₁ d₂ d₃ x = cyclicRetreat x hx := by
    rfl
  have hsIndex :
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ x) b =
        cyclicAdvance x soff := by
    rw [hzIndex, cyclicRetreat_add,
      cyclicRetreat_eq_advance_complement x (by omega : 0 < hx + b) hhxbn]
    have hoff : n - (hx + b) = soff := by
      dsimp [soff]
      omega
    rw [hoff]
  have hvpIndex : cyclicRetreat t alpha = cyclicAdvance x vp := by
    have halpha : alpha ≤ 3 := by omega
    have h := cyclicRetreat_advance x (k := 3) (m := alpha) halpha (by omega)
    dsimp [t, vp]
    exact h
  have huIndex :
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ t = cyclicAdvance x uoff := by
    unfold firstCounterclockwiseNeighbor
    rw [cyclicAdvance_add]
  have hspIndex :
      cyclicAdvance (firstCounterclockwiseNeighbor P d₁ d₂ d₃ t) beta =
        cyclicAdvance x spoff := by
    rw [huIndex, cyclicAdvance_add]
  have hFirstTerminal : IsMajorant P (cyclicAdvance x soff) (cyclicAdvance x a) := by
    have h := first.terminal
    change IsMajorant P
      (cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ x) b)
      (cyclicAdvance x a) at h
    rw [hsIndex] at h
    exact h
  have hSecondTerminal : IsMajorant P (cyclicAdvance x vp) (cyclicAdvance x spoff) := by
    have h := second.terminal
    change IsMajorant P (cyclicRetreat t alpha)
      (cyclicAdvance (firstCounterclockwiseNeighbor P d₁ d₂ d₃ t) beta) at h
    rw [hvpIndex, hspIndex] at h
    exact h
  by_cases hle : soff ≤ spoff
  · refine ⟨soff - uoff, ?_, ?_⟩
    · dsimp [spoff] at hle
      omega
    · rw [hsIndex, huIndex, cyclicAdvance_add]
      congr 2
      omega
  · have hsps : spoff < soff := by omega
    exact (erlv_terminal_majorants_not_avoiding_of_offsets hConvex x
      hah hvpu hsps hsoffn hFirstTerminal hSecondTerminal).elim

/-- The two independent `k = 3` cover budgets leave exactly three cases in
which the inner endpoints are not strictly ordered as in ErLV Figure 4.
This is an arithmetic partition only: it does not assert that any exceptional
case is geometrically realizable. -/
theorem k3_inner_endpoint_budget_partition
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {i j k ell : Fin n}
    (first : K3MajorantWitness P d₁ d₂ d₃ i j)
    (second : K3MajorantWitness P d₁ d₂ d₃ k ell) :
    first.rightMoves + second.leftMoves < 3 ∨
      (first.rightMoves = 1 ∧ second.leftMoves = 2) ∨
      (first.rightMoves = 2 ∧ second.leftMoves = 1) ∨
      (first.rightMoves = 2 ∧ second.leftMoves = 2) := by
  have hFirst := first.coverBudget
  have hSecond := second.coverBudget
  omega

/-- Exact extra statement needed to justify ErLV's printed sentence
"Obviously, `v'` lies on the arc `vt`" under the draft's side-count
convention.  It asks for a jointly minimal pair of actual cover paths whose
facing endpoints consume strictly fewer than the three sides between `x`
and `t`. -/
def ErLVInnerEndpointSeparationComplete : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    CyclicStrictConvex P → HasTopThreeDistanceClasses P d₁ d₂ d₃ →
    (∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v) →
    ∀ x : Fin n,
      (∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤
        firstNeighborGap P d₁ d₂ d₃ x) →
      let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
      let t := cyclicAdvance x 3
      let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ t
      ∃ pair : CoordinatedK3MajorantPair P d₁ d₂ d₃ z x t u,
        pair.first.rightMoves + pair.second.leftMoves < 3

/-- All of ErLV Proposition 2.6's geometry now closes the requested nesting
headline once the source's undisplayed strict order of the inner endpoints is
supplied. -/
theorem erlv_majorant_arc_nesting_complete_of_inner_endpoint_separation
    (hInner : ErLVInnerEndpointSeparationComplete) :
    ErLVMajorantArcNestingComplete := by
  intro n _ P d₁ d₂ d₃ hConvex hClasses hHigh x hMax
  dsimp only
  obtain ⟨pair, hSeparation⟩ :=
    hInner P d₁ d₂ d₃ hConvex hClasses hHigh x hMax
  refine ⟨pair, ?_⟩
  exact erlv_majorant_arc_nesting_of_inner_separation P d₁ d₂ d₃
    hConvex hHigh x hMax pair.first pair.second hSeparation

/-- The exact geometric core of ErLV Proposition 2.6: two terminal edges
cannot be avoiding.  The four `h*Cone` hypotheses spell out the cyclic ray
order between each majorant endpoint and the adjacent boundary vertex on
the exterior side. -/
theorem erlv_terminal_majorants_not_avoiding
    {a b c d pa nb pc nd : Point ℝ}
    (hquad : StrictConvexQuad a b c d)
    (haCone : 0 < turn a b d ∧ 0 < turn a d pa ∧ 0 < turn a b pa)
    (hbCone : 0 < turn b nb c ∧ 0 < turn b c a ∧ 0 < turn b nb a)
    (hcCone : 0 < turn c d b ∧ 0 < turn c b pc ∧ 0 < turn c d pc)
    (hdCone : 0 < turn d nd a ∧ 0 < turn d a c ∧ 0 < turn d nd c)
    (haLocal : 0 < dot (b - a) (pa - a))
    (hbLocal : 0 < dot (a - b) (nb - b))
    (hcLocal : 0 < dot (d - c) (pc - c))
    (hdLocal : 0 < dot (c - d) (nd - d)) : False := by
  have ha : 0 < dot (b - a) (d - a) :=
    dot_pos_of_cross_between_left (u := b - a) (w := d - a) (v := pa - a)
      (by simpa [turn, cross] using haCone.1)
      (by simpa [turn, cross] using haCone.2.1)
      (by simpa [turn, cross] using haCone.2.2) haLocal
  have hb : 0 < dot (a - b) (c - b) :=
    dot_pos_of_cross_between_right (u := nb - b) (w := c - b) (v := a - b)
      (by simpa [turn, cross] using hbCone.1)
      (by simpa [turn, cross] using hbCone.2.1)
      (by simpa [turn, cross] using hbCone.2.2)
      (by rw [dot_comm]; exact hbLocal)
  have hc : 0 < dot (b - c) (d - c) := by
    have h := dot_pos_of_cross_between_left
      (u := d - c) (w := b - c) (v := pc - c)
      (by simpa [turn, cross] using hcCone.1)
      (by simpa [turn, cross] using hcCone.2.1)
      (by simpa [turn, cross] using hcCone.2.2) hcLocal
    rw [dot_comm]
    exact h
  have hd : 0 < dot (c - d) (a - d) :=
    dot_pos_of_cross_between_right (u := nd - d) (w := a - d) (v := c - d)
      (by simpa [turn, cross] using hdCone.1)
      (by simpa [turn, cross] using hdCone.2.1)
      (by simpa [turn, cross] using hdCone.2.2)
      (by rw [dot_comm]; exact hdLocal)
  exact strict_convex_quad_not_all_acute hquad ha hb hc hd

end LeanPool.Erdos132ConvexK3
