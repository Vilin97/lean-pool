/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffResidueDelta

/-!
# Remaining cross-one-off Delta families

This completes the rank-difference assertions in part (3) of paper
Corollary 2.25.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Corollary 2.25(3): a right-endpoint coefficient and one sufficiently
interior chip on the first marked strand have second difference one. -/
theorem rankDelta_crossOneOff_right_interior_family
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (p : B.PathPosition alpha) (b : ℕ)
    (hg : 2 ≤ g) (hab : alpha ≠ beta)
    (hpLo : 2 ≤ p.val) (hpHi : p.val < B.length alpha)
    (hBeta : 2 ≤ B.length beta) (hb : b < g) :
    rankDelta
      (mark B.graph
        (strandVertex B alpha ⟨1, by have := B.length_pos alpha; omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      ((b : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B alpha p)) = 1 := by
  exact rankDelta_crossOneOff_multiple_normalForm_eq_one
    B alpha beta p b hg hab hpLo hpHi hBeta (by omega)

/-- The two-interior family at its top coefficient.  Here the first three
divisors are nonspecial, while the twice-subtracted divisor remains in the
banana normal-form range, and the second difference is zero. -/
theorem rankDelta_crossOneOff_two_interior_boundary_eq_zero
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (p : B.PathPosition alpha) (q : B.PathPosition beta)
    (hg : 2 ≤ g) (hab : alpha ≠ beta)
    (hpLo : 2 ≤ p.val) (hpHi : p.val < B.length alpha)
    (hqLo : 1 ≤ q.val) (hqHi : q.val + 1 < B.length beta) :
    rankDelta
      (mark B.graph
        (strandVertex B alpha ⟨1, by have := B.length_pos alpha; omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (((g : ℤ) - 1) •
          (oneChip (leftEndpoint B) + oneChip (rightEndpoint B)) +
        oneChip (strandVertex B alpha p) +
        oneChip (strandVertex B beta q)) = 0 := by
  let pPrev : B.PathPosition alpha := ⟨p.val - 1, by omega⟩
  let qNext : B.PathPosition beta := ⟨q.val + 1, by omega⟩
  have hpPrev : B.IsInteriorPosition alpha pPrev := by
    change 0 < p.val - 1 ∧ p.val - 1 < B.length alpha
    omega
  have hqNext : B.IsInteriorPosition beta qNext := by
    change 0 < q.val + 1 ∧ q.val + 1 < B.length beta
    omega
  let E : CFDiv B.graph :=
    oneChip (strandVertex B alpha p) + oneChip (strandVertex B beta q)
  let EUV : CFDiv B.graph :=
    oneChip (strandVertex B alpha pPrev) +
      oneChip (strandVertex B beta qNext)
  have hEUV : IsSemibreak B EUV := by
    dsimp [EUV]
    exact isSemibreak_two_distinct_strand_chips B alpha beta pPrev qNext
      hpPrev hqNext hab
  have hdegE : deg E = 2 := by simp [E, deg.map_add, deg_one_chip]
  have hdegEUV : deg EUV = 2 := by simp [EUV, deg.map_add, deg_one_chip]
  let D : CFDiv B.graph :=
    bananaNormalForm B ((g : ℤ) - 1) ((g : ℤ) - 1) E
  have hDDef : D =
      ((g : ℤ) - 1) •
          (oneChip (leftEndpoint B) + oneChip (rightEndpoint B)) +
        oneChip (strandVertex B alpha p) +
        oneChip (strandVertex B beta q) := by
    dsimp [D, E]
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.smul_apply]
    ring
  have hShiftU := crossOneOff_sub_first_mark_shift B alpha p.val
    (by omega) (by omega)
  have hShiftV := crossOneOff_sub_second_mark_shift B beta q.val (by omega)
  have hDUV : linearEquiv B.graph
      (D - oneChip
          (strandVertex B alpha
            ⟨1, by have := B.length_pos alpha; omega⟩) -
        oneChip
          (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (bananaNormalForm B ((g : ℤ) - 2) ((g : ℤ) - 2) EUV) := by
    unfold linearEquiv at hShiftU hShiftV ⊢
    have hPair := (principalDivisors B.graph).add_mem hShiftU hShiftV
    have hCommon := (principalDivisors B.graph).add_mem
      ((principalDivisors B.graph).zero_mem) hPair
    convert hCommon using 1
    all_goals
      (dsimp [D, E, EUV, pPrev, qNext]
       unfold bananaNormalForm
       ext z
       simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
         smul_eq_mul]
       ring)
  have hDegreeD : deg D = 2 * (g : ℤ) := by
    rw [degree_bananaNormalForm, hdegE]
    ring
  have hDegreeDU : deg
      (D - oneChip
        (strandVertex B alpha
          ⟨1, by have := B.length_pos alpha; omega⟩)) =
      2 * (g : ℤ) - 1 := by
    rw [deg.map_sub, hDegreeD, deg_one_chip]
  have hDegreeDV : deg
      (D - oneChip
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) =
      2 * (g : ℤ) - 1 := by
    rw [deg.map_sub, hDegreeD, deg_one_chip]
  have hRankD : rank B.graph D = (g : ℤ) := by
    have h := (rank_nonspecial_range (banana_graph_connected B) D).2.2 (by
      rw [hDegreeD, banana_genus]
      omega)
    rw [hDegreeD, banana_genus] at h
    omega
  have hRankDU : rank B.graph
      (D - oneChip
        (strandVertex B alpha
          ⟨1, by have := B.length_pos alpha; omega⟩)) =
      (g : ℤ) - 1 := by
    have h := (rank_nonspecial_range (banana_graph_connected B)
      (D - oneChip
        (strandVertex B alpha
          ⟨1, by have := B.length_pos alpha; omega⟩))).2.2 (by
            rw [hDegreeDU, banana_genus]
            omega)
    rw [hDegreeDU, banana_genus] at h
    omega
  have hRankDV : rank B.graph
      (D - oneChip
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) =
      (g : ℤ) - 1 := by
    have h := (rank_nonspecial_range (banana_graph_connected B)
      (D - oneChip
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))).2.2 (by
            rw [hDegreeDV, banana_genus]
            omega)
    rw [hDegreeDV, banana_genus] at h
    omega
  have hRankDUV : rank B.graph
      (D - oneChip
          (strandVertex B alpha
            ⟨1, by have := B.length_pos alpha; omega⟩) -
        oneChip
          (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) =
      (g : ℤ) - 2 := by
    rw [rank_eq_of_linear_equiv B.graph hDUV,
      rank_bananaNormalForm B ((g : ℤ) - 2) ((g : ℤ) - 2) EUV hEUV
        (by omega) (by omega)]
    · rw [hdegEUV]
      simp only [min_self]
      rw [max_eq_left]
      omega
    · rw [hdegEUV]
      omega
  rw [← hDDef]
  unfold rankDelta mark
  rw [hRankD, hRankDU, hRankDV, hRankDUV]
  ring

/-- Corollary 2.25(3), the terminal-chip delta family. -/
theorem rankDelta_crossOneOff_terminal_delta_family
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (p : B.PathPosition alpha) (b : ℕ)
    (hg : 2 ≤ g) (hab : alpha ≠ beta)
    (hpLo : 2 ≤ p.val) (hpHi : p.val < B.length alpha)
    (hBeta : 2 ≤ B.length beta) (hb : b ≤ g - 1) :
    rankDelta
      (mark B.graph
        (strandVertex B alpha ⟨1, by have := B.length_pos alpha; omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (((g : ℤ) - 1) • oneChip (leftEndpoint B) +
        (b : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B alpha p) +
        oneChip
          (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) =
      if b < g - 1 then 1 else 0 := by
  by_cases hbLt : b < g - 1
  · rw [if_pos hbLt]
    exact rankDelta_crossOneOff_complement_normalForm_eq_one
      B alpha beta p b hg hab hpLo hpHi hBeta hbLt
  · have hbEq : b = g - 1 := by omega
    subst b
    rw [if_neg (by omega : ¬ g - 1 < g - 1)]
    simpa [Nat.cast_sub (by omega : 1 ≤ g)] using
      rankDelta_crossOneOff_complement_boundary_eq_zero
        B alpha beta p hg hpLo hpHi hBeta

/-- Corollary 2.25(3), the balanced two-interior delta family. -/
theorem rankDelta_crossOneOff_balanced_delta_family
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (p : B.PathPosition alpha) (q : B.PathPosition beta) (b : ℕ)
    (hg : 2 ≤ g) (hab : alpha ≠ beta)
    (hpLo : 2 ≤ p.val) (hpHi : p.val < B.length alpha)
    (hqLo : 1 ≤ q.val) (hqHi : q.val + 1 < B.length beta)
    (hb : b ≤ g - 1) :
    rankDelta
      (mark B.graph
        (strandVertex B alpha ⟨1, by have := B.length_pos alpha; omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      ((b : ℤ) •
          (oneChip (leftEndpoint B) + oneChip (rightEndpoint B)) +
        oneChip (strandVertex B alpha p) +
        oneChip (strandVertex B beta q)) =
      if b < g - 1 then 1 else 0 := by
  by_cases hbLt : b < g - 1
  · rw [if_pos hbLt]
    exact rankDelta_crossOneOff_two_interior_eq_one
      B alpha beta p q b hg hab hpLo hpHi hqLo hqHi (by omega)
  · have hbEq : b = g - 1 := by omega
    subst b
    rw [if_neg (by omega : ¬ g - 1 < g - 1)]
    simpa [Nat.cast_sub (by omega : 1 ≤ g)] using
      rankDelta_crossOneOff_two_interior_boundary_eq_zero
        B alpha beta p q hg hab hpLo hpHi hqLo hqHi

end Bananas
