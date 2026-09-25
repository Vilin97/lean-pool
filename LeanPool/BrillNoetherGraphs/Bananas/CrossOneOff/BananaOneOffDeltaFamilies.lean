/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.OneOffPositiveRows

/-!
# The three endpoint/penultimate Delta families

This completes part (2) of paper Corollary 2.25 for the marking consisting of
the common left endpoint and the penultimate point of one strand.
-/

namespace Bananas

open Utilities

/-- Corollary 2.25(2), first family: a positive right-endpoint multiple up to
the genus has marked second difference one. -/
theorem rankDelta_oneOff_rightEndpoint_family
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (a : ℕ) (ha : 0 < a) (hag : a ≤ g)
    (hLength : 1 < B.length alpha) :
    rankDelta
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (a • oneChip (rightEndpoint B)) = 1 :=
  rankDelta_oneOff_rightEndpoint_nsmul_eq_one
    B alpha a ha hag hLength

/-- The coefficient-zero case of the second family.  This small lemma is
needed only in genus one; for positive coefficients the general one-off
normal-form theorem applies directly. -/
private theorem rankDelta_oneOff_interior_chip_eq_one
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (r : ℕ) (hg : 0 < g) (hLength : 1 < B.length alpha)
    (hrLo : 1 ≤ r) (hrHi : r + 1 < B.length alpha) :
    rankDelta
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (oneChip (strandVertex B alpha ⟨r, by omega⟩)) = 1 := by
  let p : B.PathPosition alpha := ⟨r, by omega⟩
  let v : B.PathPosition alpha := ⟨B.length alpha - 1, by omega⟩
  let E : CFDiv B.graph := oneChip (strandVertex B alpha p)
  have hp : B.IsInteriorPosition alpha p := by
    change 0 < r ∧ r < B.length alpha
    omega
  have hv : B.IsInteriorPosition alpha v := by
    change 0 < B.length alpha - 1 ∧ B.length alpha - 1 < B.length alpha
    omega
  have hE : IsSemibreak B E :=
    isSemibreak_one_strand_chip B alpha p hp
  have hdegE : deg E = 1 := by simp [E, deg_one_chip]
  have hRankE : rank B.graph E = 0 :=
    rank_semibreak_eq_zero B E hE (by rw [hdegE]; omega)
  have hpLeft : strandVertex B alpha p ≠ leftEndpoint B :=
    strandVertex_ne_leftEndpoint B alpha p hp.1
  have hpV : strandVertex B alpha p ≠ strandVertex B alpha v := by
    intro h
    have hpv := congrArg Fin.val (strandVertex_injective B alpha h)
    dsimp [p, v] at hpv
    omega
  have hSupportLeft : E (leftEndpoint B) = 0 := by
    simp [E, hpLeft]
  have hSupportV : E (strandVertex B alpha v) = 0 := by
    simp [E, hpV]
  have hRankLeft := rank_semibreak_sub_vertex_eq_neg_one B E hE
    (by rw [hdegE]; omega) (leftEndpoint B) hSupportLeft
  have hRankV := rank_semibreak_sub_vertex_eq_neg_one B E hE
    (by rw [hdegE]; omega) (strandVertex B alpha v) hSupportV
  have hBothDeg : deg
      (E - oneChip (leftEndpoint B) -
        oneChip (strandVertex B alpha v)) < 0 := by
    rw [deg.map_sub, deg.map_sub, hdegE, deg_one_chip, deg_one_chip]
    norm_num
  have hRankBoth := rank_neg_one_of_deg_neg B.graph _ hBothDeg
  unfold rankDelta mark
  change rank B.graph E -
      rank B.graph (E - oneChip (leftEndpoint B)) -
      rank B.graph (E - oneChip (strandVertex B alpha v)) +
      rank B.graph (E - oneChip (leftEndpoint B) -
        oneChip (strandVertex B alpha v)) = 1
  rw [hRankE, hRankLeft, hRankV, hRankBoth]
  norm_num

/-- Corollary 2.25(2), second family. -/
theorem rankDelta_oneOff_balanced_interior_family
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (b r : ℕ) (hg : 0 < g) (hb : b ≤ g - 1)
    (hLength : 1 < B.length alpha)
    (hrLo : 1 ≤ r) (hrHi : r + 1 < B.length alpha) :
    rankDelta
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      ((b : ℤ) • oneChip (leftEndpoint B) +
        (b : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B alpha ⟨r, by omega⟩)) = 1 := by
  by_cases hbZero : b = 0
  · subst b
    simp only [Nat.cast_zero, zero_smul, zero_add]
    exact rankDelta_oneOff_interior_chip_eq_one
      B alpha r hg hLength hrLo hrHi
  · have hgTwo : 2 ≤ g := by omega
    exact rankDelta_oneOff_positive_normalForm_eq_one
      B alpha b r hgTwo hb hLength hrLo hrHi

/-- Corollary 2.25(2), third family.  A terminal chip contributes the extra
corner exactly at the boundary `a = g`. -/
theorem rankDelta_oneOff_terminal_family
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (a b : ℕ) (hba : b < a) (hag : a ≤ g)
    (hLength : 1 < B.length alpha) :
    rankDelta
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      ((a : ℤ) • oneChip (leftEndpoint B) +
        (b : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B alpha
          ⟨B.length alpha - 1, by omega⟩)) =
      if a = g then 1 else 0 := by
  let v : B.PathPosition alpha := ⟨B.length alpha - 1, by omega⟩
  let E : CFDiv B.graph := oneChip (strandVertex B alpha v)
  have hv : B.IsInteriorPosition alpha v := by
    change 0 < B.length alpha - 1 ∧ B.length alpha - 1 < B.length alpha
    omega
  have hE : IsSemibreak B E :=
    isSemibreak_one_strand_chip B alpha v hv
  have hZero : IsSemibreak B (0 : CFDiv B.graph) := isSemibreak_zero B
  have hdegE : deg E = 1 := by simp [E, deg_one_chip]
  have hRangeE : (b : ℤ) + deg E ≤ (g : ℤ) := by
    rw [hdegE]
    exact_mod_cast (show b + 1 ≤ g by omega)
  have hRangeZero : (b : ℤ) + deg (0 : CFDiv B.graph) ≤ (g : ℤ) := by
    simp
    exact_mod_cast hba.le.trans hag
  have hRankD := rank_bananaNormalForm B (a : ℤ) (b : ℤ) E hE
    (by omega) (by omega) hRangeE
  have hRankDU := rank_bananaNormalForm B ((a : ℤ) - 1) (b : ℤ) E hE
    (by omega) (by omega) hRangeE
  have hRankDV := rank_bananaNormalForm B (a : ℤ) (b : ℤ) 0 hZero
    (by omega) (by omega) hRangeZero
  have hRankBoth := rank_bananaNormalForm B ((a : ℤ) - 1) (b : ℤ) 0 hZero
    (by omega) (by omega) hRangeZero
  have hD : (a : ℤ) • oneChip (leftEndpoint B) +
      (b : ℤ) • oneChip (rightEndpoint B) + E =
      bananaNormalForm B a b E := rfl
  have hDU : (a : ℤ) • oneChip (leftEndpoint B) +
      (b : ℤ) • oneChip (rightEndpoint B) + E -
      oneChip (leftEndpoint B) =
      bananaNormalForm B ((a : ℤ) - 1) b E := by
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hDV : (a : ℤ) • oneChip (leftEndpoint B) +
      (b : ℤ) • oneChip (rightEndpoint B) + E -
      oneChip (strandVertex B alpha v) =
      bananaNormalForm B a b 0 := by
    dsimp [E]
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul]
    ring
  have hBoth : (a : ℤ) • oneChip (leftEndpoint B) +
      (b : ℤ) • oneChip (rightEndpoint B) + E -
      oneChip (leftEndpoint B) - oneChip (strandVertex B alpha v) =
      bananaNormalForm B ((a : ℤ) - 1) b 0 := by
    dsimp [E]
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul]
    ring
  have hRankD' : rank B.graph
      ((a : ℤ) • oneChip (leftEndpoint B) +
        (b : ℤ) • oneChip (rightEndpoint B) + E) =
      max (min (a : ℤ) b) ((a : ℤ) + b + deg E - g) := by
    rw [hD, hRankD]
  have hRankDU' : rank B.graph
      ((a : ℤ) • oneChip (leftEndpoint B) +
        (b : ℤ) • oneChip (rightEndpoint B) + E -
        oneChip (leftEndpoint B)) =
      max (min ((a : ℤ) - 1) b)
        ((a : ℤ) - 1 + b + deg E - g) := by
    rw [hDU, hRankDU]
  have hRankDV' : rank B.graph
      ((a : ℤ) • oneChip (leftEndpoint B) +
        (b : ℤ) • oneChip (rightEndpoint B) + E -
        oneChip (strandVertex B alpha v)) =
      max (min (a : ℤ) b) ((a : ℤ) + b + deg (0 : CFDiv B.graph) - g) := by
    rw [hDV, hRankDV]
  have hRankBoth' : rank B.graph
      ((a : ℤ) • oneChip (leftEndpoint B) +
        (b : ℤ) • oneChip (rightEndpoint B) + E -
        oneChip (leftEndpoint B) - oneChip (strandVertex B alpha v)) =
      max (min ((a : ℤ) - 1) b)
        ((a : ℤ) - 1 + b + deg (0 : CFDiv B.graph) - g) := by
    rw [hBoth, hRankBoth]
  have hMinA : min (a : ℤ) (b : ℤ) = b :=
    min_eq_right (by exact_mod_cast hba.le)
  have hMinPred : min ((a : ℤ) - 1) (b : ℤ) = b := by
    apply min_eq_right
    omega
  have hMaxD : max (b : ℤ) ((a : ℤ) + b + 1 - g) =
      (b : ℤ) + if a = g then 1 else 0 := by
    by_cases hagEq : a = g
    · subst g
      have hle : (b : ℤ) ≤ (a : ℤ) + b + 1 - a := by
        ring_nf
        omega
      rw [if_pos rfl, max_eq_right hle]
      ring
    · have hagLt : a < g := lt_of_le_of_ne hag hagEq
      have hagLtInt : (a : ℤ) + 1 ≤ (g : ℤ) := by
        exact_mod_cast hagLt
      have hle : (a : ℤ) + b + 1 - g ≤ b := by omega
      rw [if_neg hagEq, max_eq_left hle]
      ring
  have hMaxDU : max (b : ℤ) ((a : ℤ) - 1 + b + 1 - g) = b := by
    rw [max_eq_left]
    omega
  have hMaxDV : max (b : ℤ) ((a : ℤ) + b - g) = b := by
    rw [max_eq_left]
    omega
  have hMaxBoth : max (b : ℤ) ((a : ℤ) - 1 + b - g) = b := by
    rw [max_eq_left]
    omega
  unfold rankDelta mark
  change rank B.graph ((a : ℤ) • oneChip (leftEndpoint B) +
      (b : ℤ) • oneChip (rightEndpoint B) + E) -
    rank B.graph ((a : ℤ) • oneChip (leftEndpoint B) +
      (b : ℤ) • oneChip (rightEndpoint B) + E -
      oneChip (leftEndpoint B)) -
    rank B.graph ((a : ℤ) • oneChip (leftEndpoint B) +
      (b : ℤ) • oneChip (rightEndpoint B) + E -
      oneChip (strandVertex B alpha v)) +
    rank B.graph ((a : ℤ) • oneChip (leftEndpoint B) +
      (b : ℤ) • oneChip (rightEndpoint B) + E -
      oneChip (leftEndpoint B) - oneChip (strandVertex B alpha v)) = _
  rw [hRankD', hRankDU', hRankDV', hRankBoth', hdegE]
  simp only [map_zero, add_zero]
  rw [hMinA, hMinPred, hMaxD, hMaxDU, hMaxDV, hMaxBoth]
  by_cases hagEq : a = g
  · rw [if_pos hagEq]
    omega
  · rw [if_neg hagEq]
    omega

/-- Corollary 2.25(2), packaged with the paper's common hypotheses
`0 ≤ b < a ≤ g` and `0 < r < n_alpha - 1`. -/
theorem rankDelta_oneOff_three_families
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (a b r : ℕ) (hba : b < a) (hag : a ≤ g)
    (hLength : 1 < B.length alpha)
    (hrLo : 1 ≤ r) (hrHi : r + 1 < B.length alpha) :
    rankDelta
        (mark B.graph (leftEndpoint B)
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
        (a • oneChip (rightEndpoint B)) = 1 ∧
      rankDelta
        (mark B.graph (leftEndpoint B)
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
        ((b : ℤ) • oneChip (leftEndpoint B) +
          (b : ℤ) • oneChip (rightEndpoint B) +
          oneChip (strandVertex B alpha ⟨r, by omega⟩)) = 1 ∧
      rankDelta
        (mark B.graph (leftEndpoint B)
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
        ((a : ℤ) • oneChip (leftEndpoint B) +
          (b : ℤ) • oneChip (rightEndpoint B) +
          oneChip (strandVertex B alpha
            ⟨B.length alpha - 1, by omega⟩)) =
        if a = g then 1 else 0 := by
  have ha : 0 < a := by omega
  have hg : 0 < g := ha.trans_le hag
  have hb : b ≤ g - 1 := by omega
  exact ⟨rankDelta_oneOff_rightEndpoint_family B alpha a ha hag hLength,
    rankDelta_oneOff_balanced_interior_family B alpha b r hg hb hLength
      hrLo hrHi,
    rankDelta_oneOff_terminal_family B alpha a b hba hag hLength⟩

end Bananas
