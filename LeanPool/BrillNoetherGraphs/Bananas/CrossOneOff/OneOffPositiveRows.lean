/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.OneOffMultipleRows
public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.NSMCrossWitness

/-!
# Positive interior-residue rows for the same-strand one-off marking

This completes the three residue classes of Lemma 4.23.  Write
`b = m n + r` with `1 ≤ r` and `r+1 < n`, and put `c = g+m-b`.  The
correct firing target is

`c·L + c·R + v_(alpha,r)`.

The paper's final displayed divisor repeats `v_(0,0)` twice; the second copy
must be the right endpoint.  With that correction the divisor has the right
degree and its marked second difference is one.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Corrected positive-residue firing identity for Lemma 4.23. -/
theorem oneOff_firing_positive_residue
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (b m r c : ℕ) (hLength : 1 < B.length alpha)
    (hb : b = m * B.length alpha + r)
    (_hrLo : 1 ≤ r) (hrHi : r + 1 < B.length alpha)
    (hbm : b ≤ g + m) (hc : c = g + m - b) :
    linearEquiv B.graph
      (g • oneChip (rightEndpoint B) +
        ((g + 2 * m + 1 - b : ℕ) : ℤ) • oneChip (leftEndpoint B) -
        (b : ℤ) • oneChip
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      ((c : ℤ) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B alpha ⟨r, by omega⟩)) := by
  have hMark := crossOneOff_second_mark_multiple B alpha b m r hb (by omega)
  unfold linearEquiv at hMark ⊢
  have hNeg := (principalDivisors B.graph).neg_mem hMark
  convert hNeg using 1
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul]
  rw [nsmul_eq_mul]
  have hcInt : (c : ℤ) = (g : ℤ) + m - b := by
    have hcAdd : c + b = g + m := by omega
    have hcAddInt : (c : ℤ) + b = (g : ℤ) + m := by
      exact_mod_cast hcAdd
    omega
  have haInt : ((g + 2 * m + 1 - b : ℕ) : ℤ) =
      (g : ℤ) + 2 * m + 1 - b := by
    have : b ≤ g + 2 * m + 1 := by omega
    omega
  rw [hcInt, haInt]
  ring

private theorem oneOff_positive_sub_mark_linearEquiv
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (c r : ℕ) (hLength : 1 < B.length alpha)
    (_hrLo : 1 ≤ r) (hrHi : r + 1 < B.length alpha) :
    linearEquiv B.graph
      ((c : ℤ) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B alpha ⟨r, by omega⟩) -
        oneChip
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (bananaNormalForm B (c : ℤ) ((c : ℤ) - 1)
        (oneChip (strandVertex B alpha ⟨r + 1, by omega⟩))) := by
  have hPenultimate := oneOff_sub_penultimate_linearEquiv_normalForm
    B alpha c hLength
  have hSlide := strand_one_add_position_linearEquiv_left_succ B alpha
    (⟨r, by omega⟩ : B.PathPosition alpha) (by
      change r + 1 ≤ B.length alpha
      omega)
  unfold linearEquiv at hPenultimate hSlide ⊢
  have hSum := (principalDivisors B.graph).add_mem hPenultimate hSlide
  convert hSum using 1
  ext z
  simp only [bananaNormalForm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

private theorem oneOff_positive_sub_both_linearEquiv
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (c r : ℕ) (hLength : 1 < B.length alpha)
    (_hrLo : 1 ≤ r) (hrHi : r + 1 < B.length alpha) :
    linearEquiv B.graph
      ((c : ℤ) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B alpha ⟨r, by omega⟩) -
        oneChip (leftEndpoint B) -
        oneChip
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (bananaNormalForm B ((c : ℤ) - 1) ((c : ℤ) - 1)
        (oneChip (strandVertex B alpha ⟨r + 1, by omega⟩))) := by
  have hPenultimate := oneOff_sub_penultimate_linearEquiv_normalForm
    B alpha c hLength
  have hSlide := strand_one_add_position_linearEquiv_left_succ B alpha
    (⟨r, by omega⟩ : B.PathPosition alpha) (by
      change r + 1 ≤ B.length alpha
      omega)
  unfold linearEquiv at hPenultimate hSlide ⊢
  have hSum := (principalDivisors B.graph).add_mem hPenultimate hSlide
  convert hSum using 1
  ext z
  simp only [bananaNormalForm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The corrected positive-residue normal form has marked second difference
one throughout its numerical range. -/
theorem rankDelta_oneOff_positive_normalForm_eq_one
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (c r : ℕ) (hg : 2 ≤ g) (hc : c ≤ g - 1)
    (hLength : 1 < B.length alpha)
    (hrLo : 1 ≤ r) (hrHi : r + 1 < B.length alpha) :
    rankDelta
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      ((c : ℤ) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B alpha ⟨r, by omega⟩)) = 1 := by
  let p : B.PathPosition alpha := ⟨r, by omega⟩
  let pNext : B.PathPosition alpha := ⟨r + 1, by omega⟩
  let v : B.PathPosition alpha := ⟨B.length alpha - 1, by omega⟩
  let E : CFDiv B.graph := oneChip (strandVertex B alpha p)
  let ENext : CFDiv B.graph := oneChip (strandVertex B alpha pNext)
  have hp : B.IsInteriorPosition alpha p := by
    change 0 < r ∧ r < B.length alpha
    omega
  have hpNext : B.IsInteriorPosition alpha pNext := by
    change 0 < r + 1 ∧ r + 1 < B.length alpha
    omega
  have hv : B.IsInteriorPosition alpha v := by
    change 0 < B.length alpha - 1 ∧ B.length alpha - 1 < B.length alpha
    omega
  have hE : IsSemibreak B E := isSemibreak_one_strand_chip B alpha p hp
  have hENext : IsSemibreak B ENext :=
    isSemibreak_one_strand_chip B alpha pNext hpNext
  have hdegE : deg E = 1 := by simp [E, deg_one_chip]
  have hdegENext : deg ENext = 1 := by simp [ENext, deg_one_chip]
  by_cases hcZero : c = 0
  · subst c
    have hRankE : rank B.graph E = 0 :=
      rank_semibreak_eq_zero B E hE (by rw [hdegE]; omega)
    have hpLeft : strandVertex B alpha p ≠ leftEndpoint B :=
      strandVertex_ne_leftEndpoint B alpha p hp.1
    have hpV : strandVertex B alpha p ≠ strandVertex B alpha v := by
      intro h
      have hpv := congrArg Fin.val (strandVertex_injective B alpha h)
      dsimp [p, v] at hpv
      omega
    have hSupportLeft : E (leftEndpoint B) = 0 := by simp [E, hpLeft]
    have hSupportV : E (strandVertex B alpha v) = 0 := by simp [E, hpV]
    have hRankLeft := rank_semibreak_sub_vertex_eq_neg_one B E hE
      (by rw [hdegE]; omega) (leftEndpoint B) hSupportLeft
    have hRankV := rank_semibreak_sub_vertex_eq_neg_one B E hE
      (by rw [hdegE]; omega) (strandVertex B alpha v) hSupportV
    have hBothDeg : deg
        (E - oneChip (leftEndpoint B) - oneChip (strandVertex B alpha v)) < 0 := by
      rw [deg.map_sub, deg.map_sub, hdegE, deg_one_chip, deg_one_chip]
      norm_num
    have hRankBoth := rank_neg_one_of_deg_neg B.graph _ hBothDeg
    unfold rankDelta mark
    simp only [Nat.cast_zero, zero_smul, zero_add]
    change rank B.graph E -
      rank B.graph (E - oneChip (leftEndpoint B)) -
      rank B.graph (E - oneChip (strandVertex B alpha v)) +
      rank B.graph (E - oneChip (leftEndpoint B) -
        oneChip (strandVertex B alpha v)) = 1
    rw [hRankE, hRankLeft, hRankV, hRankBoth]
    norm_num
  · have hcPos : 0 < c := Nat.pos_of_ne_zero hcZero
    have hRange : (c : ℤ) + 1 ≤ (g : ℤ) := by exact_mod_cast (show c + 1 ≤ g by omega)
    have hD : (c : ℤ) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) + E =
        bananaNormalForm B c c E := by
      unfold bananaNormalForm
      rfl
    have hDU : (c : ℤ) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) + E -
        oneChip (leftEndpoint B) = bananaNormalForm B (c - 1) c E := by
      unfold bananaNormalForm
      ext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hDV := oneOff_positive_sub_mark_linearEquiv B alpha c r
      hLength hrLo hrHi
    have hBoth := oneOff_positive_sub_both_linearEquiv B alpha c r
      hLength hrLo hrHi
    have hRankD := rank_bananaNormalForm B c c E hE
      (by omega) (by omega) (by rw [hdegE]; exact hRange)
    have hRankDU := rank_bananaNormalForm B (c - 1) c E hE
      (by omega) (by omega) (by rw [hdegE]; exact hRange)
    have hRangeNext : (c : ℤ) - 1 + deg ENext ≤ (g : ℤ) := by
      rw [hdegENext]
      omega
    have hRankDV := rank_bananaNormalForm B c (c - 1) ENext hENext
      (by omega) (by omega) hRangeNext
    have hRankBoth := rank_bananaNormalForm B (c - 1) (c - 1) ENext hENext
      (by omega) (by omega) hRangeNext
    have hRankD' : rank B.graph
        ((c : ℤ) • oneChip (leftEndpoint B) +
          (c : ℤ) • oneChip (rightEndpoint B) + E) = c := by
      rw [hD, hRankD, hdegE]
      omega
    have hRankDU' : rank B.graph
        ((c : ℤ) • oneChip (leftEndpoint B) +
          (c : ℤ) • oneChip (rightEndpoint B) + E -
          oneChip (leftEndpoint B)) = (c : ℤ) - 1 := by
      rw [hDU, hRankDU, hdegE]
      omega
    have hRankDV' : rank B.graph
        ((c : ℤ) • oneChip (leftEndpoint B) +
          (c : ℤ) • oneChip (rightEndpoint B) + E -
          oneChip (strandVertex B alpha v)) = (c : ℤ) - 1 := by
      rw [rank_eq_of_linear_equiv B.graph hDV, hRankDV, hdegENext]
      omega
    have hRankBoth' : rank B.graph
        ((c : ℤ) • oneChip (leftEndpoint B) +
          (c : ℤ) • oneChip (rightEndpoint B) + E -
          oneChip (leftEndpoint B) -
          oneChip (strandVertex B alpha v)) = (c : ℤ) - 1 := by
      rw [rank_eq_of_linear_equiv B.graph hBoth, hRankBoth, hdegENext]
      omega
    unfold rankDelta mark
    change rank B.graph ((c : ℤ) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) + E) -
      rank B.graph ((c : ℤ) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) + E -
          oneChip (leftEndpoint B)) -
      rank B.graph ((c : ℤ) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) + E -
          oneChip (strandVertex B alpha v)) +
      rank B.graph ((c : ℤ) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) + E -
          oneChip (leftEndpoint B) - oneChip (strandVertex B alpha v)) = 1
    rw [hRankD', hRankDU', hRankDV', hRankBoth']
    omega

/-- Lemma 4.23, positive interior-residue case. -/
theorem transmission_oneOff_positive_residue
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (b m r : ℕ) (tau : ℤ → ℤ) (hg : 2 ≤ g)
    (hLength : 1 < B.length alpha)
    (hb : b = m * B.length alpha + r)
    (hrLo : 1 ≤ r) (hrHi : r + 1 < B.length alpha)
    (hbm : b ≤ g + m)
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    tau (b : ℤ) = (g + 2 * m + 1 - b : ℕ) := by
  let c := g + m - b
  have hc : c = g + m - b := rfl
  have hcLe : c ≤ g - 1 := by
    dsimp [c]
    have hmLeMul : m ≤ m * B.length alpha :=
      Nat.le_mul_of_pos_right m (by omega)
    have hmLtB : m < b := by
      rw [hb]
      omega
    omega
  have hFiring := oneOff_firing_positive_residue B alpha b m r c hLength
    hb hrLo hrHi hbm hc
  have hDelta := rankDelta_oneOff_positive_normalForm_eq_one
    B alpha c r hg hcLe hLength hrLo hrHi
  exact transmission_value_of_linearEquiv_rankDelta_eq_one hTau hFiring hDelta

end Bananas
