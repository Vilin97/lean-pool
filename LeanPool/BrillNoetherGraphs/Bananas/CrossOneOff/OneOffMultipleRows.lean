/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.OneOffTransmission

/-!
# Multiple-residue rows for the same-strand one-off marking

This file proves the first full residue class in Lemma 4.23.  If the row
index is `b = m n`, where `n` is the length of the marked strand, then the
prefix firing reduces the marked twist of `g • rightEndpoint` to
`(g+m-b) • rightEndpoint`.  Its marked second difference is one, forcing
`tau(b)=m`.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- The multiple-residue firing identity for the one-off marking. -/
theorem oneOff_firing_multiple
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (b m c : ℕ) (hLength : 1 < B.length alpha)
    (hb : b = m * B.length alpha) (hbm : b ≤ g + m)
    (hc : c = g + m - b) :
    linearEquiv B.graph
      (g • oneChip (rightEndpoint B) +
        (m : ℤ) • oneChip (leftEndpoint B) -
        (b : ℤ) • oneChip
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (c • oneChip (rightEndpoint B)) := by
  have hMark := crossOneOff_second_mark_multiple B alpha b m 0
    (by simpa using hb) (by omega)
  rw [strandVertex_zero B alpha] at hMark
  unfold linearEquiv at hMark ⊢
  have hNeg := (principalDivisors B.graph).neg_mem hMark
  convert hNeg using 1
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul]
  rw [nsmul_eq_mul, nsmul_eq_mul]
  have hcInt : (c : ℤ) = (g : ℤ) + m - b := by
    exact_mod_cast (show c = g + m - b from hc)
  rw [hcInt]
  ring

/-- The right-endpoint rank-difference theorem including coefficient zero.
The positive case is `rankDelta_oneOff_rightEndpoint_nsmul_eq_one`; at zero
all three chip-subtracted divisors have negative degree. -/
theorem rankDelta_oneOff_rightEndpoint_nsmul_eq_one_all
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (c : ℕ) (hcg : c ≤ g) (hLength : 1 < B.length alpha) :
    rankDelta
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (c • oneChip (rightEndpoint B)) = 1 := by
  by_cases hcZero : c = 0
  · subst c
    have hLeftDeg : deg
        ((0 : CFDiv B.graph) - oneChip (leftEndpoint B)) < 0 := by simp
    have hMarkDeg : deg
        ((0 : CFDiv B.graph) - oneChip
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) < 0 := by
      simp
    have hBothDeg : deg
        ((0 : CFDiv B.graph) - oneChip (leftEndpoint B) -
          oneChip
            (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) < 0 := by
      simp
    unfold rankDelta
    simp only [zero_nsmul]
    change rank B.graph 0 -
        rank B.graph ((0 : CFDiv B.graph) - oneChip (leftEndpoint B)) -
        rank B.graph ((0 : CFDiv B.graph) - oneChip
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) +
        rank B.graph ((0 : CFDiv B.graph) - oneChip (leftEndpoint B) -
          oneChip
            (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) = 1
    rw [zero_divisor_rank,
      rank_neg_one_of_deg_neg B.graph _ hLeftDeg,
      rank_neg_one_of_deg_neg B.graph _ hMarkDeg,
      rank_neg_one_of_deg_neg B.graph _ hBothDeg]
    norm_num
  · exact rankDelta_oneOff_rightEndpoint_nsmul_eq_one
      B alpha c (Nat.pos_of_ne_zero hcZero) hcg hLength

/-- Lemma 4.23, multiple-residue case: if `b=m·n`, the transmission row
has value `m`.  The inequality `b ≤ g+m` is exactly the nonnegativity of
the residual right-endpoint coefficient used in the paper. -/
theorem transmission_oneOff_multiple
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (b m : ℕ) (tau : ℤ → ℤ)
    (hLength : 1 < B.length alpha)
    (hb : b = m * B.length alpha) (hbm : b ≤ g + m)
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    tau (b : ℤ) = (m : ℕ) := by
  let c := g + m - b
  have hc : c = g + m - b := rfl
  have hmLeB : m ≤ b := by
    rw [hb]
    have : 1 ≤ B.length alpha := by omega
    nlinarith
  have hcg : c ≤ g := by
    dsimp [c]
    omega
  have hFiring := oneOff_firing_multiple B alpha b m c hLength
    hb hbm hc
  have hDelta := rankDelta_oneOff_rightEndpoint_nsmul_eq_one_all
    B alpha c hcg hLength
  exact transmission_value_of_linearEquiv_rankDelta_eq_one hTau hFiring hDelta

/-- The first positive multiple row, recorded without auxiliary quotient
variables: if the strand length is at most `g+1`, then `tau(n)=1`. -/
theorem transmission_oneOff_length
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (tau : ℤ → ℤ) (hLength : 1 < B.length alpha)
    (hLengthBound : B.length alpha ≤ g + 1)
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    tau (B.length alpha : ℤ) = 1 := by
  apply transmission_oneOff_multiple B alpha (B.length alpha) 1 tau
    hLength (by simp) (by simpa using hLengthBound) hTau

/-! ## Complement-residue rows -/

/-- The corrected firing identity when `b+1=m·n`.  The normal form is
`gL + v + (g+m-b-1)R`; this has the same degree as the marked twist.
The right-endpoint coefficient printed in the paper's intermediate display
does not have that degree. -/
theorem oneOff_firing_complement
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (b m c : ℕ) (hLength : 1 < B.length alpha) (hm : 0 < m)
    (hb : b + 1 = m * B.length alpha) (hbm : b + 1 ≤ g + m)
    (hc : c = g + m - b - 1) :
    linearEquiv B.graph
      (g • oneChip (rightEndpoint B) +
        ((g + m : ℕ) : ℤ) • oneChip (leftEndpoint B) -
        (b : ℤ) • oneChip
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      ((g : ℤ) • oneChip (leftEndpoint B) +
        oneChip
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
        c • oneChip (rightEndpoint B)) := by
  have hDecompose : b = (m - 1) * B.length alpha +
      (B.length alpha - 1) := by
    have hRhsSucc : (m - 1) * B.length alpha +
        (B.length alpha - 1) + 1 = m * B.length alpha := by
      calc
        (m - 1) * B.length alpha + (B.length alpha - 1) + 1 =
            (m - 1) * B.length alpha + B.length alpha := by omega
        _ = ((m - 1) + 1) * B.length alpha := by
          rw [Nat.add_mul, one_mul]
        _ = m * B.length alpha := by rw [Nat.sub_add_cancel hm]
    omega
  have hMark := crossOneOff_second_mark_multiple B alpha b (m - 1)
    (B.length alpha - 1) hDecompose (by omega)
  unfold linearEquiv at hMark ⊢
  have hNeg := (principalDivisors B.graph).neg_mem hMark
  convert hNeg using 1
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul]
  rw [nsmul_eq_mul, nsmul_eq_mul]
  have hmPred : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  have hcInt : (c : ℤ) = (g : ℤ) + m - b - 1 := by
    have hcAdd : c + b + 1 = g + m := by omega
    have hcAddInt : (c : ℤ) + b + 1 = (g : ℤ) + m := by
      exact_mod_cast hcAdd
    omega
  rw [hmPred, hcInt]
  push_cast
  ring

/-- The marked second difference of the complement-residue normal form is
one. -/
theorem rankDelta_oneOff_complement_normalForm_eq_one
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (c : ℕ) (hg : 0 < g) (hc : c ≤ g - 1)
    (hLength : 1 < B.length alpha) :
    rankDelta
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      ((g : ℤ) • oneChip (leftEndpoint B) +
        oneChip
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) +
        c • oneChip (rightEndpoint B)) = 1 := by
  let v := strandVertex B alpha
    (⟨B.length alpha - 1, by omega⟩ : B.PathPosition alpha)
  let E : CFDiv B.graph := oneChip v
  have hv : B.IsInteriorPosition alpha
      (⟨B.length alpha - 1, by omega⟩ : B.PathPosition alpha) := by
    change 0 < B.length alpha - 1 ∧ B.length alpha - 1 < B.length alpha
    omega
  have hE : IsSemibreak B E :=
    isSemibreak_one_strand_chip B alpha _ hv
  have hZero : IsSemibreak B (0 : CFDiv B.graph) := isSemibreak_zero B
  have hdegE : deg E = 1 := by simp [E, deg_one_chip]
  have hD : (g : ℤ) • oneChip (leftEndpoint B) + E +
      c • oneChip (rightEndpoint B) =
      bananaNormalForm B (g : ℤ) (c : ℤ) E := by
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [nsmul_eq_mul]
    ring
  have hDU : (g : ℤ) • oneChip (leftEndpoint B) + E +
      c • oneChip (rightEndpoint B) - oneChip (leftEndpoint B) =
      bananaNormalForm B ((g : ℤ) - 1) (c : ℤ) E := by
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [nsmul_eq_mul]
    ring
  have hDV : (g : ℤ) • oneChip (leftEndpoint B) + E +
      c • oneChip (rightEndpoint B) - oneChip v =
      bananaNormalForm B (g : ℤ) (c : ℤ) 0 := by
    dsimp [E]
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul]
    rw [nsmul_eq_mul]
    ring
  have hBoth : (g : ℤ) • oneChip (leftEndpoint B) + E +
      c • oneChip (rightEndpoint B) - oneChip (leftEndpoint B) -
      oneChip v =
      bananaNormalForm B ((g : ℤ) - 1) (c : ℤ) 0 := by
    dsimp [E]
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul]
    rw [nsmul_eq_mul]
    ring
  have hRangeE : (c : ℤ) + deg E ≤ (g : ℤ) := by
    rw [hdegE]
    exact_mod_cast (show c + 1 ≤ g by omega)
  have hRangeZero : (c : ℤ) + deg (0 : CFDiv B.graph) ≤ (g : ℤ) := by
    simp
    exact_mod_cast hc.trans (Nat.sub_le g 1)
  have hRankD := rank_bananaNormalForm B (g : ℤ) (c : ℤ) E hE
    (by omega) (by omega) hRangeE
  have hRankDU := rank_bananaNormalForm B ((g : ℤ) - 1) (c : ℤ) E hE
    (by omega) (by omega) hRangeE
  have hRankDV := rank_bananaNormalForm B (g : ℤ) (c : ℤ) 0 hZero
    (by omega) (by omega) hRangeZero
  have hRankBoth := rank_bananaNormalForm B ((g : ℤ) - 1) (c : ℤ) 0 hZero
    (by omega) (by omega) hRangeZero
  have hRankD' : rank B.graph
      ((g : ℤ) • oneChip (leftEndpoint B) + E +
        c • oneChip (rightEndpoint B)) = (c : ℤ) + 1 := by
    rw [hD, hRankD, hdegE]
    omega
  have hRankDU' : rank B.graph
      ((g : ℤ) • oneChip (leftEndpoint B) + E +
        c • oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) = c := by
    rw [hDU, hRankDU, hdegE]
    omega
  have hRankDV' : rank B.graph
      ((g : ℤ) • oneChip (leftEndpoint B) + E +
        c • oneChip (rightEndpoint B) - oneChip v) = c := by
    rw [hDV, hRankDV]
    simp
  have hRankBoth' : rank B.graph
      ((g : ℤ) • oneChip (leftEndpoint B) + E +
        c • oneChip (rightEndpoint B) - oneChip (leftEndpoint B) -
        oneChip v) = c := by
    rw [hBoth, hRankBoth]
    simp
    omega
  unfold rankDelta
  change rank B.graph ((g : ℤ) • oneChip (leftEndpoint B) + E +
      c • oneChip (rightEndpoint B)) -
    rank B.graph ((g : ℤ) • oneChip (leftEndpoint B) + E +
      c • oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) -
    rank B.graph ((g : ℤ) • oneChip (leftEndpoint B) + E +
      c • oneChip (rightEndpoint B) - oneChip v) +
    rank B.graph ((g : ℤ) • oneChip (leftEndpoint B) + E +
      c • oneChip (rightEndpoint B) - oneChip (leftEndpoint B) -
      oneChip v) = 1
  rw [hRankD', hRankDU', hRankDV', hRankBoth']
  omega

/-- Lemma 4.23, complement-residue case: if `b+1=m·n`, then the
transmission value is `g+m`. -/
theorem transmission_oneOff_complement
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (b m : ℕ) (tau : ℤ → ℤ) (hg : 0 < g)
    (hLength : 1 < B.length alpha) (hm : 0 < m)
    (hb : b + 1 = m * B.length alpha) (hbm : b + 1 ≤ g + m)
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    tau (b : ℤ) = (g + m : ℕ) := by
  let c := g + m - b - 1
  have hc : c = g + m - b - 1 := rfl
  have hcLe : c ≤ g - 1 := by
    dsimp [c]
    have hmLeB : m ≤ b := by
      nlinarith [show 2 ≤ B.length alpha from hLength]
    omega
  have hFiring := oneOff_firing_complement B alpha b m c hLength hm
    hb hbm hc
  have hDelta := rankDelta_oneOff_complement_normalForm_eq_one
    B alpha c hg hcLe hLength
  exact transmission_value_of_linearEquiv_rankDelta_eq_one hTau hFiring hDelta

end Bananas
