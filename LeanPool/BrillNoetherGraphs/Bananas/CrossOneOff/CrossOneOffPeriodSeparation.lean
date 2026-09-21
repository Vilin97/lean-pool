/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffKGeneral

/-!
# Period separation for the corrected cross-one-off block

The existing torsion dichotomy records only `g ≤ k`, but its nonzero-rise
argument actually proves the strict inequality `g < k`.  In the long-second-
strand regime the zero-rise exception is impossible.  Since then
`crossOneOffCutoff g n ≤ g+1`, this supplies exactly the separation needed
by the corrected finite-row inversion count.
-/

namespace Bananas

open Utilities
open scoped BigOperators

private theorem crossOneOff_sum_erase_ge_card {n : ℕ} (s : Fin n → ℤ)
    (a : Fin n) (hpos : ∀ b, b ≠ a → 0 < s b) :
    (n - 1 : ℕ) ≤ ∑ b ∈ (Finset.univ.erase a), s b := by
  have hcard : (Finset.univ.erase a).card = n - 1 := by simp
  calc
    (((n - 1 : ℕ) : ℤ)) =
        ∑ _b ∈ (Finset.univ.erase a), (1 : ℤ) := by simp [hcard]
    _ ≤ ∑ b ∈ (Finset.univ.erase a), s b := by
      apply Finset.sum_le_sum
      intro b hb
      have := hpos b (Finset.ne_of_mem_erase hb)
      omega

private theorem crossOneOff_sum_erase_le_neg_card
    {n : ℕ} (s : Fin n → ℤ) (a : Fin n)
    (hneg : ∀ b, b ≠ a → s b < 0) :
    ∑ b ∈ (Finset.univ.erase a), s b ≤ -(((n - 1 : ℕ) : ℤ)) := by
  have hcard : (Finset.univ.erase a).card = n - 1 := by simp
  calc
    ∑ b ∈ (Finset.univ.erase a), s b ≤
        ∑ _b ∈ (Finset.univ.erase a), (-1 : ℤ) := by
      apply Finset.sum_le_sum
      intro b hb
      have := hneg b (Finset.ne_of_mem_erase hb)
      omega
    _ = -(((n - 1 : ℕ) : ℤ)) := by simp [hcard]

/-- A cross-one-off exact torsion order is strictly larger than the genus
when the second strand has length at least `g+1`. -/
theorem crossOneOff_torsionOrder_gt_genus_of_second_long
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hTO : IsTorsionOrder
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k) :
    g < k := by
  let i : B.PathPosition alpha := ⟨1, by omega⟩
  let j : B.PathPosition beta := ⟨B.length beta - 1, by omega⟩
  have hi : B.IsInteriorPosition alpha i := by
    change 0 < (1 : ℕ) ∧ 1 < B.length alpha
    exact ⟨by omega, hAlpha⟩
  have hj : B.IsInteriorPosition beta j := by
    change 0 < B.length beta - 1 ∧ B.length beta - 1 < B.length beta
    omega
  obtain ⟨script, rise, slope, _hrise, hsum, hAlphaSlope, hBetaSlope,
      hOther, hRise⟩ :=
    interior_torsion_rise_zero_or_period_ge_genus (by omega) B alpha beta
      i j hi hj hab hTO
  have hk : 0 < k := hTO.1.1
  rcases lt_trichotomy rise 0 with hneg | hzero | hpos
  · have hnegOther : ∀ gamma, gamma ≠ alpha → slope gamma < 0 := by
      intro gamma hgammaAlpha
      by_cases hgammaBeta : gamma = beta
      · subst gamma
        have hlen : (0 : ℤ) < B.length beta := by
          exact_mod_cast B.length_pos beta
        have hnj : (0 : ℤ) < ((B.length beta - j.val : ℕ) : ℤ) := by
          exact_mod_cast Nat.sub_pos_of_lt hj.2
        have hkz : (0 : ℤ) < k := by exact_mod_cast hk
        nlinarith [hBetaSlope]
      · have hEq := hOther gamma hgammaAlpha hgammaBeta
        have hlen : (0 : ℤ) < B.length gamma := by
          exact_mod_cast B.length_pos gamma
        nlinarith
    have hAlphaLt : slope alpha < k := by
      have hlen : (0 : ℤ) < B.length alpha := by
        exact_mod_cast B.length_pos alpha
      have hiPos : (0 : ℤ) < i.val := by exact_mod_cast hi.1
      have hkz : (0 : ℤ) < k := by exact_mod_cast hk
      rw [Nat.cast_sub (Nat.le_of_lt hi.2)] at hAlphaSlope
      nlinarith
    have hErase := crossOneOff_sum_erase_le_neg_card slope alpha hnegOther
    have hsplit : ∑ gamma, slope gamma = slope alpha +
        ∑ gamma ∈ (Finset.univ.erase alpha), slope gamma := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ alpha)]
    have hgCast : ((((g + 1) - 1 : ℕ) : ℤ)) = g := by norm_num
    rw [hgCast] at hErase
    rw [hsplit] at hsum
    have hStrict : (g : ℤ) < k := by nlinarith
    exact_mod_cast hStrict
  · have hAlphaZero := hAlphaSlope
    have hBetaZero := hBetaSlope
    rw [hzero] at hAlphaZero hBetaZero
    simp only [zero_add, zero_sub] at hAlphaZero hBetaZero
    have hOtherZero : ∀ gamma, gamma ≠ alpha → gamma ≠ beta →
        (B.length gamma : ℤ) * slope gamma = 0 := by
      intro gamma hgammaAlpha hgammaBeta
      simpa [hzero] using hOther gamma hgammaAlpha hgammaBeta
    obtain ⟨_alphaTwo, hBetaTwo⟩ :=
      zero_rise_cross_oneOff_forces_both_length_two
        B alpha beta i j hab (by simp [i]) (by simp [j]; omega)
          hi hj hk slope hsum hAlphaZero
          (by simpa [neg_mul] using hBetaZero) hOtherZero
    omega
  · have hposOther : ∀ gamma, gamma ≠ beta → 0 < slope gamma := by
      intro gamma hgammaBeta
      by_cases hgammaAlpha : gamma = alpha
      · subst gamma
        have hlen : (0 : ℤ) < B.length alpha := by
          exact_mod_cast B.length_pos alpha
        have hni : (0 : ℤ) < ((B.length alpha - i.val : ℕ) : ℤ) := by
          exact_mod_cast Nat.sub_pos_of_lt hi.2
        have hkz : (0 : ℤ) < k := by exact_mod_cast hk
        nlinarith [hAlphaSlope]
      · have hEq := hOther gamma hgammaAlpha hgammaBeta
        have hlen : (0 : ℤ) < B.length gamma := by
          exact_mod_cast B.length_pos gamma
        nlinarith
    have hBetaGt : -(k : ℤ) < slope beta := by
      have hlen : (0 : ℤ) < B.length beta := by
        exact_mod_cast B.length_pos beta
      have hjPos : (0 : ℤ) < j.val := by exact_mod_cast hj.1
      have hkz : (0 : ℤ) < k := by exact_mod_cast hk
      rw [Nat.cast_sub (Nat.le_of_lt hj.2)] at hBetaSlope
      nlinarith
    have hErase := crossOneOff_sum_erase_ge_card slope beta hposOther
    have hsplit : ∑ gamma, slope gamma = slope beta +
        ∑ gamma ∈ (Finset.univ.erase beta), slope gamma := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ beta)]
    have hgCast : ((((g + 1) - 1 : ℕ) : ℤ)) = g := by norm_num
    rw [hgCast] at hErase
    rw [hsplit] at hsum
    have hStrict : (g : ℤ) < k := by nlinarith
    exact_mod_cast hStrict

/-- The exact torsion order separates the whole corrected row cutoff from
the affine period. -/
theorem crossOneOff_cutoff_le_torsionOrder
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hTO : IsTorsionOrder
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k) :
    crossOneOffCutoff g (B.length beta) ≤ k := by
  have hPeriod := crossOneOff_torsionOrder_gt_genus_of_second_long
    B alpha beta hg hab hAlpha hBetaLong hTO
  unfold crossOneOffCutoff
  have hDiv : g / (B.length beta - 1) ≤ 1 := by
    have hDen : g ≤ B.length beta - 1 := by omega
    calc
      g / (B.length beta - 1) ≤
          (B.length beta - 1) / (B.length beta - 1) :=
        Nat.div_le_div_right hDen
      _ = 1 := Nat.div_self (by omega)
  omega

/-- In particular, a `k`-general cross-one-off marking supplies the missing
period-separation premise in corrected Corollary 4.31. -/
theorem crossOneOff_kGeneral_cutoff_le_period
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hK : KGeneralTransmission
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k) :
    crossOneOffCutoff g (B.length beta) ≤ k := by
  let i : B.PathPosition alpha := ⟨1, by omega⟩
  let j : B.PathPosition beta := ⟨B.length beta - 1, by omega⟩
  have hi : B.IsInteriorPosition alpha i := by
    change 0 < (1 : ℕ) ∧ 1 < B.length alpha
    exact ⟨by omega, hAlpha⟩
  have hj : B.IsInteriorPosition beta j := by
    change 0 < B.length beta - 1 ∧ B.length beta - 1 < B.length beta
    omega
  have huv : strandVertex B alpha i ≠ strandVertex B beta j := by
    intro hEq
    exact hab (strand_eq_of_interior_vertex_eq
      B alpha beta i j hi hj hEq)
  have hTO : IsTorsionOrder
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) k :=
    hK.isTorsionOrder huv (banana_graph_connected B) (by
      change 0 < genus B.graph
      rw [B.genus_graph]
      omega)
  exact crossOneOff_cutoff_le_torsionOrder
    B alpha beta hg hab hAlpha hBetaLong hTO

end Bananas
