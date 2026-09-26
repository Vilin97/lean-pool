/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffKGeneral

/-!
# An extended cross-one-off inversion block

When the second marked strand has length at least `g+2`, the corrected row
formula stays in its simple positive-residue case through row `g`.  Thus the
decreasing block extends from `2,...,g-1` to `2,...,g` and contributes
`choose (g-1) 2` inversions.

The generic counting lemma below also sharpens the period boundary in
`shifted_decreasing_block_inversion_lower_bound`: the largest *first*
coordinate is one less than the final block coordinate, so
`lo + length ≤ k` is enough.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- A shifted decreasing block whose final coordinate is at most `k`
contributes all pairwise inversions to `kInversions k tau`.  Equality at the
right endpoint is valid because it can occur only as the second coordinate
of one of the injected inversions. -/
theorem shifted_decreasing_block_inversion_lower_bound_le_period
    {lo length value k : ℕ} {tau : ℤ → ℤ}
    (hValue : length ≤ value)
    (hSeparate : lo + length ≤ k)
    (hBlock : ∀ i : ℕ, i ≤ length → tau (lo + i) = (value - i : ℕ))
    (hfinite : (kInversions k tau).Finite) :
    Nat.choose (length + 1) 2 ≤ kInversionCount k tau := by
  have hmap : ∀ x : Sym2 (Fin length), x ∈ Set.univ →
      shiftedEndpointPairEmbedding lo length x ∈ kInversions k tau := by
    intro x _
    induction x using Sym2.ind with
    | _ a b =>
      simp only [shiftedEndpointPairEmbedding, endpointPairEmbedding,
        Sym2.lift_mk, kInversions, Set.mem_ofPred_eq]
      let m := min a.val b.val
      let n := max a.val b.val + 1
      have hmn : m < n := by
        dsimp [m, n]
        omega
      have hnle : n ≤ length := by
        dsimp [n]
        exact Nat.succ_le_of_lt (max_lt a.isLt b.isLt)
      have hmLt : m < length := hmn.trans_le hnle
      have hmle : m ≤ length := hmLt.le
      have htm := hBlock m hmle
      have htn := hBlock n hnle
      change (m : ℤ) + lo < (n : ℤ) + lo ∧
        tau ((m : ℤ) + lo) > tau ((n : ℤ) + lo) ∧
        0 ≤ (m : ℤ) + lo ∧ (m : ℤ) + lo < k
      have hArgM : (m : ℤ) + lo = (lo : ℤ) + m := by omega
      have hArgN : (n : ℤ) + lo = (lo : ℤ) + n := by omega
      rw [hArgM, hArgN, htm, htn]
      refine ⟨by omega, ?_, by positivity, ?_⟩
      · have hnValue : n ≤ value := hnle.trans hValue
        exact_mod_cast (show value - n < value - m by omega)
      · exact_mod_cast (show lo + m < k by omega)
  have hle := Set.ncard_le_ncard_of_injOn
    (s := (Set.univ : Set (Sym2 (Fin length))))
    (t := kInversions k tau) (shiftedEndpointPairEmbedding lo length)
    hmap (shiftedEndpointPairEmbedding_injective lo length).injOn hfinite
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
  change (Finset.univ : Finset (Sym2 (Fin length))).card ≤ _ at hle
  rw [← Finset.sym2_univ, Finset.card_sym2, Finset.card_univ] at hle
  simpa [kInversionCount] using hle

/-- If the second strand has length at least `g+2`, corrected Lemma 4.30
forces the extended decreasing block `tau(2+i)=g-i` through `i=g-2`. -/
theorem transmission_crossOneOff_extended_simple_block
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaVeryLong : g + 2 ≤ B.length beta)
    (hLong : CrossOneOffLongEnough g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    ∀ i : ℕ, i ≤ g - 2 → tau (2 + i : ℕ) = (g - i : ℕ) := by
  intro i hi
  let b := 2 + i
  have hbLo : 2 ≤ b := by simp [b]
  have hbLe : b ≤ g := by
    dsimp [b]
    omega
  have hbHi : b ≤ crossOneOffCutoff g (B.length beta) := by
    unfold crossOneOffCutoff
    exact hbLe.trans (Nat.le_add_right g _)
  have hBeta : 1 < B.length beta := by omega
  have hRow := transmission_crossOneOff_block B alpha beta b tau
    (by omega) hab hAlpha hBeta hLong hbLo hbHi hTau
  have hbLt : b < B.length beta := hbLe.trans_lt (by omega)
  have hMod : b % B.length beta = b := Nat.mod_eq_of_lt hbLt
  have hDiv : b / B.length beta = 0 := Nat.div_eq_of_lt hbLt
  have hbNeLast : b ≠ B.length beta - 1 := by omega
  rw [hRow]
  simp [crossOneOffRow, hMod, hDiv, hbNeLast, b]
  omega

/-- The extended simple block contributes `choose (g-1) 2` normalized
inversions as soon as `g ≤ k`. -/
theorem crossOneOff_extended_simple_inversion_lower_bound
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaVeryLong : g + 2 ≤ B.length beta)
    (hLong : CrossOneOffLongEnough g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hSeparate : g ≤ k)
    (hfinite : (kInversions k tau).Finite) :
    Nat.choose (g - 1) 2 ≤ kInversionCount k tau := by
  have hBlock := transmission_crossOneOff_extended_simple_block
    B alpha beta tau hg hab hAlpha hBetaVeryLong hLong hTau
  have hCount := shifted_decreasing_block_inversion_lower_bound_le_period
    (lo := 2) (length := g - 2) (value := g) (k := k) (tau := tau)
    (by omega) (by omega) hBlock hfinite
  have hLength : g - 2 + 1 = g - 1 := by omega
  rw [hLength] at hCount
  exact hCount

/-- For a second strand strictly longer than `g+1`, the corrected inversion
block rules out `k`-general transmission already in genus five. -/
theorem crossOneOff_not_kGeneral_of_five_le_genus
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 5 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaVeryLong : g + 2 ≤ B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta)) :
    ¬ KGeneralTransmission
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k := by
  intro hK
  have hPeriod : g ≤ k := crossOneOff_kGeneral_period_ge_genus
    B alpha beta (by omega) hab hAlpha (by omega) hK
  obtain ⟨tau, hTau, _hAffine, hFinite, hUpper⟩ :=
    hK.2.2 (g • oneChip (rightEndpoint B))
  have hLower := crossOneOff_extended_simple_inversion_lower_bound
    B alpha beta tau (by omega) hab hAlpha hBetaVeryLong hLong
      hTau hPeriod hFinite
  have hGenus : Int.toNat (genus
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)).graph) = g := by
    change Int.toNat (genus B.graph) = g
    rw [B.genus_graph]
    omega
  rw [hGenus] at hUpper
  have hBound : Nat.choose (g - 1) 2 ≤ g := hLower.trans hUpper
  let product := (g - 1) * (g - 2)
  have hChoose : Nat.choose (g - 1) 2 = product / 2 := by
    rw [Nat.choose_two_right]
    have hPred : g - 1 - 1 = g - 2 := by omega
    rw [hPred]
  have hProduct : 2 * g + 2 ≤ product := by
    dsimp [product]
    have hOne : g - 1 + 1 = g := Nat.sub_add_cancel (by omega)
    have hTwo : g - 2 + 2 = g := Nat.sub_add_cancel (by omega)
    nlinarith
  rw [hChoose] at hBound
  omega

end Bananas
