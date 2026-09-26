/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffBlock
public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointCardinality

/-!
# A rigorously separated inversion block for cross-one-off markings

The ordinary inversions counted here have first coordinate below `k` by an
explicit hypothesis.  This is the period-separation condition missing from
the printed proof of Corollary 4.31.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Translate the standard pair embedding into a natural interval beginning
at `lo`. -/
noncomputable def shiftedEndpointPairEmbedding (lo length : ℕ) :
    Sym2 (Fin length) → ℤ × ℤ := fun x =>
  let p := endpointPairEmbedding length x
  (p.1 + lo, p.2 + lo)

theorem shiftedEndpointPairEmbedding_injective (lo length : ℕ) :
    Function.Injective (shiftedEndpointPairEmbedding lo length) := by
  intro x y hxy
  apply endpointPairEmbedding_injective length
  apply Prod.ext
  · have h := congrArg Prod.fst hxy
    change (endpointPairEmbedding length x).1 + (lo : ℤ) =
      (endpointPairEmbedding length y).1 + (lo : ℤ) at h
    omega
  · have h := congrArg Prod.snd hxy
    change (endpointPairEmbedding length x).2 + (lo : ℤ) =
      (endpointPairEmbedding length y).2 + (lo : ℤ) at h
    omega

/-- A shifted decreasing block contributes all of its ordinary inversions to
the normalized `k`-inversion set, provided the block's possible first
coordinates lie in `[0,k)`. -/
theorem shifted_decreasing_block_inversion_lower_bound
    {lo length value k : ℕ} {tau : ℤ → ℤ}
    (hValue : length ≤ value)
    (hSeparate : lo + length < k)
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
      have hmle : m ≤ length := by
        exact (Nat.le_of_lt hmn).trans hnle
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

/-- In the long-second-strand regime, corrected Lemma 4.30 restricts to the
simple decreasing block `tau(2+i)=g-i` for `0 ≤ i ≤ g-3`. -/
theorem transmission_crossOneOff_simple_block
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hLong : CrossOneOffLongEnough g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    ∀ i : ℕ, i ≤ g - 3 → tau (2 + i : ℕ) = (g - i : ℕ) := by
  intro i hi
  let b := 2 + i
  have hbLo : 2 ≤ b := by simp [b]
  have hbLe : b ≤ g - 1 := by
    dsimp [b]
    omega
  have hbHi : b ≤ crossOneOffCutoff g (B.length beta) := by
    unfold crossOneOffCutoff
    exact hbLe.trans ((Nat.sub_le g 1).trans (Nat.le_add_right g _))
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

/-- Corollary 4.29's decreasing-block count, with the period separation made
explicit.  The hypothesis `g ≤ k` is sufficient because every first
coordinate in the injected family is at most `g-2`.

This deliberately does not claim the stronger corrected Corollary 4.31
count, whose rows extend to `crossOneOffCutoff` and require the additional
unproved separation `crossOneOffCutoff g n ≤ k`. -/
theorem crossOneOff_simple_inversion_lower_bound
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hLong : CrossOneOffLongEnough g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hSeparate : g ≤ k)
    (hfinite : (kInversions k tau).Finite) :
    Nat.choose (g - 2) 2 ≤ kInversionCount k tau := by
  have hBlock := transmission_crossOneOff_simple_block B alpha beta tau
    hg hab hAlpha hBetaLong hLong hTau
  have hCount := shifted_decreasing_block_inversion_lower_bound
    (lo := 2) (length := g - 3) (value := g) (k := k) (tau := tau)
    (by omega) (by omega) hBlock hfinite
  have hLength : g - 3 + 1 = g - 2 := by omega
  rw [hLength] at hCount
  exact hCount

end Bananas
