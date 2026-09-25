/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffBlock

/-!
# Finite-row inversion counting for the corrected both-off block

The corrected rows of Lemma 4.30 extend to `crossOneOffCutoff g n`.  To count
their ordinary inversions as distinct affine inversions one must additionally
know that this cutoff is at most the affine period.  This file makes that
finite-row injection precise and then specializes it to the corrected
cross-one-off row function.
-/

namespace Bananas

open Utilities

/-- Ordered pairs of rows in `[lo, hi]` on which a finite row function is
strictly decreasing. -/
def finiteRowInversionPairs (lo hi : ℕ) (row : ℕ → ℕ) :
    Finset (ℕ × ℕ) :=
  ((Finset.Icc lo hi).product (Finset.Icc lo hi)).filter fun ij =>
    ij.1 < ij.2 ∧ row ij.1 > row ij.2

/-- Cast a natural-number row pair to the integer pair used by
`kInversions`. -/
def finiteRowPairCast : ℕ × ℕ → ℤ × ℤ :=
  fun ij => (ij.1, ij.2)

theorem finiteRowPairCast_injective : Function.Injective finiteRowPairCast := by
  intro x y hxy
  apply Prod.ext
  · have h := congrArg Prod.fst hxy
    change (x.1 : ℤ) = (y.1 : ℤ) at h
    exact Int.ofNat_inj.mp h
  · have h := congrArg Prod.snd hxy
    change (x.2 : ℤ) = (y.2 : ℤ) at h
    exact Int.ofNat_inj.mp h

/-- Every inversion visible in a finite row block injects into the normalized
`k`-inversion set when the final row is at most the period.  Equality
`hi = k` is allowed: the first coordinate of every inversion is strictly
smaller than its second coordinate. -/
theorem finiteRowInversionPairs_card_le_kInversionCount
    {lo hi k : ℕ} {row : ℕ → ℕ} {tau : ℤ → ℤ}
    (hRows : ∀ b : ℕ, lo ≤ b → b ≤ hi → tau b = row b)
    (hSeparate : hi ≤ k)
    (hfinite : (kInversions k tau).Finite) :
    (finiteRowInversionPairs lo hi row).card ≤ kInversionCount k tau := by
  have hmap : ∀ x : ℕ × ℕ,
      x ∈ (finiteRowInversionPairs lo hi row : Set (ℕ × ℕ)) →
        finiteRowPairCast x ∈ kInversions k tau := by
    rintro ⟨i, j⟩ hij
    change (i, j) ∈ finiteRowInversionPairs lo hi row at hij
    rw [finiteRowInversionPairs, Finset.mem_filter] at hij
    have hproduct := Finset.mem_product.mp hij.1
    have hiRange := Finset.mem_Icc.mp hproduct.1
    have hjRange := Finset.mem_Icc.mp hproduct.2
    rcases hiRange with ⟨hloi, hihi⟩
    rcases hjRange with ⟨hloj, hihj⟩
    rcases hij.2 with ⟨hij, hrow⟩
    have hTauI := hRows i hloi hihi
    have hTauJ := hRows j hloj hihj
    change (i : ℤ) < j ∧ tau i > tau j ∧
      0 ≤ (i : ℤ) ∧ (i : ℤ) < k
    rw [hTauI, hTauJ]
    refine ⟨by exact_mod_cast hij, by exact_mod_cast hrow,
      by positivity, ?_⟩
    exact_mod_cast (hij.trans_le (hihj.trans hSeparate))
  have hle := Set.ncard_le_ncard_of_injOn
    (s := (finiteRowInversionPairs lo hi row : Set (ℕ × ℕ)))
    (t := kInversions k tau) finiteRowPairCast hmap
    finiteRowPairCast_injective.injOn hfinite
  simpa [kInversionCount] using hle

/-- The finite set of all ordinary inversions forced by the corrected common
block `2 ≤ b ≤ crossOneOffCutoff g n`. -/
def crossOneOffForcedInversionPairs (g n : ℕ) : Finset (ℕ × ℕ) :=
  finiteRowInversionPairs 2 (crossOneOffCutoff g n) (crossOneOffRow g n)

/-- Under the missing period-separation hypothesis from Corollary 4.31, every
forced finite-row inversion is a distinct normalized affine inversion. -/
theorem crossOneOff_forcedInversionPairs_card_le
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 2 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hSeparate : crossOneOffCutoff g (B.length beta) ≤ k)
    (hfinite : (kInversions k tau).Finite) :
    (crossOneOffForcedInversionPairs g (B.length beta)).card ≤
      kInversionCount k tau := by
  apply finiteRowInversionPairs_card_le_kInversionCount
    (lo := 2) (hi := crossOneOffCutoff g (B.length beta))
    (row := crossOneOffRow g (B.length beta)) (tau := tau)
  · intro b hbLo hbHi
    exact transmission_crossOneOff_block B alpha beta b tau hg hab
      hAlpha hBeta hLong hbLo hbHi hTau
  · exact hSeparate
  · exact hfinite

/-- The corrected numerical target from Corollary 4.31.  Its `n = 2` branch
accounts for the corrected block beginning at row `2`; for `n ≥ 3` the
target is `choose (g-1) 2 + floor(g/(n-1))`. -/
def correctedCrossOneOffForcedCount (g n : ℕ) : ℕ :=
  if n = 2 then Nat.choose g 2
  else Nat.choose (g - 1) 2 + g / (n - 1)

/-- A sharp finite-row block certificate implies the corrected Corollary 4.31
lower bound, provided the cutoff lies in one affine period.  The remaining
pure arithmetic task is to construct `hSharp` for `crossOneOffRow`. -/
theorem crossOneOff_corrected_inversion_lower_bound_of_finiteRows
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 2 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hSeparate : crossOneOffCutoff g (B.length beta) ≤ k)
    (hfinite : (kInversions k tau).Finite)
    (hSharp : correctedCrossOneOffForcedCount g (B.length beta) ≤
      (crossOneOffForcedInversionPairs g (B.length beta)).card) :
    correctedCrossOneOffForcedCount g (B.length beta) ≤
      kInversionCount k tau := by
  exact hSharp.trans (crossOneOff_forcedInversionPairs_card_le
    B alpha beta tau hg hab hAlpha hBeta hLong hTau hSeparate hfinite)

end Bananas
