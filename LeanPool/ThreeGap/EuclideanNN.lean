/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import LeanPool.ThreeGap.EuclideanRecords

/-!
# The Euclidean isometry reduction: `gapVal` is the Euclidean nearest-neighbour distance

The combinatorial bound `gap_count_euclidean` (`g₂ ≤ 6`) counts distinct values of
`gapVal (deltaE α) N q`. This file identifies that quantity with the genuine **Euclidean** torus
nearest-neighbour distance, completing the Euclidean five-distance bound `g₂ ≤ 6` as a statement
about
the actual orbit `{0, α, …, Nα}` on `𝕋²`.

The isometry reduction (`TorusReduction.gapVal_eq_nnDist`) used only the **symmetry** of the cost,
so
it is stated here generically for any symmetric `c : ℤ → ℝ` and instantiated at the Euclidean defect
`c = deltaN (euclNorm 2) α` (symmetric by `deltaN_neg`). Axiom-clean.
-/

namespace ThreeGap.EuclideanRecords

open ThreeGap.Chevallier ThreeGap.SimApprox

/-- The nearest-neighbour distance for a symmetric cost `c`, abstractly: the minimum of `c (q − j)`
over the other points `j ∈ {0,…,N} ∖ {q}`. -/
noncomputable def nnDistC (c : ℤ → ℝ) (N q : ℕ) : ℝ :=
  if h : ((Finset.range (N + 1)).erase q).Nonempty then
    ((Finset.range (N + 1)).erase q).inf' h (fun j => c ((q : ℤ) - (j : ℤ))) else 0

/-- **Generic isometry reduction.** For a symmetric cost `c`, the gap value equals the
nearest-neighbour distance, via the value-preserving offset bijection `j ↦ |q − j|`. -/
theorem gapVal_eq_nnDistC (c : ℤ → ℝ) (hsymm : ∀ t : ℤ, c (-t) = c t) {N : ℕ} (hN : 2 ≤ N)
    {q : ℕ} (hq : q ≤ N) : gapVal (fun n => c (n : ℤ)) N q = nnDistC c N q := by
  have hIcc : (Finset.Icc 1 (max q (N - q))).Nonempty := by
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, ?_⟩⟩
    rcases Nat.eq_zero_or_pos q with h | h
    · exact le_trans (by omega : 1 ≤ N - q) (le_max_right _ _)
    · exact le_trans h (le_max_left _ _)
  have hEr : ((Finset.range (N + 1)).erase q).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),
      Finset.card_range]
    omega
  rw [gapVal, dif_pos hIcc, nnDistC, dif_pos hEr]
  apply le_antisymm
  · refine Finset.le_inf' _ _ (fun j hj => ?_)
    rw [Finset.mem_erase, Finset.mem_range] at hj
    obtain ⟨hjne, hjN⟩ := hj
    rcases lt_or_ge j q with hjq | hjq
    · have htmem : q - j ∈ Finset.Icc 1 (max q (N - q)) :=
        Finset.mem_Icc.mpr ⟨by omega, le_trans (by omega : q - j ≤ q) (le_max_left _ _)⟩
      have hval : c ((q - j : ℕ) : ℤ) = c ((q : ℤ) - (j : ℤ)) := by
        rw [Nat.cast_sub (by omega : j ≤ q)]
      calc (Finset.Icc 1 (max q (N - q))).inf' hIcc (fun n => c (n : ℤ))
          ≤ c ((q - j : ℕ) : ℤ) := Finset.inf'_le _ htmem
        _ = c ((q : ℤ) - (j : ℤ)) := hval
    · have hjq' : q < j := lt_of_le_of_ne hjq (by omega)
      have htmem : j - q ∈ Finset.Icc 1 (max q (N - q)) :=
        Finset.mem_Icc.mpr ⟨by omega, le_trans (by omega : j - q ≤ N - q) (le_max_right _ _)⟩
      have hval : c ((j - q : ℕ) : ℤ) = c ((q : ℤ) - (j : ℤ)) := by
        rw [Nat.cast_sub (by omega : q ≤ j),
          show (j : ℤ) - (q : ℤ) = -((q : ℤ) - (j : ℤ)) by ring, hsymm]
      calc (Finset.Icc 1 (max q (N - q))).inf' hIcc (fun n => c (n : ℤ))
          ≤ c ((j - q : ℕ) : ℤ) := Finset.inf'_le _ htmem
        _ = c ((q : ℤ) - (j : ℤ)) := hval
  · refine Finset.le_inf' _ _ (fun t ht => ?_)
    rw [Finset.mem_Icc] at ht
    obtain ⟨ht1, ht2⟩ := ht
    rcases le_or_gt t q with hcase | hcase
    · have hjmem : q - t ∈ (Finset.range (N + 1)).erase q :=
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
      have hval : c ((q : ℤ) - ((q - t : ℕ) : ℤ)) = c ((t : ℕ) : ℤ) := by
        rw [Nat.cast_sub hcase]; congr 1; ring
      calc ((Finset.range (N + 1)).erase q).inf' hEr (fun j => c ((q : ℤ) - (j : ℤ)))
          ≤ c ((q : ℤ) - ((q - t : ℕ) : ℤ)) := Finset.inf'_le _ hjmem
        _ = c ((t : ℕ) : ℤ) := hval
    · have htNq : t ≤ N - q := by
        rcases le_total q (N - q) with hle | hle
        · rwa [max_eq_right hle] at ht2
        · rw [max_eq_left hle] at ht2; omega
      have hjmem : q + t ∈ (Finset.range (N + 1)).erase q :=
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
      have hval : c ((q : ℤ) - ((q + t : ℕ) : ℤ)) = c ((t : ℕ) : ℤ) := by
        rw [Nat.cast_add, show (q : ℤ) - ((q : ℤ) + (t : ℤ)) = -(t : ℤ) by ring, hsymm]
      calc ((Finset.range (N + 1)).erase q).inf' hEr (fun j => c ((q : ℤ) - (j : ℤ)))
          ≤ c ((q : ℤ) - ((q + t : ℕ) : ℤ)) := Finset.inf'_le _ hjmem
        _ = c ((t : ℕ) : ℤ) := hval

/-- **The Euclidean torus nearest-neighbour distance** of `qα` among `{0, α, …, Nα}`, via
`d_𝕋(iα, jα) = deltaN (euclNorm 2) α (i − j)`. -/
noncomputable def nnDistE (α : Fin 2 → ℝ) (N q : ℕ) : ℝ := nnDistC (deltaN (euclNorm 2) α) N q

/-- **`g₂ ≤ 6` for the actual Euclidean nearest-neighbour distances on `𝕋²` (unconditional).** For
any
`α : Fin 2 → ℝ` with an irrational coordinate and `N ≥ 2`, the orbit `{0, α, …, Nα}` has at most
**six**
distinct nearest-neighbour distances in the Euclidean metric. (The sharp `≤ 5` needs Romanov's `K =
4`.) -/
theorem nnDistE_count_le (α : Fin 2 → ℝ) {k₀ : Fin 2} (hirr : Irrational (α k₀)) {N : ℕ}
    (hN : 2 ≤ N) : ((Finset.range (N + 1)).image (nnDistE α N)).card ≤ 6 := by
  have hsymm : ∀ t : ℤ, deltaN (euclNorm 2) α (-t) = deltaN (euclNorm 2) α t :=
    deltaN_neg (euclNorm 2) euclNorm_nonneg euclNorm_neg α
  have hcongr : (Finset.range (N + 1)).image (nnDistE α N)
      = (Finset.range (N + 1)).image (gapVal (deltaE α) N) := by
    refine Finset.image_congr (fun q hq => ?_)
    rw [Finset.mem_coe, Finset.mem_range] at hq
    exact (gapVal_eq_nnDistC (deltaN (euclNorm 2) α) hsymm hN (by omega)).symm
  rw [hcongr]
  exact gap_count_euclidean α hirr hN

end ThreeGap.EuclideanRecords
