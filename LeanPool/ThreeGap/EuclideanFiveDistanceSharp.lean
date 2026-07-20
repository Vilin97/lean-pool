/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/
import LeanPool.ThreeGap.EuclideanRecords
import LeanPool.ThreeGap.EuclideanNN
import LeanPool.ThreeGap.EuclideanGrowthFour

/-!
# The sharp Euclidean five-distance theorem `g₂ ≤ 5`

The capstone of the Haynes–Marklof route: the number of distinct Euclidean nearest-neighbour
distances
among the first `N` points of a Kronecker sequence on `𝕋²` is at most **5** (Haynes–Marklof, IMRN
2022). This sharpens the unconditional `g₂ ≤ 6` (`nnDistE_count_le`). The single sharpening is the
record-denominator growth `2 qₙ ≤ qₙ₊₄` (`euclidean_growth_four`, the `K = 4` HM Theorem 8 bound)
replacing `2 qₙ ≤ qₙ₊₅`; feeding it through Chevallier's count (`chevallier_gap_count_le` with `K =
4`)
yields `≤ 4 + 1 = 5` distances. Axiom-clean.
-/

namespace ThreeGap.EuclideanRecords

open scoped Real
open ThreeGap.SimApprox ThreeGap.Chevallier ThreeGap.DeltaCost ThreeGap.SimDirichlet

/-- **The sharp Euclidean growth `2 qₖ ≤ qₖ₊₄` for the record denominators (Haynes–Marklof).** -/
theorem bestDenom_euclidean_growth_four (α : Fin 2 → ℝ) {k₀ : Fin 2} (hirr : Irrational (α k₀))
    (hr : RecordsContinue (deltaE α)) (k : ℕ) :
    2 * bestDenom (deltaE α) hr k ≤ bestDenom (deltaE α) hr (k + 4) := by
  have hint : 2 * (bestDenom (deltaE α) hr k : ℤ) ≤ (bestDenom (deltaE α) hr (k + 4) : ℤ) :=
    euclidean_growth_four α (fun k => (bestDenom (deltaE α) hr k : ℤ))
      (fun k => Classical.choose (deltaN_euclNorm_attained α (bestDenom (deltaE α) hr k : ℤ)))
      (bestDenom_int_strictMono (deltaE α) hr)
      (fun k => le_of_eq (Classical.choose_spec
        (deltaN_euclNorm_attained α (bestDenom (deltaE α) hr k : ℤ))))
      (fun i j h => bestDenom_cost_antitone (deltaE α) hr h)
      (fun k => bestDenom_cost_lt (deltaE α) hr k)
      (fun k m hm hlt => bestDenom_hbest α hr k m hm hlt)
      (fun k => deltaE_pos α hirr (bestDenom_pos (deltaE α) hr k))
      k
  exact_mod_cast hint

/-- **`g₂ ≤ 5` (sharp Euclidean five-distance count, `gapVal` form).** -/
theorem gap_count_euclidean_five (α : Fin 2 → ℝ) {k₀ : Fin 2} (hirr : Irrational (α k₀)) {N : ℕ}
    (hN : 2 ≤ N) :
    ((Finset.range (N + 1)).image (gapVal (deltaE α) N)).card ≤ 5 := by
  have hr := recordsContinue_deltaE α hirr
  have := chevallier_gap_count_le (deltaE α) hr 4 (bestDenom_euclidean_growth_four α hirr hr) hN
  simpa using this

/-- **The sharp Euclidean five-distance theorem `g₂ ≤ 5`.** For any `α : Fin 2 → ℝ` with an
irrational
coordinate and `N ≥ 2`, the number of distinct values of the Euclidean nearest-neighbour distance
`nnDistE α N q` over `q ∈ {0, …, N}` is at most **5**. -/
theorem nnDistE_count_le_five (α : Fin 2 → ℝ) {k₀ : Fin 2} (hirr : Irrational (α k₀)) {N : ℕ}
    (hN : 2 ≤ N) : ((Finset.range (N + 1)).image (nnDistE α N)).card ≤ 5 := by
  have hsymm : ∀ t : ℤ, deltaN (euclNorm 2) α (-t) = deltaN (euclNorm 2) α t :=
    deltaN_neg (euclNorm 2) euclNorm_nonneg euclNorm_neg α
  have hcongr : (Finset.range (N + 1)).image (nnDistE α N)
      = (Finset.range (N + 1)).image (gapVal (deltaE α) N) := by
    refine Finset.image_congr (fun q hq => ?_)
    rw [Finset.mem_coe, Finset.mem_range] at hq
    exact (gapVal_eq_nnDistC (deltaN (euclNorm 2) α) hsymm hN (by omega)).symm
  rw [hcongr]
  exact gap_count_euclidean_five α hirr hN

end ThreeGap.EuclideanRecords
