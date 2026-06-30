/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import LeanPool.ThreeGap.EuclideanDefect
import LeanPool.ThreeGap.SimultaneousDirichlet

/-!
# Euclidean record denominators ⟹ `g₂ ≤ 6` (combinatorial, unconditional)

Assembles the Euclidean route: with the **Euclidean defect cost** `r q = deltaN(euclNorm 2) α q`,
the
record denominators `bestDenom r` satisfy every hypothesis of `euclidean_growth_five` —
`hattain` from `deltaN_euclNorm_attained`, `hdec`/`hbest` from the record structure, `hpos` from
irrationality — so `2 q_k ≤ q_{k+5}`. Feeding this `K = 5` growth into Chevallier's count
(`chevallier_gap_count_le`) gives the Euclidean five-distance bound **`g₂ ≤ 6`**: at most six
distinct
values of the Euclidean nearest-neighbour distance `gapVal (deltaE α) N q`.

`RecordsContinue` (the irrationality input) is discharged exactly as for the sup norm, transferring
Dirichlet via `deltaN(euclNorm 2) α q ≤ √2 · delta α q` (the Euclidean norm is `≤ √2 ·` the sup norm
in the plane). The sharp `g₂ ≤ 5` needs Romanov's `K = 4`; this is the `K = 5` bound. Axiom-clean.
-/

namespace ThreeGap.EuclideanRecords

open scoped Real
open ThreeGap.SimApprox ThreeGap.Chevallier ThreeGap.DeltaCost ThreeGap.SimDirichlet

/-- The **Euclidean defect cost** as a function of a natural denominator. -/
noncomputable def deltaE (α : Fin 2 → ℝ) : ℕ → ℝ := fun q => deltaN (euclNorm 2) α (q : ℤ)

/-- The Euclidean norm is at most `√2 ·` the sup norm in the plane. -/
theorem euclNorm_le_sqrt_two_mul (x : Fin 2 → ℝ) : euclNorm 2 x ≤ Real.sqrt 2 * ‖x‖ := by
  rw [euclNorm_eq]
  have hb : ∀ i : Fin 2, (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    intro i
    have h1 : |x i| ≤ ‖x‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x i
    calc (x i) ^ 2 = |x i| ^ 2 := (sq_abs (x i)).symm
      _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc Real.sqrt (∑ i, (x i) ^ 2) ≤ Real.sqrt (∑ _i : Fin 2, ‖x‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i _ => hb i))
    _ = Real.sqrt 2 * ‖x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show ((2 : ℕ) : ℝ) * ‖x‖ ^ 2 = 2 * ‖x‖ ^ 2 by norm_num,
          Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]

/-- **Dirichlet transferred to the Euclidean defect:** `δ^E_q ≤ √2 · δ_q`. -/
theorem deltaE_le_sqrt_two_mul (α : Fin 2 → ℝ) (q : ℤ) :
    deltaN (euclNorm 2) α q ≤ Real.sqrt 2 * delta α q := by
  calc deltaN (euclNorm 2) α q ≤ euclNorm 2 (rem α q (nearestInt α q)) :=
        deltaN_le (euclNorm 2) euclNorm_nonneg α q (nearestInt α q)
    _ ≤ Real.sqrt 2 * ‖rem α q (nearestInt α q)‖ := euclNorm_le_sqrt_two_mul _
    _ = Real.sqrt 2 * delta α q := by rw [delta_attained]

/-- **Euclidean Dirichlet:** the defect gets arbitrarily small. -/
theorem exists_deltaE_lt (α : Fin 2 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 1 ≤ q ∧ deltaE α q < ε := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨q, hq1, hq2⟩ := exists_delta_lt α (show 0 < ε / Real.sqrt 2 by positivity)
  refine ⟨q, hq1, ?_⟩
  calc deltaE α q ≤ Real.sqrt 2 * delta α q := deltaE_le_sqrt_two_mul α q
    _ < Real.sqrt 2 * (ε / Real.sqrt 2) := by exact mul_lt_mul_of_pos_left hq2 hs2
    _ = ε := by field_simp

/-- **Euclidean positivity:** `δ^E_q > 0` for `q ≥ 1` when some coordinate is irrational. -/
theorem deltaE_pos (α : Fin 2 → ℝ) {k₀ : Fin 2} (hirr : Irrational (α k₀)) {q : ℕ} (hq : 1 ≤ q) :
    0 < deltaE α q := by
  have hirrq : Irrational ((q : ℝ) * α k₀) := hirr.natCast_mul (by omega : q ≠ 0)
  have hne : (q : ℝ) * α k₀ - round ((q : ℝ) * α k₀) ≠ 0 := fun h =>
    hirrq ⟨round ((q : ℝ) * α k₀), by push_cast; linarith [h]⟩
  have hposc : 0 < |(q : ℝ) * α k₀ - round ((q : ℝ) * α k₀)| := abs_pos.mpr hne
  refine lt_of_lt_of_le hposc ?_
  refine le_ciInf (fun p => ?_)
  calc |(q : ℝ) * α k₀ - round ((q : ℝ) * α k₀)|
      ≤ |(q : ℝ) * α k₀ - (p k₀ : ℝ)| := round_le _ _
    _ = |rem α (q : ℤ) p k₀| := by rw [rem]; simp [Pi.smul_apply, smul_eq_mul]
    _ ≤ euclNorm 2 (rem α (q : ℤ) p) := abs_le_euclNorm _ k₀

/-- **`RecordsContinue (deltaE α)` from irrationality.** -/
theorem recordsContinue_deltaE (α : Fin 2 → ℝ) {k₀ : Fin 2} (hirr : Irrational (α k₀)) :
    RecordsContinue (deltaE α) := by
  intro q hq
  by_contra hcon
  push Not at hcon
  set δ₀ : ℝ := (Finset.Icc 1 q).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hq⟩⟩ (deltaE α) with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀, Finset.lt_inf'_iff]
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact deltaE_pos α hirr hj.1
  have hlb : ∀ q' : ℕ, 1 ≤ q' → δ₀ ≤ deltaE α q' := by
    intro q' hq'
    rcases le_or_gt q' q with h | h
    · exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hq', h⟩)
    · calc δ₀ ≤ deltaE α q := Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hq, le_refl q⟩)
        _ ≤ deltaE α q' := hcon q' h
  obtain ⟨q', hq'1, hq'2⟩ := exists_deltaE_lt α hδ₀pos
  exact absurd (hlb q' hq'1) (not_le.mpr hq'2)

/-- `hbest` for the Euclidean record denominators (strict best-approximation property). -/
theorem bestDenom_hbest (α : Fin 2 → ℝ) (hr : RecordsContinue (deltaE α)) (k : ℕ) (m : ℤ)
    (hpos : 0 < m) (hlt : m < (bestDenom (deltaE α) hr k : ℤ)) :
    deltaN (euclNorm 2) α (bestDenom (deltaE α) hr k : ℤ) < deltaN (euclNorm 2) α m := by
  have hmnat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hpos.le
  have hj1 : 1 ≤ m.toNat := by omega
  have hj2 : m.toNat < bestDenom (deltaE α) hr k := by
    have : (m.toNat : ℤ) < (bestDenom (deltaE α) hr k : ℤ) := by rw [hmnat]; exact hlt
    exact_mod_cast this
  have := bestDenom_strict_floor (deltaE α) hr k hj1 hj2
  simp only [deltaE] at this
  rw [← hmnat]
  exact this

/-- **The Euclidean growth `2 q_k ≤ q_{k+5}` for the record denominators (unconditional).** -/
theorem bestDenom_euclidean_growth (α : Fin 2 → ℝ) {k₀ : Fin 2} (hirr : Irrational (α k₀))
    (hr : RecordsContinue (deltaE α)) (k : ℕ) :
    2 * bestDenom (deltaE α) hr k ≤ bestDenom (deltaE α) hr (k + 5) := by
  have hint : 2 * (bestDenom (deltaE α) hr k : ℤ) ≤ (bestDenom (deltaE α) hr (k + 5) : ℤ) :=
    euclidean_growth_five α (fun k => (bestDenom (deltaE α) hr k : ℤ))
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

/-- **`g₂ ≤ 6` (Euclidean five-distance count, combinatorial, unconditional).** For any `α : Fin 2 →
ℝ`
with an irrational coordinate and `N ≥ 2`, the number of distinct values of the Euclidean
nearest-neighbour distance `gapVal (deltaE α) N q` is at most `6`. -/
theorem gap_count_euclidean (α : Fin 2 → ℝ) {k₀ : Fin 2} (hirr : Irrational (α k₀)) {N : ℕ}
    (hN : 2 ≤ N) :
    ((Finset.range (N + 1)).image (gapVal (deltaE α) N)).card ≤ 6 := by
  have hr := recordsContinue_deltaE α hirr
  have := chevallier_gap_count_le (deltaE α) hr 5 (bestDenom_euclidean_growth α hirr hr) hN
  simpa using this

end ThreeGap.EuclideanRecords
