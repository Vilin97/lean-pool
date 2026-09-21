/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ExponentCompetition
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleSplit

/-! # Bad Scale Component Bounds Top -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# The crude top bad-scale component

In the top complementary range, the selected-scale inequality bounds `n` by a
deterministic logarithmic offset.  Since this branch also has `q ≤ n`, it is
empty above the corresponding deterministic threshold.
-/

noncomputable section

variable {Ω : Type*}

/-- The selected bad-pair scale is bounded by the logarithmic offset plus the
positive part of the exponent correction.  This deterministic cutoff estimate
is loss-free; it is kept with the crude-top branch rather than with the old
kernel bounds. -/
theorem selectedBadPairScale_cast_le_logOffset
    {K a t α : ℝ} (ha : 0 < a) {q m n : ℕ} :
    let x : ℝ := α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
    (selectedBadPairScale K a t α q m n : ℝ) ≤
      L + max (x / a) 0 + 1 := by
  intro x L
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hden_pos : 0 < a * Real.log (3 : ℝ) := mul_pos ha hlog3_pos
  have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) := by
    exact Real.log_nonneg (le_max_right (2 * K) 1)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (inv_nonneg.mpr hden_pos.le) hlog_nonneg
  have harg_eq :
      (a * Real.log 3)⁻¹ *
          (Real.log (max (2 * K) 1) + x * Real.log 3) =
        L + x / a := by
    dsimp [L]
    field_simp [ha.ne', hlog3_pos.ne']
  have hceil :=
    natCeil_le_add_max_zero_add_one (L := L) (y := x / a) hL_nonneg
  change
    (Nat.ceil
      ((a * Real.log 3)⁻¹ *
        (Real.log (max (2 * K) 1) + x * Real.log 3)) : ℝ) ≤
      L + max (x / a) 0 + 1
  rw [harg_eq]
  exact hceil

theorem crudeTopBadScaleEvent_eq_empty_of_large
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    (ha : 0 < a) (hα_nonneg : 0 ≤ α) (hαt : α < t) (hαa : α < a)
    (hq_large :
      let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
      L + 1 < (1 - α / a) * (q : ℝ)) :
    crudeTopBadScaleEvent H K a t α q = ∅ := by
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  have hlarge : L + 1 < (1 - α / a) * (q : ℝ) := by
    simpa [L] using hq_large
  have hα_div_lt_one : α / a < 1 := by
    have hdiv := div_lt_div_of_pos_right hαa ha
    simpa [div_self (ne_of_gt ha)] using hdiv
  have hbuffer_nonneg : 0 ≤ 1 - α / a := by linarith
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨m, n, hqn, hnot, hpair⟩
    rcases hpair with ⟨hnm, _hqm, _hbad⟩
    have hnℓ : n ≤ selectedBadPairScale K a t α q m n :=
      le_of_not_gt hnot
    have hceil :
        (selectedBadPairScale K a t α q m n : ℝ) ≤
          L +
            max
              ((α * ((m - q : ℕ) : ℝ) -
                  t * ((m - n : ℕ) : ℝ)) / a) 0 + 1 := by
      simpa [L] using
        selectedBadPairScale_cast_le_logOffset
          (K := K) (a := a) (t := t) (α := α)
          (q := q) (m := m) (n := n) ha
    have hn_bound :
        (1 - α / a) * (n : ℝ) ≤ L + 1 := by
      simpa [L] using
        scale_bound_of_not_high_q_le_n
          (a := a) (t := t) (α := α) (L := L)
          (q := q) (m := m) (n := n)
          (ℓ := selectedBadPairScale K a t α q m n)
          ha hα_nonneg hαt hαa
          (by simpa [L] using hceil) hnℓ hqn (le_of_lt hnm)
    have hq_le_n : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqn
    have hq_bound :
        (1 - α / a) * (q : ℝ) ≤ L + 1 :=
      (mul_le_mul_of_nonneg_left hq_le_n hbuffer_nonneg).trans hn_bound
    linarith
  · intro hω
    cases hω

variable [MeasurableSpace Ω]

theorem measureReal_crudeTopBadScaleEvent_eq_zero_of_large
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    (ha : 0 < a) (hα_nonneg : 0 ≤ α) (hαt : α < t) (hαa : α < a)
    (hq_large :
      let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
      L + 1 < (1 - α / a) * (q : ℝ)) :
    μ.real (crudeTopBadScaleEvent H K a t α q) = 0 := by
  rw [crudeTopBadScaleEvent_eq_empty_of_large
    (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
    ha hα_nonneg hαt hαa hq_large]
  simp [Measure.real]

end

end Section57
end Ch05
end Book
end Homogenization
