/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.BaseCutoffs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.DerivativeBounds

/-! The two cutoffs at the large time scale. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Cutoff

/-- Cell cutoff with unit transition margin and a specified period ratio. -/
def hatXiProfile (ratio x : ℝ) : ℝ := cellCutoff step ratio 1 x

/-- Cell cutoff with a specified period and transition margin. -/
def hatXiCutoff (period margin t : ℝ) : ℝ := cellCutoff step period margin t

/-- Product profile for the enlarged time cutoff in normalized coordinates. -/
def hatZetaProfile (ratio x : ℝ) : ℝ :=
  step (x + ratio / 2 - 1) * step (ratio / 2 - 1 - x)

/-- Enlarged time cutoff with a specified period and transition margin. -/
def hatZetaCutoff (period margin t : ℝ) : ℝ :=
  step ((t + period / 2 - margin) / margin) *
    step ((period / 2 - margin - t) / margin)

theorem hatXiProfile_contDiff (ratio : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (hatXiProfile ratio) := by
  unfold hatXiProfile cellCutoff
  fun_prop

theorem hatZetaProfile_contDiff (ratio : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (hatZetaProfile ratio) := by
  unfold hatZetaProfile
  fun_prop

theorem hatXiCutoff_contDiff (period margin : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (hatXiCutoff period margin) := by
  unfold hatXiCutoff cellCutoff
  fun_prop

theorem hatZetaCutoff_contDiff (period margin : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (hatZetaCutoff period margin) := by
  unfold hatZetaCutoff
  fun_prop

theorem hatXiCutoff_nonneg (period margin t : ℝ) : 0 ≤ hatXiCutoff period margin t := by
  unfold hatXiCutoff cellCutoff
  exact mul_nonneg (step_nonneg _) (step_nonneg _)

theorem hatXiCutoff_le_one (period margin t : ℝ) : hatXiCutoff period margin t ≤ 1 := by
  unfold hatXiCutoff cellCutoff
  have h₁ := step_le_one ((t + period / 2 + margin) / (2 * margin))
  have h₂₀ := step_nonneg ((period / 2 + margin - t) / (2 * margin))
  have h₂ := step_le_one ((period / 2 + margin - t) / (2 * margin))
  calc
    _ ≤ 1 * step ((period / 2 + margin - t) / (2 * margin)) :=
      mul_le_mul_of_nonneg_right h₁ h₂₀
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left h₂ (by norm_num)
    _ = 1 := by norm_num

theorem hatXiCutoff_one_on_core {period margin t : ℝ} (hm : 0 < margin)
    (ht₁ : -period / 2 + margin ≤ t) (ht₂ : t ≤ period / 2 - margin) :
    hatXiCutoff period margin t = 1 := by
  unfold hatXiCutoff
  exact cellCutoff_one_on_core hm (fun y hy => step_one_of_one_le hy) ht₁ ht₂

theorem hatXiCutoff_zero_of_le {period margin t : ℝ} (hm : 0 < margin)
    (ht : t ≤ -(period / 2 + margin)) : hatXiCutoff period margin t = 0 :=
  cellCutoff_zero_of_le hm (fun _ hy => step_zero_of_nonpos hy) ht

theorem hatXiCutoff_zero_of_ge {period margin t : ℝ} (hm : 0 < margin)
    (ht : period / 2 + margin ≤ t) : hatXiCutoff period margin t = 0 :=
  cellCutoff_zero_of_ge hm (fun _ hy => step_zero_of_nonpos hy) ht

theorem hatZetaCutoff_nonneg (period margin t : ℝ) : 0 ≤ hatZetaCutoff period margin t := by
  unfold hatZetaCutoff
  exact mul_nonneg (step_nonneg _) (step_nonneg _)

theorem hatZetaCutoff_le_one (period margin t : ℝ) : hatZetaCutoff period margin t ≤ 1 := by
  unfold hatZetaCutoff
  have h₁ := step_le_one ((t + period / 2 - margin) / margin)
  have h₂₀ := step_nonneg ((period / 2 - margin - t) / margin)
  have h₂ := step_le_one ((period / 2 - margin - t) / margin)
  calc
    _ ≤ 1 * step ((period / 2 - margin - t) / margin) :=
      mul_le_mul_of_nonneg_right h₁ h₂₀
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left h₂ (by norm_num)
    _ = 1 := by norm_num

theorem hatZetaCutoff_one_on_core {period margin t : ℝ} (hm : 0 < margin)
    (ht₁ : -period / 2 + 2 * margin ≤ t)
    (ht₂ : t ≤ period / 2 - 2 * margin) : hatZetaCutoff period margin t = 1 := by
  unfold hatZetaCutoff
  rw [step_one_of_one_le, step_one_of_one_le]
  · norm_num
  · rw [le_div_iff₀ hm]
    linarith
  · rw [le_div_iff₀ hm]
    linarith

theorem hatZetaCutoff_zero_of_le {period margin t : ℝ} (hm : 0 < margin)
    (ht : t ≤ -period / 2 + margin) : hatZetaCutoff period margin t = 0 := by
  unfold hatZetaCutoff
  have hz : step ((t + period / 2 - margin) / margin) = 0 :=
    step_zero_of_nonpos (by rw [div_le_iff₀ hm]; linarith)
  rw [hz, zero_mul]

theorem hatZetaCutoff_zero_of_ge {period margin t : ℝ} (hm : 0 < margin)
    (ht : period / 2 - margin ≤ t) : hatZetaCutoff period margin t = 0 := by
  unfold hatZetaCutoff
  have hz : step ((period / 2 - margin - t) / margin) = 0 :=
    step_zero_of_nonpos (by rw [div_le_iff₀ hm]; linarith)
  rw [hz, mul_zero]

theorem hatXiCutoff_eq_profile {period margin t : ℝ} (hm : margin ≠ 0) :
    hatXiCutoff period margin t = hatXiProfile (period / margin) (t / margin) := by
  unfold hatXiCutoff hatXiProfile cellCutoff
  congr 2 <;> field_simp [hm]

theorem hatZetaCutoff_eq_profile {period margin t : ℝ} (hm : margin ≠ 0) :
    hatZetaCutoff period margin t = hatZetaProfile (period / margin) (t / margin) := by
  unfold hatZetaCutoff hatZetaProfile
  congr 2 <;> field_simp [hm]

theorem hatXiProfile_deriv_bound {N : ℕ} {M : ℝ}
    (hM : 1 ≤ M)
    (hstep : ∀ j : ℕ, j ≤ N → ∀ x : ℝ, |iteratedDeriv j step x| ≤ M)
    (ratio : ℝ) :
    ∀ j : ℕ, j ≤ N → ∀ x : ℝ,
      |iteratedDeriv j (hatXiProfile ratio) x| ≤ 2 ^ N * M ^ 2 := by
  have hshape : hatXiProfile ratio = fun x : ℝ =>
      step (ratio / 4 + 1 / 2 + (1 / 2) * x) *
        step (ratio / 4 + 1 / 2 - (1 / 2) * x) := by
    funext x
    unfold hatXiProfile cellCutoff
    congr 2 <;> ring
  intro j hj x
  rw [hshape]
  exact affine_product_iteratedDeriv_uniform_bound hM hstep
    (a := ratio / 4 + 1 / 2) (b := ratio / 4 + 1 / 2) (c := 1 / 2)
    (by norm_num) hj

theorem hatZetaProfile_deriv_bound {N : ℕ} {M : ℝ}
    (hM : 1 ≤ M)
    (hstep : ∀ j : ℕ, j ≤ N → ∀ x : ℝ, |iteratedDeriv j step x| ≤ M)
    (ratio : ℝ) :
    ∀ j : ℕ, j ≤ N → ∀ x : ℝ,
      |iteratedDeriv j (hatZetaProfile ratio) x| ≤ 2 ^ N * M ^ 2 := by
  have hshape : hatZetaProfile ratio = fun x : ℝ =>
      step (ratio / 2 - 1 + x) * step (ratio / 2 - 1 - x) := by
    funext x
    unfold hatZetaProfile
    congr 2
    ring
  intro j hj x
  rw [hshape]
  simpa [mul_one] using affine_product_iteratedDeriv_uniform_bound hM hstep
    (a := ratio / 2 - 1) (b := ratio / 2 - 1) (c := 1)
    (by norm_num) hj

theorem hatXi_partition {period margin : ℝ} (hp : 0 < period) (hm : 0 < margin)
    (hmp : 2 * margin ≤ period) (t : ℝ) :
    ∑' l : ℤ, AVenhance.shiftCutoff (hatXiCutoff period margin) ((l : ℝ) * period) t = 1 := by
  simpa [AVenhance.shiftCutoff, hatXiCutoff] using
    (cellCutoff_lattice_partition (s := step) (period := period) (margin := margin)
      (t := t) hp hm hmp (fun x hx => step_zero_of_nonpos hx)
      (fun x hx => step_one_of_one_le hx) step_one_sub)

theorem hatXi_shift_ge {period margin : ℝ} (hm : 0 < margin)
    (_hspace : 2 * margin ≤ period) (l : ℤ) (t : ℝ) :
    AVenhance.indIcc ((l - 1 / 2) * period + margin)
      ((l + 1 / 2) * period - margin) t ≤
      AVenhance.shiftCutoff (hatXiCutoff period margin) ((l : ℝ) * period) t := by
  by_cases ht : t ∈ Set.Icc ((l - 1 / 2) * period + margin)
      ((l + 1 / 2) * period - margin)
  · have hlo : -period / 2 + margin ≤ t - (l : ℝ) * period := by
      have h := ht.1
      nlinarith
    have hhi : t - (l : ℝ) * period ≤ period / 2 - margin := by
      have h := ht.2
      nlinarith
    have hind : AVenhance.indIcc ((l - 1 / 2) * period + margin)
        ((l + 1 / 2) * period - margin) t = 1 := by
      unfold AVenhance.indIcc
      rw [Set.indicator_of_mem ht]
    rw [hind, AVenhance.shiftCutoff]
    change 1 ≤ hatXiCutoff period margin (t - (l : ℝ) * period)
    rw [hatXiCutoff_one_on_core hm hlo hhi]
  · have hind : AVenhance.indIcc ((l - 1 / 2) * period + margin)
        ((l + 1 / 2) * period - margin) t = 0 := by
      unfold AVenhance.indIcc
      rw [Set.indicator_of_notMem ht]
    rw [hind, AVenhance.shiftCutoff]
    exact hatXiCutoff_nonneg period margin (t - (l : ℝ) * period)

theorem hatXi_shift_le {period margin : ℝ} (hm : 0 < margin)
    (l : ℤ) (t : ℝ) :
    AVenhance.shiftCutoff (hatXiCutoff period margin) ((l : ℝ) * period) t ≤
      AVenhance.indIcc ((l - 1 / 2) * period - margin)
        ((l + 1 / 2) * period + margin) t := by
  by_cases ht : t ∈ Set.Icc ((l - 1 / 2) * period - margin)
      ((l + 1 / 2) * period + margin)
  · have hind : AVenhance.indIcc ((l - 1 / 2) * period - margin)
        ((l + 1 / 2) * period + margin) t = 1 := by
      unfold AVenhance.indIcc
      rw [Set.indicator_of_mem ht]
    rw [AVenhance.shiftCutoff, hind]
    exact hatXiCutoff_le_one period margin (t - (l : ℝ) * period)
  · have hout : t < (l - 1 / 2) * period - margin ∨
        (l + 1 / 2) * period + margin < t := by
      have hmem : ¬ ((l - 1 / 2) * period - margin ≤ t ∧
          t ≤ (l + 1 / 2) * period + margin) := by
        simpa [Set.mem_Icc] using ht
      rcases not_and_or.mp hmem with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (lt_of_not_ge h)
    rcases hout with hleft | hright
    · have hz : hatXiCutoff period margin (t - (l : ℝ) * period) = 0 := by
        apply hatXiCutoff_zero_of_le hm
        nlinarith
      have hind : AVenhance.indIcc ((l - 1 / 2) * period - margin)
          ((l + 1 / 2) * period + margin) t = 0 := by
        unfold AVenhance.indIcc
        rw [Set.indicator_of_notMem ht]
      rw [AVenhance.shiftCutoff, hind, hz]
    · have hz : hatXiCutoff period margin (t - (l : ℝ) * period) = 0 := by
        apply hatXiCutoff_zero_of_ge hm
        nlinarith
      have hind : AVenhance.indIcc ((l - 1 / 2) * period - margin)
          ((l + 1 / 2) * period + margin) t = 0 := by
        unfold AVenhance.indIcc
        rw [Set.indicator_of_notMem ht]
      rw [AVenhance.shiftCutoff, hind, hz]

theorem hatZeta_shift_ge {period margin : ℝ} (hm : 0 < margin)
    (_hspace : 4 * margin ≤ period) (l : ℤ) (t : ℝ) :
    AVenhance.indIcc ((l - 1 / 2) * period + 2 * margin)
      ((l + 1 / 2) * period - 2 * margin) t ≤
      AVenhance.shiftCutoff (hatZetaCutoff period margin) ((l : ℝ) * period) t := by
  by_cases ht : t ∈ Set.Icc ((l - 1 / 2) * period + 2 * margin)
      ((l + 1 / 2) * period - 2 * margin)
  · have hlo : -period / 2 + 2 * margin ≤ t - (l : ℝ) * period := by
      have h := ht.1
      nlinarith
    have hhi : t - (l : ℝ) * period ≤ period / 2 - 2 * margin := by
      have h := ht.2
      nlinarith
    have hind : AVenhance.indIcc ((l - 1 / 2) * period + 2 * margin)
        ((l + 1 / 2) * period - 2 * margin) t = 1 := by
      unfold AVenhance.indIcc
      rw [Set.indicator_of_mem ht]
    rw [hind, AVenhance.shiftCutoff]
    change 1 ≤ hatZetaCutoff period margin (t - (l : ℝ) * period)
    rw [hatZetaCutoff_one_on_core hm hlo hhi]
  · have hind : AVenhance.indIcc ((l - 1 / 2) * period + 2 * margin)
        ((l + 1 / 2) * period - 2 * margin) t = 0 := by
      unfold AVenhance.indIcc
      rw [Set.indicator_of_notMem ht]
    rw [hind, AVenhance.shiftCutoff]
    exact hatZetaCutoff_nonneg period margin (t - (l : ℝ) * period)

theorem hatZeta_shift_le {period margin : ℝ} (hm : 0 < margin)
    (l : ℤ) (t : ℝ) :
    AVenhance.shiftCutoff (hatZetaCutoff period margin) ((l : ℝ) * period) t ≤
      AVenhance.indIcc ((l - 1 / 2) * period + margin)
        ((l + 1 / 2) * period - margin) t := by
  by_cases ht : t ∈ Set.Icc ((l - 1 / 2) * period + margin)
      ((l + 1 / 2) * period - margin)
  · have hind : AVenhance.indIcc ((l - 1 / 2) * period + margin)
        ((l + 1 / 2) * period - margin) t = 1 := by
      unfold AVenhance.indIcc
      rw [Set.indicator_of_mem ht]
    rw [AVenhance.shiftCutoff, hind]
    exact hatZetaCutoff_le_one period margin (t - (l : ℝ) * period)
  · have hout : t < (l - 1 / 2) * period + margin ∨
        (l + 1 / 2) * period - margin < t := by
      have hmem : ¬ ((l - 1 / 2) * period + margin ≤ t ∧
          t ≤ (l + 1 / 2) * period - margin) := by
        simpa [Set.mem_Icc] using ht
      rcases not_and_or.mp hmem with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (lt_of_not_ge h)
    rcases hout with hleft | hright
    · have hz : hatZetaCutoff period margin (t - (l : ℝ) * period) = 0 := by
        apply hatZetaCutoff_zero_of_le hm
        nlinarith
      have hind : AVenhance.indIcc ((l - 1 / 2) * period + margin)
          ((l + 1 / 2) * period - margin) t = 0 := by
        unfold AVenhance.indIcc
        rw [Set.indicator_of_notMem ht]
      rw [AVenhance.shiftCutoff, hind, hz]
    · have hz : hatZetaCutoff period margin (t - (l : ℝ) * period) = 0 := by
        apply hatZetaCutoff_zero_of_ge hm
        nlinarith
      have hind : AVenhance.indIcc ((l - 1 / 2) * period + margin)
          ((l + 1 / 2) * period - margin) t = 0 := by
        unfold AVenhance.indIcc
        rw [Set.indicator_of_notMem ht]
      rw [AVenhance.shiftCutoff, hind, hz]

theorem hatXi_shift_normalized {period margin : ℝ} (hm : 0 < margin) (l : ℤ) :
    AVenhance.shiftCutoff (hatXiCutoff period margin) ((l : ℝ) * period) =
      fun t => hatXiProfile (period / margin) (t / margin - (l : ℝ) * (period / margin)) := by
  funext t
  rw [AVenhance.shiftCutoff,
    hatXiCutoff_eq_profile (period := period) (margin := margin)
      (t := t - (l : ℝ) * period) (ne_of_gt hm)]
  congr 1
  field_simp [ne_of_gt hm]

theorem hatZeta_shift_normalized {period margin : ℝ} (hm : 0 < margin) (l : ℤ) :
    AVenhance.shiftCutoff (hatZetaCutoff period margin) ((l : ℝ) * period) =
      fun t => hatZetaProfile (period / margin) (t / margin - (l : ℝ) * (period / margin)) := by
  funext t
  rw [AVenhance.shiftCutoff,
    hatZetaCutoff_eq_profile (period := period) (margin := margin)
      (t := t - (l : ℝ) * period) (ne_of_gt hm)]
  congr 1
  field_simp [ne_of_gt hm]

theorem hatXi_scaled_deriv_bound {period margin : ℝ} {N : ℕ} {M : ℝ}
    (hm : 0 < margin) (hM : 1 ≤ M)
    (hstep : ∀ j : ℕ, j ≤ N → ∀ x : ℝ, |iteratedDeriv j step x| ≤ M)
    (_hspace : 2 * margin ≤ period) (l : ℤ) {j : ℕ} (hj : j ≤ N) (t : ℝ) :
    margin ^ j * |iteratedDeriv j
      (AVenhance.shiftCutoff (hatXiCutoff period margin) ((l : ℝ) * period)) t| ≤
        2 ^ N * M ^ 2 := by
  rw [hatXi_shift_normalized hm l]
  exact scaled_translate_iteratedDeriv_bound (hatXiProfile_contDiff (period / margin))
    (hatXiProfile_deriv_bound hM hstep (period / margin)) hm hj

theorem hatZeta_scaled_deriv_bound {period margin : ℝ} {N : ℕ} {M : ℝ}
    (hm : 0 < margin) (hM : 1 ≤ M)
    (hstep : ∀ j : ℕ, j ≤ N → ∀ x : ℝ, |iteratedDeriv j step x| ≤ M)
    (l : ℤ) {j : ℕ} (hj : j ≤ N) (t : ℝ) :
    margin ^ j * |iteratedDeriv j
      (AVenhance.shiftCutoff (hatZetaCutoff period margin) ((l : ℝ) * period)) t| ≤
        2 ^ N * M ^ 2 := by
  rw [hatZeta_shift_normalized hm l]
  exact scaled_translate_iteratedDeriv_bound (hatZetaProfile_contDiff (period / margin))
    (hatZetaProfile_deriv_bound hM hstep (period / margin)) hm hj

end AVenhance.Infra.Cutoff
