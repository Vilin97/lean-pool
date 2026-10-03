/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.LIdxConsequences

/-! Source consequences for the magnitudes of the time scales. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Ingredients

theorem TimeScaleBounds.epsilon_le_one {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    AVenhance.epsilon β Λ m ≤ 1 := by
  by_cases hm : m = 0
  · simp [AVenhance.epsilon, hm]
  · have hΛ1 : 1 ≤ (Λ : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 7) hΛ)
    have hq : 1 < AVenhance.q β := one_lt_q hβ hβ'
    have hexp : 0 < (AVenhance.q β) ^ m / (AVenhance.q β - 1) := by
      apply div_pos
      · exact pow_pos (by linarith) _
      · linarith
    have hpow : 1 ≤ (Λ : ℝ) ^ ((AVenhance.q β) ^ m /
        (AVenhance.q β - 1)) := by
      exact Real.one_le_rpow hΛ1 hexp.le
    have hceil : 1 ≤
        (⌈(Λ : ℝ) ^ ((AVenhance.q β) ^ m /
          (AVenhance.q β - 1))⌉₊ : ℝ) := by
      have hnat : 1 ≤ ⌈(Λ : ℝ) ^ ((AVenhance.q β) ^ m /
          (AVenhance.q β - 1))⌉₊ := by
        exact Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hpow)
      exact_mod_cast hnat
    simp only [AVenhance.epsilon, hm, ge_iff_le]
    exact inv_le_one_of_one_le₀ hceil

theorem TimeScaleBounds.rpow_ceil_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  constructor
  · exact_mod_cast Nat.le_ceil x
  · have hceil : (⌈x⌉₊ : ℝ) < x + 1 := by
      exact_mod_cast (Nat.ceil_lt_add_one (le_of_lt (lt_of_lt_of_le zero_lt_one hx)))
    linarith

theorem TimeScaleBounds.tauPP_rpow_bounds {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (_hm : 1 ≤ m) :
    (2 : ℝ) ^ (-26 : ℤ) *
        AVenhance.epsilon β Λ (m - 1) ^ (2 - β + 2 * AVenhance.delta β) ≤
      AVenhance.tauPP β Λ m ∧
    AVenhance.tauPP β Λ m ≤
      (2 : ℝ) ^ (-25 : ℤ) *
        AVenhance.epsilon β Λ (m - 1) ^ (2 - β + 2 * AVenhance.delta β) := by
  let e := AVenhance.epsilon β Λ (m - 1)
  let d := AVenhance.delta β
  have he : 0 < e := by
    dsimp [e]
    exact AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have he1 : e ≤ 1 := by
    dsimp [e]
    exact TimeScaleBounds.epsilon_le_one hβ hβ' hΛ
  have hd : 0 < d := by
    dsimp [d]
    exact delta_pos hβ hβ'
  have hexp : 0 < 2 - β + 2 * d := by
    have hdsmall := delta_le_one_sixteenth hβ hβ'
    nlinarith
  have hAeq : AVenhance.a β Λ (m - 1) / e ^ (2 * d) =
      e ^ (-(2 - β + 2 * d)) := by
    dsimp [e, d, AVenhance.a]
    rw [← Real.rpow_sub he]
    congr 1
    ring
  have hApos : 0 < AVenhance.a β Λ (m - 1) / e ^ (2 * d) := by
    rw [hAeq]
    exact Real.rpow_pos_of_pos he _
  have hAge : 1 ≤ AVenhance.a β Λ (m - 1) / e ^ (2 * d) := by
    rw [hAeq]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos he he1 (by linarith)
  let c :=
    (⌈AVenhance.a β Λ (m - 1) / e ^ (2 * d)⌉₊ : ℝ)
  have hc :
      AVenhance.a β Λ (m - 1) / e ^ (2 * d) ≤ c ∧
      c ≤ 2 * (AVenhance.a β Λ (m - 1) / e ^ (2 * d)) := by
    dsimp [c]
    exact TimeScaleBounds.rpow_ceil_bounds hAge
  have hcge1 : 1 ≤ c := hAge.trans hc.1
  have hceilpos : 0 < c := lt_of_lt_of_le zero_lt_one hcge1
  have hreciplo : (1 / (2 * (AVenhance.a β Λ (m - 1) / e ^ (2 * d)))) ≤ c⁻¹ := by
    rw [show 1 / (2 * (AVenhance.a β Λ (m - 1) / e ^ (2 * d))) =
      (2 * (AVenhance.a β Λ (m - 1) / e ^ (2 * d)))⁻¹ by ring]
    exact (inv_le_inv₀ (mul_pos (by norm_num) hApos) hceilpos).2 hc.2
  have hreciphi : c⁻¹ ≤
      (AVenhance.a β Λ (m - 1) / e ^ (2 * d))⁻¹ := by
    exact (inv_le_inv₀ hceilpos hApos).2 hc.1
  have hinvA :
      (AVenhance.a β Λ (m - 1) / e ^ (2 * d))⁻¹ =
        e ^ (2 - β + 2 * d) := by
    rw [hAeq, Real.rpow_neg (le_of_lt he), inv_inv]
  have hreciplo' :
      (1 / 2) * e ^ (2 - β + 2 * d) ≤ c⁻¹ := by
    calc
      (1 / 2) * e ^ (2 - β + 2 * d) =
          (2 * (AVenhance.a β Λ (m - 1) / e ^ (2 * d)))⁻¹ := by
        rw [← hinvA]
        field_simp
      _ ≤ c⁻¹ := by simpa [one_div] using hreciplo
  have hscale :
      AVenhance.tauPP β Λ m = (2 : ℝ) ^ (-25 : ℤ) * c⁻¹ := by
    simp [c, e, d, AVenhance.tauPP]
  constructor
  · rw [hscale]
    have hcst : (2 : ℝ) ^ (-26 : ℤ) ≤ (2 : ℝ) ^ (-25 : ℤ) / 2 := by norm_num
    have hp : 0 ≤ e ^ (2 - β + 2 * d) := by positivity
    calc
      (2 : ℝ) ^ (-26 : ℤ) * e ^ (2 - β + 2 * d) ≤
          ((2 : ℝ) ^ (-25 : ℤ) / 2) * e ^ (2 - β + 2 * d) :=
        mul_le_mul_of_nonneg_right hcst hp
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) * c⁻¹ := by
        have hh := mul_le_mul_of_nonneg_left hreciplo'
          (by positivity : 0 ≤ (2 : ℝ) ^ (-25 : ℤ))
        convert hh using 1
        ring
  · rw [hscale]
    have hp : 0 ≤ e ^ (2 - β + 2 * d) := by positivity
    have hreciphi' : c⁻¹ ≤ e ^ (2 - β + 2 * d) := by
      simpa [hinvA] using hreciphi
    exact mul_le_mul_of_nonneg_left hreciphi'
      (by positivity : 0 ≤ (2 : ℝ) ^ (-25 : ℤ))

/-- `e.taubounds` (1153-1168), corrected: the `τ''` lower
constant is `2⁻²⁶`; its upper constant is `2⁻²⁵`. -/
theorem tauPP_bounds {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (-26 : ℤ) *
        AVenhance.epsilon β Λ (m - 1) ^ (2 - β + 2 * AVenhance.delta β) ≤
      AVenhance.tauPP β Λ m ∧
    AVenhance.tauPP β Λ m ≤
      (2 : ℝ) ^ (-25 : ℤ) *
        AVenhance.epsilon β Λ (m - 1) ^ (2 - β + 2 * AVenhance.delta β) :=
  TimeScaleBounds.tauPP_rpow_bounds hβ hβ' hΛ hm

/-- `e.taubounds` (1153-1168): the stated `τ_m` bounds. -/
theorem tau_bounds {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (-33 : ℤ) *
        AVenhance.epsilon β Λ (m - 1) ^ (2 - β + 4 * AVenhance.delta β) ≤
      AVenhance.tau β Λ m ∧
    AVenhance.tau β Λ m ≤
      (2 : ℝ) ^ (-28 : ℤ) *
        AVenhance.epsilon β Λ (m - 1) ^ (2 - β + 4 * AVenhance.delta β) := by
  let e := AVenhance.epsilon β Λ (m - 1)
  let d := AVenhance.delta β
  let F := tauCellFactor β Λ m
  have he : 0 < e := by dsimp [e]; exact AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have he1 : e ≤ 1 := by dsimp [e]; exact TimeScaleBounds.epsilon_le_one hβ hβ' hΛ
  have hd : 0 < d := by dsimp [d]; exact delta_pos hβ hβ'
  have hx : 1 ≤ e ^ (-d) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos he he1 (by linarith)
  have hc : e ^ (-d) ≤
      (⌈e ^ (-d)⌉₊ : ℝ) ∧
      (⌈e ^ (-d)⌉₊ : ℝ) ≤ 2 * e ^ (-d) := TimeScaleBounds.rpow_ceil_bounds hx
  have hFlo : 4 * e ^ (-d) ≤ F := by
    dsimp [F, tauCellFactor]
    have hcast : e ^ (-d) ≤
        (⌈e ^ (-d)⌉₊ : ℝ) := hc.1
    linarith
  have hFhi : F ≤ 9 * e ^ (-d) := by
    dsimp [F, tauCellFactor]
    have hcast : (⌈e ^ (-d)⌉₊ : ℝ) ≤ 2 * e ^ (-d) := hc.2
    nlinarith [hx]
  have hFpos : 0 < F := by dsimp [F]; unfold tauCellFactor; positivity
  have hratio := tauPP_bounds hβ hβ' hΛ hm
  have hτ := tauPP_eq_cellFactor_sq_mul_tau (β := β) (Λ := Λ) hm
  have hτ' : AVenhance.tau β Λ m = AVenhance.tauPP β Λ m / F ^ 2 := by
    calc
      AVenhance.tau β Λ m = (F ^ 2 * AVenhance.tau β Λ m) / F ^ 2 := by
        field_simp [ne_of_gt hFpos]
      _ = AVenhance.tauPP β Λ m / F ^ 2 := by rw [← hτ]
  have hErel : e ^ (2 - β + 2 * d) =
      e ^ (2 - β + 4 * d) * (e ^ (-d)) ^ 2 := by
    calc
      e ^ (2 - β + 2 * d) =
          e ^ (2 - β + 4 * d + (-d) * 2) := by
        congr 1
        ring
      _ = e ^ (2 - β + 4 * d) * e ^ ((-d) * 2) := by
        rw [Real.rpow_add he]
      _ = e ^ (2 - β + 4 * d) * (e ^ (-d)) ^ 2 := by
        rw [Real.rpow_mul (le_of_lt he)]
        simp
  constructor
  · rw [hτ']
    have hF2 : F ^ 2 ≤ (9 * e ^ (-d)) ^ 2 := by
      exact pow_le_pow_left₀ (le_of_lt hFpos) hFhi 2
    have hF2' : F ^ 2 ≤ 81 * (e ^ (-d)) ^ 2 := by
      nlinarith [hF2, sq_nonneg (e ^ (-d))]
    have hconst : (2 : ℝ) ^ (-33 : ℤ) * 81 ≤ (2 : ℝ) ^ (-26 : ℤ) := by norm_num
    have hP : 0 ≤ e ^ (2 - β + 4 * d) := by positivity
    have hE : 0 ≤ (e ^ (-d)) ^ 2 := sq_nonneg _
    apply (le_div_iff₀ (pow_pos hFpos 2)).2
    calc
      (2 : ℝ) ^ (-33 : ℤ) * e ^ (2 - β + 4 * d) * F ^ 2 ≤
          (2 : ℝ) ^ (-33 : ℤ) * e ^ (2 - β + 4 * d) *
            (81 * (e ^ (-d)) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hF2' (by positivity)
      _ = ((2 : ℝ) ^ (-33 : ℤ) * 81) *
          (e ^ (2 - β + 4 * d) * (e ^ (-d)) ^ 2) := by ring
      _ ≤ (2 : ℝ) ^ (-26 : ℤ) * e ^ (2 - β + 2 * d) := by
        rw [← hErel]
        exact mul_le_mul_of_nonneg_right hconst (by positivity)
      _ ≤ AVenhance.tauPP β Λ m := hratio.1
  · rw [hτ']
    have hF2 : (4 * e ^ (-d)) ^ 2 ≤ F ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hFlo 2
    have hF2' : 16 * (e ^ (-d)) ^ 2 ≤ F ^ 2 := by
      nlinarith [hF2, sq_nonneg (e ^ (-d))]
    have hconst : (2 : ℝ) ^ (-25 : ℤ) ≤ 16 * (2 : ℝ) ^ (-28 : ℤ) := by norm_num
    have hP : 0 ≤ e ^ (2 - β + 4 * d) := by positivity
    have hE : 0 ≤ (e ^ (-d)) ^ 2 := sq_nonneg _
    apply (div_le_iff₀ (pow_pos hFpos 2)).2
    calc
      AVenhance.tauPP β Λ m ≤
          (2 : ℝ) ^ (-25 : ℤ) * e ^ (2 - β + 2 * d) := hratio.2
      _ = (2 : ℝ) ^ (-25 : ℤ) *
          (e ^ (2 - β + 4 * d) * (e ^ (-d)) ^ 2) := by rw [hErel]
      _ ≤ (2 : ℝ) ^ (-28 : ℤ) * e ^ (2 - β + 4 * d) * F ^ 2 := by
        calc
          (2 : ℝ) ^ (-25 : ℤ) *
              (e ^ (2 - β + 4 * d) * (e ^ (-d)) ^ 2) ≤
              (16 * (2 : ℝ) ^ (-28 : ℤ)) *
                (e ^ (2 - β + 4 * d) * (e ^ (-d)) ^ 2) :=
              mul_le_mul_of_nonneg_right hconst (by positivity)
          _ ≤ (2 : ℝ) ^ (-28 : ℤ) * e ^ (2 - β + 4 * d) * F ^ 2 := by
            calc
              (16 * (2 : ℝ) ^ (-28 : ℤ)) *
                  (e ^ (2 - β + 4 * d) * (e ^ (-d)) ^ 2) =
                  (2 : ℝ) ^ (-28 : ℤ) * e ^ (2 - β + 4 * d) *
                    (16 * (e ^ (-d)) ^ 2) := by ring
              _ ≤ (2 : ℝ) ^ (-28 : ℤ) * e ^ (2 - β + 4 * d) * F ^ 2 := by
                exact mul_le_mul_of_nonneg_left hF2'
                  (by positivity : 0 ≤ (2 : ℝ) ^ (-28 : ℤ) *
                    e ^ (2 - β + 4 * d))

end AVenhance.Infra.Ingredients
