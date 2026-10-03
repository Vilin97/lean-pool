/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Ingredients

/-! Numerical relations among the §2.1 parameters. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Ingredients

/-- `e.q.def.0` (986-989): the definition simplifies to
`q = β / (4(β - 1))`. -/
theorem q_eq_beta_div_four_sub_one {β : ℝ} (hβ : 1 < β) :
    AVenhance.q β = β / (4 * (β - 1)) := by
  unfold AVenhance.q
  field_simp [ne_of_gt (sub_pos.mpr hβ)]
  ring

/-- `e.q.def` (999-1001): `q > 1` on the β range. -/
theorem one_lt_q {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    1 < AVenhance.q β := by
  rw [q_eq_beta_div_four_sub_one hβ]
  rw [lt_div_iff₀ (by positivity : 0 < 4 * (β - 1))]
  nlinarith

/-- `e.delta` (1008): an algebraically simplified expression for δ. -/
theorem delta_eq_q_fraction {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    AVenhance.delta β =
      (AVenhance.q β - 1) ^ 2 /
        (4 * (AVenhance.q β + 1) * (4 * AVenhance.q β - 1)) := by
  let r : ℝ := AVenhance.q β
  have hr : 1 < r := by exact one_lt_q hβ hβ'
  have hden : 4 * r - 1 ≠ 0 := by linarith
  have hb : β = 4 * r / (4 * r - 1) := by
    rw [show r = AVenhance.q β by rfl, q_eq_beta_div_four_sub_one hβ]
    field_simp [ne_of_gt (sub_pos.mpr hβ)]
    ring
  calc
    AVenhance.delta β =
        (1 / 4) * (r - 1) * (1 - ((2 * r + 1) / (2 * r + 2)) * β) := by
      simp [r, AVenhance.delta]
    _ = (1 / 4) * (r - 1) *
        (1 - ((2 * r + 1) / (2 * r + 2)) * (4 * r / (4 * r - 1))) := by
      rw [hb]
    _ = (r - 1) ^ 2 / (4 * (r + 1) * (4 * r - 1)) := by
      have hden' : 2 * r + 2 ≠ 0 := by linarith
      field_simp [hden, hden']
      ring

/-- `e.delta` (1008): the chosen δ is positive. -/
theorem delta_pos {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 < AVenhance.delta β := by
  rw [delta_eq_q_fraction hβ hβ']
  have hq := one_lt_q hβ hβ'
  have hqp : 0 < AVenhance.q β + 1 := by linarith
  have h4q : 0 < 4 * AVenhance.q β - 1 := by linarith
  have hden : 0 < 4 * (AVenhance.q β + 1) * (4 * AVenhance.q β - 1) :=
    mul_pos (mul_pos (by norm_num) hqp) h4q
  exact div_pos (sq_pos_of_pos (sub_pos.mpr hq)) hden

/-- `e.delta` (1004-1009): `δ ≤ 1/16` throughout the allowed β range. -/
theorem delta_le_one_sixteenth {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    AVenhance.delta β ≤ 1 / 16 := by
  rw [delta_eq_q_fraction hβ hβ']
  have hq := one_lt_q hβ hβ'
  have hqp : 0 < AVenhance.q β + 1 := by linarith
  have h4q : 0 < 4 * AVenhance.q β - 1 := by linarith
  have hden : 0 < 4 * (AVenhance.q β + 1) * (4 * AVenhance.q β - 1) :=
    mul_pos (mul_pos (by norm_num) hqp) h4q
  apply (div_le_iff₀ hden).2
  nlinarith [hq]

/-- `e.gamma` (1025): γ is positive on the β range. -/
theorem gamma_pos {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 < AVenhance.gamma β := by
  unfold AVenhance.gamma
  have hq := one_lt_q hβ hβ'
  positivity

/-- `e.delta` and `e.gamma` (1008, 1025): `γ ≥ 4δ`. -/
theorem four_delta_le_gamma {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    4 * AVenhance.delta β ≤ AVenhance.gamma β := by
  rw [delta_eq_q_fraction hβ hβ']
  unfold AVenhance.gamma
  have hq := one_lt_q hβ hβ'
  have hbase : AVenhance.q β - 1 ≤ β * (4 * AVenhance.q β - 1) := by
    nlinarith [hβ, hq]
  have hmul := mul_le_mul_of_nonneg_left hbase (sub_nonneg.mpr hq.le)
  have hqp : 0 < AVenhance.q β + 1 := by linarith
  have h4q : 0 < 4 * AVenhance.q β - 1 := by linarith
  have hden : 0 < (AVenhance.q β + 1) * (4 * AVenhance.q β - 1) :=
    mul_pos hqp h4q
  rw [show 4 * ((AVenhance.q β - 1) ^ 2 /
      (4 * (AVenhance.q β + 1) * (4 * AVenhance.q β - 1))) =
      (AVenhance.q β - 1) ^ 2 /
        ((AVenhance.q β + 1) * (4 * AVenhance.q β - 1)) by
    field_simp [ne_of_gt hden]]
  apply (div_le_iff₀ hden).2
  calc
    (AVenhance.q β - 1) ^ 2 ≤
        (AVenhance.q β - 1) * (β * (4 * AVenhance.q β - 1)) := by
      simpa [pow_two] using hmul
    _ = ((AVenhance.q β - 1) * β / (AVenhance.q β + 1)) *
        ((AVenhance.q β + 1) * (4 * AVenhance.q β - 1)) := by
      field_simp [ne_of_gt hqp, ne_of_gt h4q]

/-- The three correction terms of `N_*` are nonnegative. -/
theorem Nstar_corrections_nonneg {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 ≤ 8 + 4 * (AVenhance.q β - 1) *
        (β + (AVenhance.q β - 1) * β / (AVenhance.q β + 1)) / AVenhance.delta β ∧
      0 ≤ 8 + 128 * AVenhance.q β ^ 2 / (AVenhance.q β - 1) ∧
      0 ≤ 8 + 128 * AVenhance.q β ^ 2 * (AVenhance.q β - 1) := by
  have hq := one_lt_q hβ hβ'
  have hd := delta_pos hβ hβ'
  have hq1 : 0 ≤ AVenhance.q β - 1 := by linarith
  have hqp : 0 < AVenhance.q β + 1 := by linarith
  have hb : 0 ≤ β := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have : 0 ≤ 4 * (AVenhance.q β - 1) *
        (β + (AVenhance.q β - 1) * β / (AVenhance.q β + 1)) / AVenhance.delta β := by
      apply div_nonneg _ hd.le
      apply mul_nonneg (mul_nonneg (by norm_num) hq1)
      exact add_nonneg hb (div_nonneg (mul_nonneg hq1 hb) hqp.le)
    linarith
  · have : 0 ≤ 128 * AVenhance.q β ^ 2 / (AVenhance.q β - 1) :=
      div_nonneg (by positivity) hq1
    linarith
  · have : 0 ≤ 128 * AVenhance.q β ^ 2 * (AVenhance.q β - 1) :=
      mul_nonneg (by positivity) hq1
    linarith

/-- The real number whose ceiling is `N_*`. -/
theorem Nstar_eq_ceil (β : ℝ) :
    AVenhance.Nstar β =
      ⌈1 / (AVenhance.delta β) ^ 2 + 500 / AVenhance.delta β
        + (8 + 4 * (AVenhance.q β - 1) *
            (β + (AVenhance.q β - 1) * β / (AVenhance.q β + 1)) / AVenhance.delta β)
        + (8 + 128 * AVenhance.q β ^ 2 / (AVenhance.q β - 1))
        + (8 + 128 * AVenhance.q β ^ 2 * (AVenhance.q β - 1))⌉₊ := rfl

/-- `e.N` (1018): `N_*` dominates its source defining quantity `1/δ² + 500/δ`. -/
theorem Nstar_ge_defining_real {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    1 / (AVenhance.delta β) ^ 2 + 500 / AVenhance.delta β ≤
      (AVenhance.Nstar β : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := Nstar_corrections_nonneg hβ hβ'
  rw [Nstar_eq_ceil]
  exact le_trans (by linarith) (Nat.le_ceil _)

/-- Correction: `N_* ≥ 8 + 4(q-1)(β+γ)/δ` (the requirement used at line 7850). -/
theorem Nstar_ge_requirement {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    8 + 4 * (AVenhance.q β - 1) *
        (β + AVenhance.gamma β) / AVenhance.delta β ≤ (AVenhance.Nstar β : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := Nstar_corrections_nonneg hβ hβ'
  have hd := delta_pos hβ hβ'
  have hdef : 0 ≤ 1 / (AVenhance.delta β) ^ 2 + 500 / AVenhance.delta β := by positivity
  have hγ : AVenhance.gamma β = (AVenhance.q β - 1) * β / (AVenhance.q β + 1) := by
    unfold AVenhance.gamma; ring
  rw [Nstar_eq_ceil, hγ]
  exact le_trans (by linarith) (Nat.le_ceil _)

/-- Correction: `N_* ≥ 8 + 128q²/(q-1)` (line 7850). -/
theorem Nstar_ge_eight_add_div {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    8 + 128 * AVenhance.q β ^ 2 / (AVenhance.q β - 1) ≤ (AVenhance.Nstar β : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := Nstar_corrections_nonneg hβ hβ'
  have hd := delta_pos hβ hβ'
  have hdef : 0 ≤ 1 / (AVenhance.delta β) ^ 2 + 500 / AVenhance.delta β := by positivity
  rw [Nstar_eq_ceil]
  exact le_trans (by linarith) (Nat.le_ceil _)

/-- Correction: `N_* ≥ 8 + 128q²(q-1)` (line 7883). -/
theorem Nstar_ge_eight_add_mul {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    8 + 128 * AVenhance.q β ^ 2 * (AVenhance.q β - 1) ≤ (AVenhance.Nstar β : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := Nstar_corrections_nonneg hβ hβ'
  have hd := delta_pos hβ hβ'
  have hdef : 0 ≤ 1 / (AVenhance.delta β) ^ 2 + 500 / AVenhance.delta β := by positivity
  rw [Nstar_eq_ceil]
  exact le_trans (by linarith) (Nat.le_ceil _)

/-- `e.N` (1018) and `e.delta` (1008): the integer satisfies `N_* ≥ 256`. -/
theorem Nstar_ge_256 {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    256 ≤ AVenhance.Nstar β := by
  have hdpos := delta_pos hβ hβ'
  have hdle := delta_le_one_sixteenth hβ hβ'
  have hx : (255 : ℝ) < 1 / (AVenhance.delta β) ^ 2 +
      500 / AVenhance.delta β := by
    have hδsq : AVenhance.delta β ^ 2 ≤ (1 / 16) ^ 2 := by
      exact pow_le_pow_left₀ (le_of_lt hdpos) hdle 2
    have hδsqpos : 0 < AVenhance.delta β ^ 2 := sq_pos_of_pos hdpos
    have hinv : 256 ≤ 1 / (AVenhance.delta β) ^ 2 := by
      apply (le_div_iff₀ hδsqpos).2
      nlinarith [hδsq]
    have hterm : 0 < 500 / AVenhance.delta β := by positivity
    linarith
  have hceil : (255 : ℝ) < AVenhance.Nstar β :=
    lt_of_lt_of_le hx (Nstar_ge_defining_real hβ hβ')
  have hceil : 255 < AVenhance.Nstar β := by exact_mod_cast hceil
  omega

end AVenhance.Infra.Ingredients
