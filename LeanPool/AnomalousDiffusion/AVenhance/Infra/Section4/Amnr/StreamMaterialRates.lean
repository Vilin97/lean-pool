/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMaterial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.DerivativeBounds

/-! Quantitative material estimates for the actual transported stream summands. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Time Leibniz estimates with one common derivative radius. -/
theorem amnr_iteratedDeriv_product_abs_le {f g : ℝ → ℝ} {N n : ℕ}
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) (hn : n ≤ N)
    {F G R : ℝ} (hF : 0 ≤ F) (_hG : 0 ≤ G) (hR : 0 ≤ R)
    (hfb : ∀ j, j ≤ N → ∀ t, |iteratedDeriv j f t| ≤ F * R ^ j)
    (hgb : ∀ j, j ≤ N → ∀ t, |iteratedDeriv j g t| ≤ G * R ^ j) (t : ℝ) :
    |iteratedDeriv n (f * g) t| ≤ (2 : ℝ) ^ n * F * G * R ^ n := by
  rw [iteratedDeriv_mul (hf.of_le (by exact_mod_cast hn)).contDiffAt
    (hg.of_le (by exact_mod_cast hn)).contDiffAt]
  calc
    |∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * iteratedDeriv j f t *
        iteratedDeriv (n - j) g t| ≤
        ∑ j ∈ Finset.range (n + 1), |(n.choose j : ℝ) * iteratedDeriv j f t *
          iteratedDeriv (n - j) g t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (F * G * R ^ n) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by simp only [Finset.mem_range] at hj; omega
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        (n.choose j : ℝ) * |iteratedDeriv j f t| * |iteratedDeriv (n - j) g t| ≤
            (n.choose j : ℝ) * (F * R ^ j) * (G * R ^ (n - j)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (hfb j (hjn.trans hn) t) (Nat.cast_nonneg _)
          · exact hgb (n - j) (by omega) t
          · exact abs_nonneg _
          · positivity
        _ = _ := by
          rw [show R ^ n = R ^ j * R ^ (n - j) by
            rw [← pow_add, Nat.add_sub_of_le hjn]]
          ring
    _ = _ := by
      rw [← Finset.sum_mul]
      have hc : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) = (2 : ℝ) ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [hc]
      ring

/-- The fine time-cutoff rate dominates the large-cutoff rate. -/
theorem amnr_inverse_tauP_le_inverse_tau {β : ℝ} (I : AVenhance.Ingredients β) {m : ℕ} (hm : 1 ≤
    m) :
    (AVenhance.tauP β I.Λ m)⁻¹ ≤ (AVenhance.tau β I.Λ m)⁻¹ := by
  have ht := AVenhance.Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m)
  have hf := (time_cell_factor_bounds I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m)).1
  have he := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have he1 := AVenhance.Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m - 1)
  have hd := AVenhance.Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hp : 1 ≤ AVenhance.epsilon β I.Λ (m - 1) ^ (-AVenhance.delta β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos he he1 (by linarith)
  have hfactor : 1 ≤ AVenhance.Infra.Ingredients.tauCellFactor β I.Λ m := by linarith
  apply inv_anti₀ ht
  rw [AVenhance.Infra.Ingredients.tauP_eq_cellFactor_mul_tau hm]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor ht.le

/-- Exact amplitude bound of the prescribed shear profile. -/
theorem amnr_psi_abs_le {β : ℝ} (I : AVenhance.Ingredients β) (m : ℕ) (k : ℤ)
    (x : Vec 2) : |AVenhance.psi β I.Λ m k x| ≤
      AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ 2 := by
  have ha := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m)
  have hp : |AVenhance.psi0 k ((AVenhance.epsilon β I.Λ m)⁻¹ • x)| ≤ 1 := by
    unfold AVenhance.psi0
    split_ifs <;> first | exact Real.abs_sin_le_one _ | simp
  unfold AVenhance.psi
  rw [abs_mul, abs_of_nonneg (mul_nonneg ha.le (sq_nonneg _))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (mul_nonneg ha.le (sq_nonneg _))

/-- Actual large-cutoff derivatives in the fine time radius used by the
stream-recursion material estimates. -/
theorem amnr_hatZeta_derivative_abs_le {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) {j : ℕ} (hj : j ≤ AVenhance.Nstar β) (t : ℝ) :
    |iteratedDeriv j (I.hatZetaML m l) t| ≤ I.Chat * (AVenhance.tau β I.Λ m)⁻¹ ^ j := by
  have ht := AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m)
  have hh := I.hatZeta_deriv_le m hm l j hj t
  change AVenhance.tauP β I.Λ m ^ j * |iteratedDeriv j (I.hatZetaML m l) t| ≤ I.Chat at hh
  have hh' : |iteratedDeriv j (I.hatZetaML m l) t| ≤
      I.Chat * (AVenhance.tauP β I.Λ m)⁻¹ ^ j := by
    rw [inv_pow, ← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos ht j)).mpr (by simpa only [mul_comm] using hh)
  refine hh'.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by linarith [I.one_le_Chat])
  exact pow_le_pow_left₀ (inv_nonneg.mpr ht.le) (amnr_inverse_tauP_le_inverse_tau I hm) j

/-- Fine-cutoff derivatives follow from the literal profile derivative data. -/
theorem amnr_zeta_derivative_abs_le {β : ℝ} (I : AVenhance.Ingredients β)
    (m : ℕ) (k : ℤ) {j : ℕ} (hj : j ≤ AVenhance.Nstar β) (t : ℝ) :
    |iteratedDeriv j (I.zetaMK m k) t| ≤ I.Czeta * (AVenhance.tau β I.Λ m)⁻¹ ^ j := by
  have ht := AVenhance.Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hh := AVenhance.Infra.Cutoff.scaled_translate_iteratedDeriv_bound I.zeta_smooth
    I.zeta_deriv_le ht (shift := (k : ℝ)) (x := t) hj
  have heq : (fun t : ℝ => I.zeta (t / AVenhance.tau β I.Λ m - (k : ℝ))) = I.zetaMK m k := by
    funext t
    unfold AVenhance.Ingredients.zetaMK AVenhance.scaledCutoff
    congr 1
    rw [sub_div, mul_div_cancel_right₀ _ ht.ne']
  rw [heq] at hh
  rw [inv_pow, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos ht j)).mpr (by simpa only [mul_comm] using hh)

end AVenhance.Infra.Section4
