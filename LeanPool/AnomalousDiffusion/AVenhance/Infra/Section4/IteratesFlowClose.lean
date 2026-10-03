/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowBounds

/-! # Iterates Flow Close

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance Infra.Construction

/-- The refresh-time estimate supplies the small factor, rather than the
uniform all-order seminorm bound. -/
theorem iterate_flowGrad_zero_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 2 ≤ m) {l : ℤ} {t : ℝ} (hne : I.hatXiML m l t ≠ 0)
    (x : Vec 2) (i j : Fin 2) :
    |(I.flowGrad hΦ m l t x - 1) i j| ≤
      40 * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
  let s := (l : ℝ) * tauPP β I.Λ m
  let r := t - s
  let y := constructionFlowInv hΦ (m - 1) (s + r) x s
  let A := constructionFlowJacobian hΦ (m - 1) r s y -
    ContinuousLinearMap.id ℝ (Vec 2)
  let scales := section2Scales_canonical I
  let data := appB2InverseFlowData_of_smoothPeriodicFlow hΦ scales
  have hind := section2_stream_induction scales data
  have hc := (section2_flow_close_from_previous scales data (m - 1) (by omega)
    (hind ((m - 1) - 1)) s r (iterate_hatXi_section2_window I (by omega) hne) y).1
  have hb : ‖basisVec i‖ ≤ (1 : ℝ) := by
    rw [pi_norm_le_iff_of_nonempty]
    intro k
    by_cases hk : k = i <;> simp [Homogenization.basisVec, hk]
  have hentry : |(I.flowGrad hΦ m l t x - 1) i j| ≤ ‖A‖ := by
    rw [iterate_flowGrad_entry_eq_composed I hΦ m l t x i j, ← Real.norm_eq_abs]
    change ‖A (basisVec i) j‖ ≤ ‖A‖
    exact (norm_le_pi_norm _ j).trans ((A.le_opNorm _).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (norm_nonneg A)))
  have ha := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hρ : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) := Real.rpow_nonneg
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _
  have ht := iterate_hatXi_time_window I (by omega) hne
  have hp := iterate_refresh_amplitude_bound I (by omega : 1 ≤ m)
  have hsize : 2 ^ 23 * |r| * a β I.Λ (m - 1) ≤
      (1 / 4) * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    calc
      2 ^ 23 * |r| * a β I.Λ (m - 1) =
          2 ^ 23 * (|r| * a β I.Λ (m - 1)) := by ring
      _ ≤ 2 ^ 23 * (tauPP β I.Λ m * a β I.Λ (m - 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht ha.le) (by positivity)
      _ ≤ 2 ^ 23 * ((2 : ℝ) ^ (-25 : ℤ) * epsilon β I.Λ (m - 1) ^ (2 * delta β)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by norm_num; ring
  exact (hentry.trans hc).trans (hsize.trans
    (mul_le_mul_of_nonneg_right (by norm_num : (1 / 4 : ℝ) ≤ 40) hρ))

end AVenhance.Infra.Section4
