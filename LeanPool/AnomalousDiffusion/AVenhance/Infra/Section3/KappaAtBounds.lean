/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KhomSymmetry
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KappaAt

/-! Elementary positivity and monotonicity facts for the diffusivity chain. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace AVenhance.Infra.Section3

open AVenhance

/-- The averaged scalar diffusivity is at least the molecular diffusivity. -/
theorem khomScalar_ge_input {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) :
    κ ≤ I.KhomScalar κ m := by
  have hcont : ∀ i j : Fin 2, Continuous (fun t => I.flux κ m t i j) := by
    intro i j
    exact flux_entry_time_continuous I hm κ i j
  have hscalar := khom_eq_scalar_of_flux_continuous I hm κ hκ hcont
  have hint : IntervalIntegrable (fun t => I.flux κ m t 0 0) volume 0 1 :=
    (hcont 0 0).intervalIntegrable (μ := volume) 0 1
  have hge : κ ≤ I.Khom κ m 0 0 := by
    change κ ≤ ∫ t in (0 : ℝ)..1, I.flux κ m t 0 0
    have hmono : (∫ _ in (0 : ℝ)..1, κ) ≤
        ∫ t in (0 : ℝ)..1, I.flux κ m t 0 0 := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        intervalIntegrable_const hint
      intro t _
      exact flux_diag_ge_kappa I hm κ t 0
    simpa using hmono
  have hdiag : I.Khom κ m 0 0 = I.KhomScalar κ m := by
    rw [hscalar.1]
    simp [Matrix.smul_apply]
  rw [← hdiag]
  exact hge

/-- The averaged scalar diffusivity also has the upper bound inherited from the
pointwise memory relaxation estimate. -/
theorem khomScalar_le_input_add_amplitude {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) :
    I.KhomScalar κ m ≤ κ + a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ) := by
  have hcont : ∀ i j : Fin 2, Continuous (fun t => I.flux κ m t i j) := by
    intro i j
    exact flux_entry_time_continuous I hm κ i j
  have hscalar := khom_eq_scalar_of_flux_continuous I hm κ hκ hcont
  have hint : IntervalIntegrable (fun t => I.flux κ m t 0 0) volume 0 1 :=
    (hcont 0 0).intervalIntegrable (μ := volume) 0 1
  have hcap := flux_diag_le_kappa_add_amplitude I hm κ hκ
  have hmono :
      (∫ t in (0 : ℝ)..1, I.flux κ m t 0 0) ≤
        ∫ _ in (0 : ℝ)..1,
          κ + a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hint intervalIntegrable_const
    intro t _
    exact hcap t 0
  have hdiag : I.Khom κ m 0 0 = I.KhomScalar κ m := by
    rw [hscalar.1]
    simp [Matrix.smul_apply]
  rw [← hdiag]
  change (∫ t in (0 : ℝ)..1, I.flux κ m t 0 0) ≤ _
  simpa using hmono

/-- Every value in the recurrence is positive when its terminal value is. -/
theorem kappaAt_pos {β : ℝ} (I : Ingredients β) {κ : ℝ}
    (hκ : 0 < κ) (m d : ℕ) : 0 < I.kappaAt κ m d := by
  induction d generalizing m with
  | zero => simpa [Ingredients.kappaAt] using hκ
  | succ d ih =>
      rw [Ingredients.kappaAt]
      have hnext : 0 < I.kappaAt κ (m + 1) d := ih (m + 1)
      have hge := khomScalar_ge_input I (m := m + 1) (by omega)
        (I.kappaAt κ (m + 1) d) hnext
      exact lt_of_lt_of_le hnext hge

end AVenhance.Infra.Section3
