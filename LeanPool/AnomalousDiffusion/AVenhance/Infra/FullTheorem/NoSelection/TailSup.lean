/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.TailHolder

/-! # Sup-in-time bound of the tail `θ − θ_M` in terms of `‖θ₀‖_{L²}`

`tail_sup`: for a weak solution `θ` of the limit drift `streamVel φ` and the classical solution
`θ_M` of `streamVel (Φ M)`, both with diffusivity `κ ≥ ½ ε_M^{β-γ}` and the same datum,
`‖θ(t) − θ_M(t)‖ ≤ 2 C_t (1+A)^β ε_M^{a} ‖θ₀‖`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSel

open AVenhance AVenhance.Infra.FullTheorem

theorem tail_sup {β Ct Bφ : ℝ} (hCt : 0 ≤ Ct) {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {φ : ℝ → Vec 2 → ℝ}
    (htail : ∀ (M : ℕ) (t : ℝ) (x : Vec 2),
      |φ t x - Φ M t x| ≤ Ct * epsilon β I.Λ (M + 1) ^ β)
    (hφ_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hφ_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (φ t))
    (hφ_diff : ∀ t ∈ Set.Icc (0 : ℝ) 1, Differentiable ℝ (φ t))
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (streamVel φ t))
    (hdiv : IsDivFree (streamVel φ))
    (hb_bdd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖streamVel φ t x‖ ≤ Bφ)
    {κ : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hκlo : (1 / 2) * epsilon β I.Λ M ^ (β - gamma β) ≤ κ)
    {θ₀ : Vec 2 → ℝ} (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀)
    {θ : ℝ → Vec 2 → ℝ} (hθ : IsWeakSolution (streamVel φ) κ θ₀ θ)
    {θM : ℝ → Vec 2 → ℝ}
    (hθM : IsClassicalSol (streamVel (Φ M)) κ (fun _ _ => 0) θ₀ θM) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (l2NormSq (fun x => θ t x - θM t x)) ≤
      (2 * Ct * (1 + Infra.Ingredients.supergeoConstant β) ^ β * epsilon β I.Λ M ^ tailExp β) *
        Real.sqrt (l2NormSq θ₀) := by
  intro t ht
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  obtain ⟨Dθ, hDθ⟩ := hθ
  set E := epsilon β I.Λ M with hEdef
  have hE : 0 < E := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκlo
  have hγ := Infra.Ingredients.gamma_pos hβ1 hβ2
  have hγβ := gamma_lt_beta hβ1 hβ2
  have hA := Infra.Section5.RelativeError.supergeoConstant_nonneg' hβ1 hβ2
  have h1 := Contracts.forcedEnergySup_contract hb_meas ⟨Bφ, hb_bdd⟩ hb_per hdiv hφ_meas hφ_per
    hφ_diff (fun t _ x => rfl) (streamSeq_isAdmissible hΦ M) hκ0
    (hθ₀) hper hθM hDθ (η := Ct * epsilon β I.Λ (M + 1) ^ β)
    (fun t _ x => htail M t x) t ht
  have h2 := classical_sqrt_energy_le hΦ M hκ0 hθ₀ hθM
  have hη0 : 0 ≤ Ct * epsilon β I.Λ (M + 1) ^ β :=
    mul_nonneg hCt (Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7).le _)
  have hratio := tail_ratio_le (Ct := Ct) (A := Infra.Ingredients.supergeoConstant β)
    (E' := epsilon β I.Λ (M + 1)) (q := q β) (β := β) (s := β - gamma β) hE
    (Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7).le
    (Infra.Section5.RelativeError.epsilon_succ_le hβ1 hβ2 hΛ7 hM) hA hCt (by linarith) hκlo
  have h3 : 0 ≤ Ct * epsilon β I.Λ (M + 1) ^ β / κ := div_nonneg hη0 hκ0.le
  calc _ ≤ _ := h1
    _ ≤ (Ct * epsilon β I.Λ (M + 1) ^ β / κ) * Real.sqrt (l2NormSq θ₀) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        have := hratio
        unfold tailExp
        exact this

end AVenhance.Infra.FullTheorem.NoSel
