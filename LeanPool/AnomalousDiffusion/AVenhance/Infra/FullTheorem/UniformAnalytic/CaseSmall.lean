/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.TailHolder
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LaterStart

/-! # Case `M ≤ m₀ − 1` of the analytic case of `r.LeBron.2`

Lemma U directly for `θ`, with `κ ≥ ½ ε_M^{β-γ} ≥ ½ ε_{m₀-1}^{β-γ}`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- The exponent `e = max(P, β - γ)/2` of the scale `ε_{m₀-1}^{-e}`. -/
def unifE (β : ℝ) : ℝ := max (lebronP β) (β - gamma β) / 2

theorem unifE_nonneg {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : 0 ≤ unifE β := by
  have h := gamma_lt_beta hβ hβ'
  have : 0 ≤ β - gamma β := by linarith
  unfold unifE
  have := le_max_right (lebronP β) (β - gamma β)
  linarith

theorem case_small {β CU Bφ : ℝ} (hU : LemmaUWith CU) (hCU : 0 < CU) (hBφ : 0 ≤ Bφ)
    {I : Ingredients β} (hΛs : (2 : ℝ) ^ (1 / (β - gamma β)) ≤ (I.Λ : ℝ))
    {φ : ℝ → Vec 2 → ℝ}
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (streamVel φ t))
    (hdiv : IsDivFree (streamVel φ))
    (hb_bdd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖streamVel φ t x‖ ≤ Bφ)
    {κ : ℝ} {M : ℕ} (hM : 1 ≤ M) (hκM : κ ∈ permittedInterval β I.Λ M) {R : ℝ}
    {θ₀ : Vec 2 → ℝ} (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀)
    {θ : ℝ → Vec 2 → ℝ} (hθ : IsWeakSolution (streamVel φ) κ θ₀ θ)
    (hMm : M ≤ mTheta0 β I.Λ R - 1) :
    IsHolderTimeL2 (1 / 4)
      (CU * (1 + Bφ) * (1 / Real.sqrt (1 / 2)) *
        epsilon β I.Λ (mTheta0 β I.Λ R - 1) ^ (-unifE β) *
        Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀))) θ := by
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  obtain ⟨Dθ, hDθ⟩ := hθ
  obtain ⟨hκlo, hκ1⟩ := permitted_bounds hβ1 hβ2 hΛ7 hΛs hM hκM
  set E := epsilon β I.Λ (mTheta0 β I.Λ R - 1) with hEdef
  have hE : 0 < E := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hE1 : E ≤ 1 := Infra.Construction.epsilon_le_one hβ1 hβ2 hΛ7
  have hγβ := gamma_lt_beta hβ1 hβ2
  have hεM : E ≤ epsilon β I.Λ M :=
    Infra.Section5.RelativeError.epsilon_antitone hβ1 hβ2 hΛ7 hMm
  have hκlo' : (1 / 2) * E ^ (β - gamma β) ≤ κ := by
    refine le_trans ?_ hκlo
    have := Real.rpow_le_rpow hE.le hεM (by linarith : 0 ≤ β - gamma β)
    linarith
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκlo'
  set N := Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  intro s hs t ht
  have hu := hU (streamVel φ) hb_meas hb_per hdiv Bφ hBφ hb_bdd κ hκ0 hκ1 θ₀
    (fun x => spaceGrad θ₀ x)
    (Infra.Section5.RelativeError.isPeriodicH1With_of_contDiff
      (hθ₀.of_le (by exact_mod_cast le_top)) hper) θ Dθ hDθ s hs t ht
  have hκ' := one_div_sqrt_le (c := 1 / 2) (by norm_num) hE (P := β - gamma β) hκlo'
  have hexp : E ^ (-((β - gamma β) / 2)) ≤ E ^ (-unifE β) := by
    refine Real.rpow_le_rpow_of_exponent_ge hE hE1 ?_
    have : (β - gamma β) / 2 ≤ unifE β := by
      unfold unifE
      have := le_max_right (lebronP β) (β - gamma β)
      linarith
    linarith
  have hh4 : 0 ≤ |t - s| ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (abs_nonneg _) _
  refine hu.trans ?_
  calc CU * (1 + Bφ) / Real.sqrt κ * |t - s| ^ ((1 : ℝ) / 4) * N
      = CU * (1 + Bφ) * (1 / Real.sqrt κ) * N * |t - s| ^ ((1 : ℝ) / 4) := by ring
    _ ≤ CU * (1 + Bφ) * ((1 / Real.sqrt (1 / 2)) * E ^ (-unifE β)) * N *
          |t - s| ^ ((1 : ℝ) / 4) := by
        have : 1 / Real.sqrt κ ≤ (1 / Real.sqrt (1 / 2)) * E ^ (-unifE β) :=
          hκ'.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
        gcongr
    _ = _ := by ring

end AVenhance.Infra.FullTheorem
