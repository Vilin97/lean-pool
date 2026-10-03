/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorHGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse

/-! # The `S`-normalised `HTilde_m` gradient bound from the AMNR tensor estimate

Equations (16)-(18).  The tensor
hypothesis is the scale form of equation (5), stated for each `r₀ < Jcut β` separately:
`CA · S · (ε_m²/κ_m)/√ν · L² · (τ'_m)^{-r₀}` with `L = ε_{m-1}^{-1-γ/2}` and `ν = κ_{m-1}`,
and is the literal `hAmnrHess` premise of `hmr_spaceGrad_eLpNorm_le_of_pAmnr_qMNR`.  The
conclusion is the `hHgrad` input shape of the leading-error assembly:
`√κ_m √(spaceTimeGradNormSq ∇HTilde_m) ≤ CH ε_{m-1}^{4δ} S`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.LeftToShow

/-- `ε_{m-1}^δ ≤ 1/4` once `Λ ≥ 4^{1/δ}`. -/
theorem leh_epsilon_rpow_delta_le {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) {m : ℕ} (hm : 1 ≤ m)
    (hbig : (4 : ℝ) ^ (1 / delta β) ≤ (Λ : ℝ)) :
    epsilon β Λ m ^ delta β ≤ 1 / 4 := by
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  have hΛ0 : (0 : ℝ) < Λ := by
    have : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
    linarith
  have hε := epsilon_le_inv_Lambda hβ hβ' hΛ hm
  have hε0 : 0 ≤ epsilon β Λ m := (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le
  have h1 : epsilon β Λ m ^ delta β ≤ ((Λ : ℝ)⁻¹) ^ delta β :=
    Real.rpow_le_rpow hε0 hε hδ.le
  have h4 : (4 : ℝ) ≤ (Λ : ℝ) ^ delta β := by
    have := Real.rpow_le_rpow (by positivity) hbig hδ.le
    rwa [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4), one_div, inv_mul_cancel₀ hδ.ne',
      Real.rpow_one] at this
  rw [Real.inv_rpow hΛ0.le] at h1
  refine h1.trans ?_
  rw [one_div]
  exact inv_anti₀ (by norm_num) h4

/-- **Gradient bound** (16)-(18). -/
theorem relative_Hm_gradient (β C₀ CA : ℝ) (hCA : 0 ≤ CA) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∃ Λ₀ : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λ₀ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (T : ℝ → Vec 2 → ℝ) (S : ℝ), 0 ≤ S →
        (∀ r ∈ Finset.range (Jcut β), ∀ n ∈ Finset.range (Nstar β), ∀ i j k p : Fin 2,
          AEStronglyMeasurable
            (fun z : ℝ × Vec 2 => amnrSpatialDivergenceGradientTensor
              I hΦ m (I.kappaSeq κ M m) T n r z i j k p) (volume.restrict timeCube)) →
        (∀ r ∈ Finset.range (Jcut β), AEStronglyMeasurable
          (fun z : ℝ × Vec 2 =>
            spaceGrad (fun x => I.Hmr hΦ m (I.kappaSeq κ M m) T r z.1 x) z.2)
          (volume.restrict timeCube)) →
        (∀ r ∈ Finset.range (Jcut β), ∀ n ∈ Finset.range (Nstar β), ∀ i j k : Fin 2, ∀ t x,
          DifferentiableAt ℝ
            (fun y : Vec 2 => I.Amnr hΦ m (I.kappaSeq κ M m) n T r t y i j k) x) →
        (∀ r ∈ Finset.range (Jcut β), ∀ n ∈ Finset.range (Nstar β), ∀ i j k : Fin 2, ∀ t x,
          DifferentiableAt ℝ
            (fun y : Vec 2 => spaceGrad
              (fun x => I.Amnr hΦ m (I.kappaSeq κ M m) n T r t x i j k) y i) x) →
        (∀ r ∈ Finset.range (Jcut β), ∀ t x,
          DifferentiableAt ℝ (fun y : Vec 2 => I.Hmr hΦ m (I.kappaSeq κ M m) T r t y) x) →
        -- (L3, equation (5)), for every r₀ < Jcut β and n < Nstar β, the actual tensor
        (∀ r₀ ∈ Finset.range (Jcut β), ∀ n ∈ Finset.range (Nstar β),
          eLpNorm (amnrSpatialDivergenceGradientTensor I hΦ m (I.kappaSeq κ M m) T n r₀) 2
              (volume.restrict timeCube) ≤
            ENNReal.ofReal (CA * S * (epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m) /
              Real.sqrt (I.kappaSeq κ M (m - 1)) *
              (epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ 2 *
                ((tauP β I.Λ m)⁻¹) ^ r₀)) →
        Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (spaceTimeGradNormSq (fun s x =>
            spaceGrad (I.Hm hΦ m (I.kappaSeq κ M m) T s) x)) ≤
          CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * S := by
  obtain ⟨K, hK1, hK⟩ := left_to_show_scales β C₀
  obtain ⟨c, C, hc, hcC, hL⟩ := l_recurse β C₀
  obtain ⟨Λc, hcond⟩ := left_to_show_condition β C₀
  have hK0 : 0 ≤ K := by linarith
  have hC0 : 0 ≤ C := by linarith
  refine ⟨256 * Real.sqrt 2 * (Nstar β : ℝ) * (4 * Real.pi ^ 2 * max C₀ 0) * CA * K * C *
      (2 : ℝ) ^ (-28 : ℤ), by positivity, max Λc (4 ^ (1 / delta β)), ?_⟩
  intro I hz hx hh hΛ₀ Φ hΦ κ hκp M hM hperm m hm hmM T S hS hHess hGradMeas hD1 hD2 hHmrD
    hAmnr
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hΛ := I.two_pow_seven_le
  have hΛc : Λc ≤ (I.Λ : ℝ) := le_trans (le_max_left _ _) hΛ₀
  have hbig : (4 : ℝ) ^ (1 / delta β) ≤ (I.Λ : ℝ) := le_trans (le_max_right _ _) hΛ₀
  obtain ⟨hκ0, hκle, -, hX, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm hmM
  have hcm := hcond I hz hx hh hΛc κ hκp M hM hperm m hm hmM
  have hτ0 : 0 < tau β I.Λ m := Infra.Ingredients.tau_pos hβ hβ' hΛ
  have hratio : epsilon β I.Λ m ^ 2 / (I.kappaSeq κ M m * tau β I.Λ m) ≤ 1 := by
    rw [div_le_one (mul_pos hκ0 hτ0)]
    have : 0 ≤ I.kappaSeq κ M m * tau β I.Λ m := (mul_pos hκ0 hτ0).le
    linarith
  -- the time-scale ratio
  have hE4 := leh_epsilon_rpow_delta_le hβ hβ' hΛ (m := m - 1) (by omega) hbig
  have hτ'0 : 0 < tauP β I.Λ m := Infra.Cutoff.tauP_pos hβ hβ' hΛ
  have hτ : 8 * tau β I.Λ m / tauP β I.Λ m ≤ 1 / 2 := by
    have h := (Infra.Section4.time_ratio_bounds hβ hβ' hΛ (m := m) (by omega)).2
    rw [mul_div_assoc]
    nlinarith only [h, hE4]
  -- the interior upper bound for ν = κ_{m-1}
  have hν : I.kappaSeq κ M (m - 1) ≤
      C * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)) :=
    ((hL I hz hx hh κ hκp M hM hperm).1 (m - 1) (by omega) (by omega)).2
  have hat := (Infra.Section4.amplitude_tau_bounds hβ hβ' hΛ (m := m) (by omega)).2
  have hz' : I.Czeta ≤ max C₀ 0 := hz.trans (le_max_left _ _)
  exact hm_gradient_le_of_amnr_scales hCA hS hK0 hC0 I hz' hΦ hm T hκ0 hκle hratio hτ hX hν hat
    hHess hGradMeas hD1 hD2 hHmrD hAmnr

end AVenhance.Infra.Section5.RelativeError
