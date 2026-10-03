/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeLeading
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Assembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.Bridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.Monotone
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy

/-! Amplitude-generic leading-energy estimates on the actual datum and T iterates.
The quadratic error has amplitude S squared; the base consumes only integrated gradients. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5.AnalyticBridge AVenhance.Infra.Section5.LeftToShow

theorem RelativeLeadingBounds.amplitude_le {e γ A' A'' θ : ℝ} (he : 0 < e) (hA : A' ≤ A'') (hθ : 0
    ≤ θ) :
    A' * (e ^ (1 + γ / 2)) ^ (-6 : ℤ) * θ ≤ A'' * e ^ (-(6 + 3 * γ)) * θ := by
  have hpow : (e ^ (1 + γ / 2)) ^ (-6 : ℤ) = e ^ (-(6 + 3 * γ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul he.le]
    congr 1
    push_cast
    ring
  rw [hpow]
  have hnn : 0 ≤ e ^ (-(6 + 3 * γ)) := (Real.rpow_pos_of_pos he _).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hnn) hθ

/-- `e.left.to.show` (additive), conditional only on source estimates for `T_{m-1}` and the flows:
`e.Tm.reg.upgrade` (n = 0 L²_tH¹ part `hT0`, and all orders L∞_tL²_x `hTall`), `e.barf.cascade`
(n = 0, ℓ = 1, `hDt`) and `e.flow.for.ergodic` on `supp ξ_{m,k}` (`hFlow`), all with one constant
`A ≥ 1` (they weaken as `A` grows). -/
theorem relative_leading_energy_of_bounds (β C₀ A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (S : ℝ), 0 ≤ S → ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
        Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x)) ≤
          A * S →
        Real.sqrt (spaceTimeGradNormSq (materialGrad (streamVel (Φ (m - 1))) (T (Nstar β)))) ≤
          A * epsilon β I.Λ (m - 1) ^ (3 * delta β) * (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
            S * (tauP β I.Λ m)⁻¹ →
        PositiveTemperatureJets A (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) S (T (Nstar β)) →
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ k : ℤ, Odd k → I.xiMK m k t ≠ 0 →
          FlowForErgodicBound A (epsilon β I.Λ (m - 1)) (I.xFlow hΦ m (lIdx β I.Λ m k) t)) →
        |I.kappaSeq κ M m *
              spaceTimeGradNormSq (leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β))) -
            I.kappaSeq κ M (m - 1) *
              spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x)| ≤
          C * epsilon β I.Λ (m - 1) ^ (2 * delta β) * S ^ 2 := by
  by_cases hb : 1 < β ∧ β < 4 / 3
  swap
  · exact ⟨0, fun I => absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb⟩
  obtain ⟨A', hA'1, hbr⟩ := relative_hasCoordinateAnalyticL1Bounds_of_bounds A hA
  set A'' := max A A' with hA''
  have hA''pos : 0 < A'' := lt_of_lt_of_le (by linarith) (le_max_left A A')
  have hγ : 0 ≤ gamma β := (Infra.Ingredients.gamma_pos hb.1 hb.2).le
  obtain ⟨C, hC⟩ := relative_left_to_show_conditional β C₀ A'' (6 + 3 * gamma β) hA''pos (by
      linarith)
  refine ⟨C, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm m hm hmM S hS θ₀ θprev T hTit hT0 hDt hTall hFlow
  have hθ : 0 ≤ S ^ 2 := sq_nonneg S
  have hsq : 0 ≤ S := hS
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hT0' : Real.sqrt (I.kappaSeq κ M (m - 1)) *
      Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x)) ≤
      A'' * S :=
    hT0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsq)
  have hτ : 0 < tauP β I.Λ m := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hX0 : 0 ≤ epsilon β I.Λ (m - 1) ^ (3 * delta β) *
      (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ * S * (tauP β I.Λ m)⁻¹ := by
    have := (Real.rpow_pos_of_pos he (3 * delta β)).le
    have := inv_nonneg.2 (Real.sqrt_nonneg (I.kappaSeq κ M (m - 1)))
    have := inv_nonneg.2 hτ.le
    positivity
  have hDt' : Real.sqrt (spaceTimeGradNormSq
      (materialGrad (streamVel (Φ (m - 1))) (T (Nstar β)))) ≤
      A'' * epsilon β I.Λ (m - 1) ^ (3 * delta β) * (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
        S * (tauP β I.Λ m)⁻¹ := by
    refine hDt.trans ?_
    have h := mul_le_mul_of_nonneg_right (le_max_left A A') hX0
    calc A * epsilon β I.Λ (m - 1) ^ (3 * delta β) * (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
          S * (tauP β I.Λ m)⁻¹ =
        A * (epsilon β I.Λ (m - 1) ^ (3 * delta β) * (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
          S * (tauP β I.Λ m)⁻¹) := by ring
      _ ≤ A'' * (epsilon β I.Λ (m - 1) ^ (3 * delta β) * (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
          S * (tauP β I.Λ m)⁻¹) := h
      _ = _ := by ring
  -- regularity of `T_{m-1}`
  have hN : 1 ≤ Nstar β := by
    have := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  have hTsol := hTit.2 (Nstar β) hN le_rfl
  set ρ := epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos he _
  have hρe : ρ ≤ epsilon β I.Λ (m - 1) := by
    have h := Real.rpow_le_rpow_of_exponent_ge he he1 (show (1 : ℝ) ≤ 1 + gamma β / 2 by linarith)
    simpa [hρ] using h
  have hAn : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ k : ℤ, Odd k → I.xiMK m k t ≠ 0 → ∀ i j : Fin 2,
      Infra.Ergodic.HasCoordinateAnalyticL1Bounds
        (fun y => ((spaceGrad (T (Nstar β) t) (I.xFlow hΦ m (lIdx β I.Λ m k) t y) i *
          spaceGrad (T (Nstar β) t) (I.xFlow hΦ m (lIdx β I.Λ m k) t y) j : ℝ) : ℂ))
        (A'' * epsilon β I.Λ (m - 1) ^ (-(6 + 3 * gamma β)) * S ^ 2)
        (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) / A'') := by
    intro t ht k hk hξ i j
    have hXs : ContDiff ℝ (⊤ : ℕ∞) (I.xFlow hΦ m (lIdx β I.Λ m k) t) :=
      (xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t).contDiff_toFun
    have hTs : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t) :=
      Infra.Classical.classicalSmooth_slice_nonneg hTsol.1 ht.1.le
    have hTp : IsZ2Periodic (T (Nstar β) t) := hTsol.2.1 t ht.1.le
    have hb := hbr S (T (Nstar β)) ρ (epsilon β I.Λ (m - 1)) (I.xFlow hΦ m (lIdx β I.Λ m k) t)
      hS hρpos hρe he1 hTall (hFlow t ht k hk hξ) hXs t ht hTs hTp i j
    refine hasCoordinateAnalyticL1Bounds_mono hb (RelativeLeadingBounds.amplitude_le he
        (le_max_right A A') hθ)
      (by positivity) (div_pos hρpos hA''pos) ?_
    exact div_le_div_of_nonneg_left hρpos.le (by linarith) (le_max_right A A')
  exact hC I hz hx hh hΛ Φ hΦ κ hκ M hM hperm m hm hmM S θ₀ θprev T hTit
    (by simpa only [Real.sqrt_sq hS] using hT0')
    (by simpa only [Real.sqrt_sq hS] using hDt') hAn

end AVenhance.Infra.Section5.RelativeError
