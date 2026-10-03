/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeLeadingBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.AssemblyBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.FlowForErgodicBound

/-! Amplitude-generic leading-energy estimates on the actual datum and T iterates.
The quadratic error has amplitude S squared; the base consumes only integrated gradients. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5.AnalyticBridge AVenhance.Infra.Section5.LeftToShow

/-- `e.left.to.show` (additive), conditional only on the three `T_{m-1}` source estimates:
`e.Tm.reg.upgrade` (n = 0 `L²_tH¹` part `hT0`; all orders `L∞_tL²_x` part `hTall`) and
`e.barf.cascade` (n = 0, ℓ = 1, `hDt`), with one constant `A ≥ 2^14`. -/
theorem relative_leading_energy_of_T_bounds (β C₀ A : ℝ) (hA : 2 ^ (14 : ℕ) ≤ A) :
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
        |I.kappaSeq κ M m *
              spaceTimeGradNormSq (leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β))) -
            I.kappaSeq κ M (m - 1) *
              spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x)| ≤
          C * epsilon β I.Λ (m - 1) ^ (2 * delta β) * S ^ 2 := by
  have hA1 : (1 : ℝ) ≤ A := le_trans (by norm_num) hA
  obtain ⟨C, hC⟩ := relative_leading_energy_of_bounds β C₀ A hA1
  refine ⟨C, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm m hm hmM S hS θ₀ θprev T hTit hT0 hDt hTall
  exact hC I hz hx hh hΛ Φ hΦ κ hκ M hM hperm m hm hmM S hS θ₀ θprev T hTit hT0 hDt hTall
    (fun t ht k hk hξ => flowForErgodicBound_of_stream hΦ A hA m hm t ht k hk hξ)

end AVenhance.Infra.Section5.RelativeError
