/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualForBigBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46IteratesRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Matrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar

/-! # Contracts already produced

Each theorem below proves an `Integration.*Contract` of `Integration/OpenInputs.lean` exactly, in
    the
producer form `∃ C₁, OnA7Instances β C₀ C₁ (fun … => <Name>Contract …)` (no constants needed). -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

/-- Positivity facts available on the big-bound premise block. -/
theorem onA7_basic {β : ℝ} (I : Ingredients β) {κ R : ℝ} {M m : ℕ}
    (hκ : κ ∈ permittedInterval β I.Λ M) (hR : 0 < R) (hm : mTheta0 β I.Λ R ≤ m) :
    2 ≤ m ∧ 0 < I.kappaSeq κ M m := by
  have hstar : 2 ≤ mTheta0 β I.Λ R :=
    (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1
  have he : 0 < epsilon β I.Λ M :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hκpos : 0 < κ :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos he _)) (Set.mem_Icc.mp hκ).1
  exact ⟨hstar.trans hm, LeftToShow.kappaSeq_pos I hκpos M m⟩

/-- `ResidualContract` (big-bound estimate `residual`), from the `frozenResidualBigBoundResidual`.
-/
theorem residual_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      ResidualContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  exact frozenResidualBigBoundResidual I hΦ m (by omega) _ _ hκm θ₀ θprev hθprev T hT

/-- `R46FluxSmoothContract` (big-bound estimate `R46_flux_smooth`), from the
    `tIterate_r46Flux_regular`. -/
theorem r46FluxSmooth_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      R46FluxSmoothContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨hm2, -⟩ := onA7_basic I hperm hR hm
  exact (tIterate_r46Flux_regular I hΦ (by omega) _ hT hθprev le_rfl ht.1).1

/-- `R46FluxPeriodicContract` (big-bound estimate `R46_flux_periodic`), from the
    `tIterate_r46Flux_regular`. -/
theorem r46FluxPeriodic_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      R46FluxPeriodicContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨hm2, -⟩ := onA7_basic I hperm hR hm
  exact (tIterate_r46Flux_regular I hΦ (by omega) _ hT hθprev le_rfl ht.1).2

end AVenhance.Infra.Section5.Contracts
