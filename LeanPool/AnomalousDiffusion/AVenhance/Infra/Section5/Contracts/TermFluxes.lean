/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxesSlice

/-! # Flux contracts of the divergence-form terms

Producers, in the exact form `∃ C₁, OnA7Instances β C₀ C₁ (… <Name>Contract …)`, of the
smoothness and `ℤ²`-periodicity contracts of the `twistie3`, `normie1` and `normie2` fluxes.  At a
fixed time `t ∈ (0,1)` the `ξ`-sums are finite, the diffusion matrix, `∇T - G_l`, `ΧTilde ∇G_l` are
smooth and periodic, and `∇HTilde_m(t)` is smooth and periodic for `t > 0`. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

/-- `Twistie3FluxSmoothContract` (big-bound estimate `twistie3_flux_smooth`). -/
theorem twistie3FluxSmooth_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      Twistie3FluxSmoothContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨hm2, -⟩ := onA7_basic I hperm hR hm
  exact (tf_twistie3Flux_slice I hΦ (by omega) _ (T (Nstar β)) t
    (Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le)
    (Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.1.le)).1

/-- `Twistie3FluxPeriodicContract` (big-bound estimate `twistie3_flux_periodic`). -/
theorem twistie3FluxPeriodic_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      Twistie3FluxPeriodicContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨hm2, -⟩ := onA7_basic I hperm hR hm
  exact (tf_twistie3Flux_slice I hΦ (by omega) _ (T (Nstar β)) t
    (Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le)
    (Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.1.le)).2

/-- `Normie1FluxSmoothContract` (big-bound estimate `normie1_flux_smooth`). -/
theorem normie1FluxSmooth_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      Normie1FluxSmoothContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨hm2, -⟩ := onA7_basic I hperm hR hm
  exact (tf_normie1Flux_slice I hΦ (by omega) _ (T (Nstar β)) t
    (Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le)
    (Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.1.le)).1

/-- `Normie1FluxPeriodicContract` (big-bound estimate `normie1_flux_periodic`). -/
theorem normie1FluxPeriodic_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      Normie1FluxPeriodicContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨hm2, -⟩ := onA7_basic I hperm hR hm
  exact (tf_normie1Flux_slice I hΦ (by omega) _ (T (Nstar β)) t
    (Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le)
    (Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.1.le)).2

/-- `Normie2FluxSmoothContract` (big-bound estimate `normie2_flux_smooth`). -/
theorem normie2FluxSmooth_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      Normie2FluxSmoothContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  exact (tf_normie2Flux_slice I hΦ m _ (T (Nstar β)) t
    (Hm_slice_contDiff_pos I hΦ (by omega) hκm hθprev hT ht.1)
    (Hm_periodic_pos I hΦ (by omega) hκm hθprev hT ht.1)).1

/-- `Normie2FluxPeriodicContract` (big-bound estimate `normie2_flux_periodic`). -/
theorem normie2FluxPeriodic_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      Normie2FluxPeriodicContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  exact (tf_normie2Flux_slice I hΦ m _ (T (Nstar β)) t
    (Hm_slice_contDiff_pos I hΦ (by omega) hκm hθprev hT ht.1)
    (Hm_periodic_pos I hΦ (by omega) hκm hθprev hT ht.1)).2

end AVenhance.Infra.Section5.Contracts
end
