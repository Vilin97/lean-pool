/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBoundRegularityMeans
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBoundMeanZeroGroup
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBoundMeanZeroData

/-! Producers for the four mean-zero contracts consumed by big-bound estimate and step-down part
    (ii). -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

theorem groupMeanZero_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      GroupMeanZeroContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR _θ₀ _ _ _ _ m hm _ _θprev T hθprev hT t ht
  obtain ⟨hm2, _⟩ := onA7_basic I hperm hR hm
  have hTsm : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t) :=
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le
  have hTper : IsZ2Periodic (T (Nstar β) t) :=
    Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.1.le
  exact group_meanZero_of_slice I hΦ m (by omega) (I.kappaSeq κ M m)
    (T (Nstar β)) hTsm hTper

theorem cutoff1MeanZero_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      Cutoff1MeanZeroContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨_, _⟩ := onA7_basic I hperm hR hm
  have hTsm : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t) :=
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le
  have hTper : IsZ2Periodic (T (Nstar β) t) :=
    Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.1.le
  exact cutoff1_meanZero_of_slice I hΦ m (I.kappaSeq κ M m)
    (T (Nstar β)) hTsm hTper

theorem twistie1MeanZero_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      Twistie1MeanZeroContract I hΦ m (I.kappaSeq κ M m) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨hm2, _⟩ := onA7_basic I hperm hR hm
  have hTsm : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t) :=
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le
  have hTper : IsZ2Periodic (T (Nstar β) t) :=
    Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.1.le
  exact twistie1_meanZero_of_slice I hΦ m (by omega) (I.kappaSeq κ M m)
    (T (Nstar β)) hTsm hTper

theorem tinyMeanZero_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      TinyMeanZeroContract I hΦ m (I.kappaSeq κ M m)
        (I.kappaSeq κ M (m - 1)) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT t ht
  obtain ⟨hm2, _⟩ := onA7_basic I hperm hR hm
  have hSourceErrors := actual_sourceErrors_regular_of_iterates I hΦ m (by omega)
    (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T hθprev hT ht.1
  rcases hSourceErrors with ⟨⟨hdsm, hdper⟩, ⟨hesm, heper⟩⟩
  exact tiny_meanZero_of_slice I hΦ m (by omega) (I.kappaSeq κ M m)
    (sourceErrorD I hΦ m (I.kappaSeq κ M m) (T (Nstar β)))
    (iterateError I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T)
    hdsm hdper hesm heper

end AVenhance.Infra.Section5.Contracts

end
