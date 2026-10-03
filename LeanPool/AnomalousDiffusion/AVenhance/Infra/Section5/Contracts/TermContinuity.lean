/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuityDiv
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuityPointwise

/-! # `TermContinuousContract`

Each of the ten §5.1 terms of the actual ansatz is jointly continuous on the open half space
(`TermContinuityDiv`: the divergence-form terms; `TermContinuityPointwise`: the others), hence on
`(0,1) × ℝ²`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open Homogenization AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

/-- `TermContinuousContract` (big-bound estimate `term_continuous`, also consumed by step-down
    part (ii)). -/
theorem termContinuous_contract (β C₀ : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      TermContinuousContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T) := by
  refine ⟨0, ?_⟩
  intro I _ _ _ _ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm _ θprev T hθprev hT i hi
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  have hm1 : 1 ≤ m := by omega
  have hsub : Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec 2)) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.univ :=
    Set.prod_mono Set.Ioo_subset_Ioi_self le_rfl
  interval_cases i
  · exact (cutoff1_term_continuousOn I hΦ hm1 hκm hθprev hT).mono hsub
  · exact (twistie1_term_continuousOn I hΦ hm1 hκm hθprev hT).mono hsub
  · exact (twistie3_term_continuousOn I hΦ hm1 hκm hθprev hT).mono hsub
  · exact (twistie4_term_continuousOn I hΦ hm1 hκm hθprev hT).mono hsub
  · exact (twistie5_term_continuousOn I hΦ hm1 hκm hθprev hT).mono hsub
  · exact (normie1_term_continuousOn I hΦ hm1 hκm hθprev hT).mono hsub
  · exact (normie2_term_continuousOn I hΦ hm1 hκm hθprev hT).mono hsub
  · exact (tiny_term_continuousOn I hΦ hm1 hκm hθprev hT).mono hsub
  · exact (normie3_term_continuousOn I hΦ hm1 hκm hθprev hT).mono hsub
  · exact (R46_term_continuousOn I hΦ hm1 hκm hθprev hT).mono hsub

end AVenhance.Infra.Section5.Contracts
