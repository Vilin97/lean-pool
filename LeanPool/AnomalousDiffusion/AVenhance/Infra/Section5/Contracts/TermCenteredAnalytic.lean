/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsCentered
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.FlowForErgodicBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticNear
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticCompose

/-! # Analytic inputs of the centered ergodic estimates

The four statements below are assembled from the helper modules
`TermCenteredAnalytic{Window,Jets,Near,Smooth,Inputs,Compose}`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError

/-- Near-identity of the actual flow slice on the support of `ξ_{m,k}`. -/
theorem sd_flow_nearIdentity {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 4)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {k : ℤ} (hξ : I.xiMK m k t ≠ 0) :
    Infra.Ergodic.FlowDerivativeNearIdentity
      (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t) := by
  have _ := ht
  exact sdn_flow_nearIdentity I hΦ hm hsmall hξ

/-- The two slow factors are smooth and `ℤ²`-periodic (any `k`). -/
theorem sd_slow2_smooth_periodic {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTp : IsZ2Periodic (T t)) (k : ℤ) (a j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (section5SlowChoice2 I hΦ m κm T k t a j) ∧
      Infra.Ergodic.IsZPeriodic (section5SlowChoice2 I hΦ m κm T k t a j) :=
  ⟨(sds_slow2 I hΦ m κm T hTt hTp k a j).1,
    sds_isZPeriodic_of_isZ2Periodic (sds_slow2 I hΦ m κm T hTt hTp k a j).2⟩

theorem sd_slow3_smooth_periodic {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTp : IsZ2Periodic (T t)) (k : ℤ) (a j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (section5SlowChoice3 I hΦ m T k t a j) ∧
      Infra.Ergodic.IsZPeriodic (section5SlowChoice3 I hΦ m T k t a j) :=
  ⟨(sds_slow3 I hΦ m T hTt hTp k a j).1,
    sds_isZPeriodic_of_isZ2Periodic (sds_slow3 I hΦ m T hTt hTp k a j).2⟩

end AVenhance.Infra.Section5.Contracts
end
