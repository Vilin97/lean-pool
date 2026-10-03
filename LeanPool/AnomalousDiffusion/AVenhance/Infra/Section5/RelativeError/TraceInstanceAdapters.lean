/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceInstanceInterface
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceInstanceContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.ThetaProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.RelativeInitialProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TMaterialFamily

/-! # Compatibility of the uniform producer with the step-down part (ii) adapters -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Section4
open AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Integration
open AVenhance.Infra.Section5.Contracts

/-- Expand the producer's shared literal trace formula to the exact alias
consumed by T7 and T10. This is a definitional bridge only. -/
theorem e44_uniformTrace_for_T1h_contracts (β C₀ : ℝ) :
    ∃ Ctr L : ℝ, 1 ≤ Ctr ∧ OnA8Instances β C₀ L
      (fun I _Φ _hΦ κ M R θ₀ m _θm θprev _T =>
        (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        T1hThetaInitialTraceInput β I κ M m θ₀ θprev Ctr) := by
  obtain ⟨Ctr, L, hCtr, hfamily⟩ := e44_initialTrace_contract β C₀
  refine ⟨Ctr, L, hCtr, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκp M hM hperm R hR θ₀ hθ₀smooth hθ₀per hmean
    hanalytic m hm0 hmM θm θprev T hθm hθprev hT hgate hlater
  exact hfamily I hz hx hh hΛ Φ hΦ κ hκp M hM hperm R hR θ₀ hθ₀smooth hθ₀per
    hmean hanalytic m hm0 hmM θm θprev T hθm hθprev hT hgate hlater

end AVenhance.Infra.Section5.RelativeError

end
