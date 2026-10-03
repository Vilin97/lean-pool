/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.TransportLimitContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.TransportLimit.LimitWeakForm

/-! # Proof of the transport-limit statement

`transportLimit_contract : TransportLimitContract`.  The limit `Θ` is the pointwise limit of a
fast subsequence (`TransportLimit.Construction`); the weak form passes to the limit using the
divergence-free cancellation `∫ (b·Dθ) φ = -∫ θ b·∇φ` and the energy bound on the viscous term. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem.Contracts

open AVenhance AVenhance.Infra.FullTheorem AVenhance.Infra.FullTheorem.TransportLimit

theorem transportLimit_contract : TransportLimitContract := by
  intro b hmeas hbdd hper hdiv θ₀ hθ₀ κ hκ hκ0 θ hθ hcau
  have h : DriftHyp b := ⟨hmeas, hbdd, hper, hdiv⟩
  choose Dθ hD using hθ
  obtain ⟨Θ, hΘper, hΘmem, hΘjoint, hunif⟩ := exists_uniform_l2_limit θ
    (fun j t ht => (hD j).1 t ht |>.1) (fun j t ht => (hD j).1 t ht |>.2)
    (fun j => (hD j).2.2.1) hcau
  refine ⟨Θ, ⟨fun t ht => ⟨hΘper t ht, hΘmem t ht⟩, ?_, hΘjoint, ?_, ?_⟩, hΘmem, hunif⟩
  · exact limit_l2_bound (fun j t ht => (hD j).1 t ht |>.2)
      (fun j => (hD j).2.1) hΘmem hunif
  · intro ψ hψ hψp
    exact limit_weak_continuity (fun j t ht => (hD j).1 t ht |>.2) hΘmem
      (fun j ψ hψ hψp => (hD j).2.2.2.2.2.2.1 ψ hψ hψp) hunif hψ hψp
  · intro φ hφ
    exact limit_weak_form h hθ₀ hκ hκ0 hD hΘjoint hunif hφ

end AVenhance.Infra.FullTheorem.Contracts
