/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.UniformContracts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Uniform.ForcedEnergySup
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Uniform.HeatApproxH1

/-! # Proofs of the uniform-regularity statements -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.Contracts

open AVenhance AVenhance.Infra.FullTheorem AVenhance.Infra.Parabolic.WeakUniqueness

theorem forcedEnergySup_contract : ForcedEnergySupContract := by
  intro b hb_meas hb_bdd hb_per hdiv φ hφ_meas hφ_per hφ_diff hbφ Ψ hΨ κ hκ g hg hgp θM hθM
    θ Dθ hθ η hη
  exact Uniform.stream_difference_sup hb_meas hb_bdd hb_per hdiv hφ_meas hφ_per hφ_diff hbφ hΨ
    hκ hg hgp hθM hθ hη

theorem heatApproxH1_contract : HeatApproxH1Contract := by
  intro f Df hf hm hA α hα hαsmall
  exact Uniform.analytic_approximation_gradient hf hm hA hα hαsmall

theorem weakDifference_contract : WeakDifferenceContract := by
  intro b hb_meas hb_bdd hb_per hdiv κ hκ f g hf hg θ θ' Dθ Dθ' hθ hθ' t ht
  have hsub := isWeakSolutionGrad_sub hf hg hθ hθ'
  have hfg : MemL2On unitCube (fun x => f x - g x) := hf.sub hg
  have hid := weak_solution_divFree_energy_identity hsub hfg hb_meas hb_bdd hb_per hdiv t ht
  have hnn : 0 ≤ ∫ p in Set.Ioo (0 : ℝ) t ×ˢ unitCube,
      vecNormSq ((fun t x => Dθ t x - Dθ' t x) p.1 p.2) :=
    integral_nonneg fun p => vecNormSq_nonneg _
  have : 0 ≤ 2 * κ * (∫ p in Set.Ioo (0 : ℝ) t ×ˢ unitCube,
      vecNormSq ((fun t x => Dθ t x - Dθ' t x) p.1 p.2)) := by positivity
  exact le_of_le_of_eq (by linarith) hid

end AVenhance.Infra.FullTheorem.Contracts
