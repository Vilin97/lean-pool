/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualPointwiseConstructor

/-! The residual field adapter for `BigBoundInputs`. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The `BigBoundInputs.residual` field follows from the iterate
recursion and the exact classical-solution predicate for the previous
iterate.  At each positive time, choose any positive localization radius. -/
theorem frozenResidualBigBoundResidual
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm κprev : ℝ) (hκm : 0 < κm)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x,
      sourceResidualIdentity I hΦ m κm κprev T t x := by
  intro t ht x
  have htpos : 0 < t := ht.1
  have hρ : 0 < (1 : ℝ) := by norm_num
  let R := frozenResidualPointwiseDataOfIterates I hΦ m hm κm κprev hκm
    θ₀ θprev hθprev T hT t htpos x 1 hρ
  have hResidual := frozen_source_residual_identity I hΦ m hm κm κprev
    θ₀ θprev T hT t htpos x 1 hρ R
  simpa [sourceResidualIdentity, R] using hResidual

end AVenhance.Infra.Section5.Integration

end
