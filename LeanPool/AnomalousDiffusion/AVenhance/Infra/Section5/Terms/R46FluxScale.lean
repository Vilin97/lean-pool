/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46FluxSupport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46Scale

/-! Source-scale transfer for the corrected transition-window flux.

The two analytic inputs are kept separate: flow distortion controls the
flux-to-gradient time norm, and the previous-scale energy estimate controls
the gradient time norm. The support and exact-flux identities that justify
the first input are proved in `R46FluxSupport`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The space-time L² norm of the spatial L² norm, in the exact ENNReal
carrier used for the `R46` source estimate. -/
def r46TimeL2 (F : ℝ → Vec 2 → Vec 2) : ENNReal :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt (gradNormSq (F t))) ^ 2) ^ (1 / 2 : ℝ)

end AVenhance.Infra.Section5
end
