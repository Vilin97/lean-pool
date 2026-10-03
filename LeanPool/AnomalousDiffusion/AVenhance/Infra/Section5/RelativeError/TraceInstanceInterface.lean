/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaProfileDischarge

/-! # The positive-word trace interface shared by the producer and step-down estimate consumers -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Section4
open AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Integration

/-- Literal trace formula, stated independently of the profile consumer
module so the Fourier construction and its adapters can be built in
separate import components. It unfolds to `T1hThetaInitialTraceInput`. -/
def e44PositiveTraceInput (β : ℝ) (I : Ingredients β) (κ : ℝ)
    (M m : ℕ) (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (Ctr : ℝ) : Prop :=
  let S := Real.sqrt (I.kappaSeq κ M (m - 1)) *
    Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (θprev t)))
  ∀ w : List (Fin 2), 1 ≤ w.length →
    Real.sqrt (∫ x in unitCube,
      (classicalWordDerivative w θ₀ x) ^ 2) ≤
    S * ((w.length.factorial : ℝ) /
      ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) / Ctr ^ 2) ^ w.length)

end AVenhance.Infra.Section5.RelativeError

end
