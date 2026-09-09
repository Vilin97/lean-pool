/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EnergyForcingIdentity

@[expose] public section

/-! Actual coercive projected sources have precisely the signed energy forcing required by the
  differentiated equation. -/

noncomputable section

namespace EulerProjectedEnergyForcing

open InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse
  EulerSobolevCoefficientPressure EulerSobolevTransport EulerEnergyWordCoordinates
    EulerEnergyForcingIdentity
  EulerGevreyCorrectionForcing EulerGevreyDifferentiatedEquation EulerGevreyMetricComparison
    EulerBaseWordMetric
  EulerMildTopWord

variable (period : ℝ) [Fact (0 < period)]

/-- The actual pressure-projected negative source splits into its two positive pressure solves with the literal PDE signs. -/
theorem projected_negative_split {s : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ) (T F : SobolevSpace period s) :
    -(projectedSourceOperator period K κ m c hc hpos (T+F)) =
      -(T+F-coefficientSobolevOperator period K (pressureSobolevOperator period K κ m c hc hpos F)-
        coefficientSobolevOperator period K (pressureSobolevOperator period K κ m c hc hpos T)) :=
          by
  let P := pressureSobolevOperator period K κ m c hc hpos
  let G := coefficientSobolevOperator period K
  change -(T+F-G (P (T+F))) = -(T+F-G (P F)-G (P T))
  rw [map_add P T F, map_add G (P T) (P F)]
  abel

/-- The signed actual pressure is the negative sum of the two genuine component pressure solves. -/
theorem pressure_negative_split {s : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ) (T F : SobolevSpace period s) :
    -(pressureSobolevOperator period K κ m c hc hpos (T+F)) =
      -(pressureSobolevOperator period K κ m c hc hpos F + pressureSobolevOperator period K κ m c
        hc hpos T) := by
  rw [map_add]
  exact congrArg (fun x : SobolevSpace period s => -x) (add_comm _ _)

/-- The actual coercive projected source and actual signed pressure give exactly the seven differentiated correction terms. -/
theorem projected_forcing_word {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (K0 : CoefficientJet period standardDirection
      6 A)
    (N : ℕ) (hN : N+6 ≤ s) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (hL : ∀ i, ‖velocityComponents κ m i‖ ≤ 1)
    (z : SobolevSpace period s) (u v : SobolevSpace period (s+1)) (hzu : value period z = value
      period u)
    (f : SobolevSpace period s) (I : ExternalWord N) (a : BaseWord 6) :
    word period (-(projectedSourceOperator period K κ m c hc hpos
      (transportBilinear period hs (velocityComponents κ m) hL u v+f)))
      (energyLength_le hN I a) (energyWord I a) +
      EulerSobolevMetricTransport.transportOperator period (by omega : 3 ≤ s) κ m z
        (boundedWordBlock period 1 (energyLength I a) (by have := energyLength_le hN I a; omega)
          (energyWord I a) v) +
      A.operator (word period (-(pressureSobolevOperator period K κ m c hc hpos
        (transportBilinear period hs (velocityComponents κ m) hL u v+f)))
        (energyLength_le hN I a) (energyWord I a)) =
      correctionForcing period hs K K0 N hN (velocityComponents κ m) hL u v f
        (pressureSobolevOperator period K κ m c hc hpos f)
        (pressureSobolevOperator period K κ m c hc hpos
          (transportBilinear period hs (velocityComponents κ m) hL u v)) I a := by
  let TV := transportBilinear period hs (velocityComponents κ m) hL u v
  let D := wordOperator period (⟨⟨energyLength I a, Nat.lt_succ_of_le (energyLength_le hN I
    a)⟩,energyWord I a⟩ : SobolevWord s)
  let Tr := EulerSobolevMetricTransport.transportOperator period (by omega : 3 ≤ s) κ m z
    (boundedWordBlock period 1 (energyLength I a) (by have := energyLength_le hN I a; omega)
      (energyWord I a) v)
  have hf := projected_negative_split period K κ m c hc hpos TV f
  have hp := pressure_negative_split period K κ m c hc hpos TV f
  have he := forcing_word_telescope period hs K K0 N hN κ m hL z u v hzu f
    (pressureSobolevOperator period K κ m c hc hpos f)
    (pressureSobolevOperator period K κ m c hc hpos TV) I a
  have hh := congrArg₂ (fun x y : LiftL2 period => x+Tr+A.operator y) (congrArg D hf) (congrArg D
    hp)
  exact hh.trans he

end EulerProjectedEnergyForcing
