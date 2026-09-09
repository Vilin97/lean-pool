/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EnergyWordCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionForcing
import LeanPool.NavierStokesAndEuler.Euler.ProjectedEnergyForcing
import LeanPool.NavierStokesAndEuler.Euler.SobolevWordValueIdentity

/-! Exact energy forcing from the literal raw, projected, and signed-pressure field identities. -/

@[expose] public section


noncomputable section

namespace EulerProjectedForcingFields

open InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerSobolevTransport EulerMildTopWord
  EulerEnergyWordCoordinates EulerSobolevWordValueIdentity EulerProjectedEnergyForcing
  EulerGevreyCorrectionForcing EulerGevreyMetricComparison EulerBaseWordMetric
      EulerSobolevMetricTransport

variable (period : ℝ) [Fact (0 < period)]

/-- Actual raw-source and pressure identities determine the complete differentiated forcing,
independently of the chosen equivalent higher representative. -/
theorem forcing_word_of_actual_fields {s r : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (K0 : CoefficientJet period standardDirection
        6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hL : ∀ i, ‖velocityComponents κ m i‖ ≤ 1)
    (z : SobolevSpace period s) (u v : SobolevSpace period (s + 1)) (V : SobolevSpace period r)
    (hzu : value period z = value period u) (hV : value period V = value period v)
    (f raw F P : SobolevSpace period s)
    (hraw : raw = transportBilinear period hs (velocityComponents κ m) hL u v + f)
    (hF : F = -(projectedSourceOperator period K κ m c hc hpos raw))
    (hP : P = -(pressureSobolevOperator period K κ m c hc hpos raw))
    (I : ExternalWord N) (a : BaseWord 6) (horder : 1 + energyLength I a ≤ r) :
    word period F (energyLength_le hN I a) (energyWord I a) +
      transportOperator period (by omega : 3 ≤ s) κ m z
        (boundedWordBlock period 1 (energyLength I a) horder (energyWord I a) V) +
      A.operator (word period P (energyLength_le hN I a) (energyWord I a)) =
      correctionForcing period hs K K0 N hN (velocityComponents κ m) hL u v f
        (pressureSobolevOperator period K κ m c hc hpos f)
        (pressureSobolevOperator period K κ m c hc hpos
          (transportBilinear period hs (velocityComponents κ m) hL u v)) I a := by
  let D := wordOperator period (⟨⟨energyLength I a,Nat.lt_succ_of_le (energyLength_le hN I
      a)⟩,energyWord I a⟩ : SobolevWord s)
  let Tr := transportOperator period (by omega : 3 ≤ s) κ m z
  have hf' := hF.trans (congrArg (fun x : SobolevSpace period s => -(projectedSourceOperator period
      K κ m c hc hpos x)) hraw)
  have hp' := hP.trans (congrArg (fun x : SobolevSpace period s => -(pressureSobolevOperator period
      K κ m c hc hpos x)) hraw)
  have hblock := boundedWordBlock_of_value_eq period V v hV horder
    (by have := energyLength_le hN I a; omega : 1+energyLength I a ≤ s+1) (energyWord I a)
  have he := congrArg₂ (fun x y : SobolevSpace period s => D x +
    Tr (boundedWordBlock period 1 (energyLength I a) horder (energyWord I a) V)+A.operator (D y))
        hf' hp'
  have ht := congrArg (fun b : SobolevSpace period 1 =>
    D (-(projectedSourceOperator period K κ m c hc hpos
      (transportBilinear period hs (velocityComponents κ m) hL u v+f)))+Tr b +
    A.operator (D (-(pressureSobolevOperator period K κ m c hc hpos
      (transportBilinear period hs (velocityComponents κ m) hL u v+f))))) hblock
  exact he.trans (ht.trans (projected_forcing_word period hs K K0 N hN κ m c hc hpos hL z u v hzu f
      I a))

end EulerProjectedForcingFields
