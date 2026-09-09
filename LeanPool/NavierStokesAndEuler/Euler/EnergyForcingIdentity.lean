/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EnergyWordCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.TransportL2Time

@[expose] public section

/-! Exact identification of the limiting actual metric forcing with the seven spatial correction
  terms. -/

noncomputable section

namespace EulerEnergyForcingIdentity

open InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerSobolevTransport
    EulerSobolevL2Product
  EulerSobolevMetricTransport EulerGevreyDifferentiatedEquation EulerGevreyCorrectionForcing
  EulerEnergyWordCoordinates EulerGevreyMetricComparison EulerBaseWordMetric EulerMildTopWord
  EulerSobolevWordLevel

variable (period : ℝ) [Fact (0 < period)]

/-- The actual H¹→L² transport depends only on the underlying velocity field, independently of its Sobolev order. -/
theorem transportOperator_of_value_eq {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (κ : ℝ) (m : Vector3)
    (u : SobolevSpace period p) (v : SobolevSpace period q) (huv : value period u = value period v)
    (e : SobolevSpace period 1) : transportOperator period hp κ m u e = transportOperator period hq
      κ m v e := by
  rw [transportOperator_apply, transportOperator_apply]
  exact Finset.sum_congr rfl (fun i _ => scalarProduct_of_value_eq period hp hq
    (velocityComponents κ m i) u v huv (value period (derivativeOperator period 0 i e)))

/-- The literal metric transport of a concatenated energy word is exactly the top transport in the spatial telescope. -/
theorem metric_topTransport {s N : ℕ} (hs : 6 ≤ s) (hN : N+6 ≤ s) (κ : ℝ) (m : Vector3)
    (z : SobolevSpace period s) (u v : SobolevSpace period (s+1))
    (hzu : value period z = value period u) (I : ExternalWord N) (a : BaseWord 6) :
    transportOperator period (by omega : 3 ≤ s) κ m z
      (boundedWordBlock period 1 (energyLength I a) (by have := energyLength_le hN I a; omega)
        (energyWord I a) v) =
      topTransport period N hN (velocityComponents κ m) u v I a := by
  rw [topTransport_block period hN I a v]
  change _ = EulerTransportL2Bilinear.transportL2Bilinear period (by norm_num : 3 ≤ 7)
    (velocityComponents κ m)
    (restrictOperator period (by omega : 7 ≤ s+1) u) _
  rw [EulerTransportL2Bilinear.transportL2Bilinear_eq_metric]
  apply transportOperator_of_value_eq period (by omega : 3 ≤ s) (by norm_num : 3 ≤ 7) κ m z _ _ _
  exact hzu

/-- Negating a genuine Sobolev field negates every exact external/base energy word. -/
theorem energyValues_neg {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (u : SobolevSpace period s)
    (I : ExternalWord N) (a : BaseWord q) :
    energyValues period q N hN (-u) I a = -energyValues period q N hN u I a := by
  rw [← energyWordOperator_apply, ← energyWordOperator_apply, map_neg]

/-- The actual source-plus-transport-plus-signed-pressure forcing equals precisely the seven correction terms. -/
theorem forcing_word_telescope {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (K0 : CoefficientJet period standardDirection
      6 A)
    (N : ℕ) (hN : N+6 ≤ s) (κ : ℝ) (m : Vector3)
    (hL : ∀ i, ‖velocityComponents κ m i‖ ≤ 1)
    (z : SobolevSpace period s) (u v : SobolevSpace period (s+1)) (hzu : value period z = value
      period u)
    (f p0 p1 : SobolevSpace period s) (I : ExternalWord N) (a : BaseWord 6) :
    word period (-(transportBilinear period hs (velocityComponents κ m) hL u v + f -
      coefficientSobolevOperator period K p0 - coefficientSobolevOperator period K p1))
      (energyLength_le hN I a) (energyWord I a) +
      transportOperator period (by omega : 3 ≤ s) κ m z
        (boundedWordBlock period 1 (energyLength I a) (by have := energyLength_le hN I a; omega)
          (energyWord I a) v) +
      A.operator (word period (-(p0+p1)) (energyLength_le hN I a) (energyWord I a)) =
      correctionForcing period hs K K0 N hN (velocityComponents κ m) hL u v f p0 p1 I a := by
  let raw := transportBilinear period hs (velocityComponents κ m) hL u v + f -
    coefficientSobolevOperator period K p0 - coefficientSobolevOperator period K p1
  have hn (v' : SobolevSpace period s) :
      word period (-v') (energyLength_le hN I a) (energyWord I a) = -energyValues period 6 N hN v'
        I a :=
    (energyValues_eq_word period 6 N hN I a (-v')).symm.trans
      (energyValues_neg period 6 N hN v' I a)
  have hp : A.operator (word period (-(p0+p1)) (energyLength_le hN I a) (energyWord I a)) =
      -(A.operator (energyValues period 6 N hN (p0+p1) I a)) :=
    (congrArg A.operator (hn (p0+p1))).trans (map_neg A.operator _)
  have ht := metric_topTransport period hs hN κ m z u v hzu I a
  have he := congrFun (congrFun (correction_differentiated_identity period hs K K0 N hN
    (velocityComponents κ m) hL u v f p0 p1) I) a
  simp only [Pi.sub_apply] at he
  change word period (-raw) (energyLength_le hN I a) (energyWord I a) + _ + _ = _
  rw [hn raw, hp, ht]
  change energyValues period 6 N hN raw I a = _ at he
  rw [he]
  abel

end EulerEnergyForcingIdentity
