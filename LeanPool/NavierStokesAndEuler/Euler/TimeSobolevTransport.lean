/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AsymmetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.SobolevTimeRegularization

@[expose] public section

/-! Actual derivative-losing transport on continuous coefficients and square-integrable higher
  Sobolev states. -/

noncomputable section

namespace EulerTimeSobolevTransport

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAsymmetricTransport
  EulerTimeLp EulerVolterraConvolution EulerSobolevTimeRegularization EulerHeatRegularizedPaths
  EulerSobolevHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A named local normed-group instance for the actual Sobolev scale. -/
local instance transportTimeGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance

/-- A named local real normed-space instance for the actual Sobolev scale. -/
local instance transportTimeSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- A continuous actual velocity path gives a continuous path of asymmetric transport operators. -/
def transportPath {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s)) :
    C(Icc (0 : ℝ) T, SobolevSpace period (s+1) →L[ℝ] SobolevSpace period s) :=
  (asymmetricTransport period hs L hL).compLeftContinuous ℝ (Icc (0 : ℝ) T) u

/-- Actual nonlinear transport of a higher Sobolev time field belongs to the full energy-order Bochner space. -/
def transportTime {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (v : TimeLp T (SobolevSpace period (s+1))) : TimeLp T (SobolevSpace period s) :=
  timeMultiplier T hT (transportPath period hs L hL T u) v

/-- The actual Bochner transport is literal asymmetric Sobolev transport almost everywhere in time. -/
theorem transportTime_ae {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (v : TimeLp T (SobolevSpace period (s+1))) :
    (transportTime period hs L hL T hT u v : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => asymmetricTransport period hs L hL (extendPath T hT u t) (v t) :=
  timeMultiplier_ae T hT (transportPath period hs L hL T u) v

/-- Genuine heat smoothing and actual transport commute asymptotically in the energy-order L² time space. -/
theorem transport_regularization_commutator {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (v : TimeLp T (SobolevSpace period (s+1))) :
    Filter.Tendsto (fun n =>
      transportTime period hs L hL T hT u
        ((heatOperator period (s+1) (regularizerVariance n)).compLpL 2 (timeMeasure T) v) -
      (heatOperator period s (regularizerVariance n)).compLpL 2 (timeMeasure T)
        (transportTime period hs L hL T hT u v)) Filter.atTop (𝓝 0) :=
  heat_time_commutator_tendsto period s (s+1) T hT (transportPath period hs L hL T u) v

end EulerTimeSobolevTransport
