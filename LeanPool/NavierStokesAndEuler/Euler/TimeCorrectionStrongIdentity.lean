/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeCorrectionSource

/-! The constructed Bochner correction source is literally the higher-order nonlinear correction
almost everywhere. -/

@[expose] public section


noncomputable section

namespace EulerTimeCorrectionStrongIdentity

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAsymmetricTransport
  EulerSobolevTransport EulerTimeLp EulerVolterraConvolution EulerTimeCorrectionSource
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine raw source is the literal transport of the actual higher-order representative plus
the prescribed lower-order terms. -/
theorem rawSourceTime_transport_ae {s : ℕ} (hs : 6 ≤ s) (T : ℝ) (hT : 0 ≤ T)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (C : Fin 3 → C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (z : C(Icc (0 : ℝ) T, SobolevSpace period (s + 1)))
    (r e : C(Icc (0 : ℝ) T, SobolevSpace period s)) (U : TimeLp T (SobolevSpace period (s + 1)))
    (hU : (fun t => truncateOperator period s (U t)) =ᵐ[timeMeasure T] extendPath T hT e) :
    (rawSourceTime period hs T hT L hL C0 C z r e U : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => transportBilinear period hs L hL (extendPath T hT z t + U t) (U t) +
        extendPath T hT (orderZeroPath period hs T L hL C0 C z r e) t := by
  filter_upwards [rawSourceTime_ae period hs T hT L hL C0 C z r e U, hU] with t hraw hu
  have ht := asymmetricTransport_eq period hs L hL (extendPath T hT z t + U t) (U t)
  have hv : truncateOperator period s (extendPath T hT z t + U t) =
      truncateOperator period s (extendPath T hT z t) + extendPath T hT e t :=
    (map_add (truncateOperator period s) (extendPath T hT z t) (U t)).trans
      (congrArg (fun x : SobolevSpace period s => truncateOperator period s (extendPath T hT z
          t)+x) hu)
  have ht' := (congrArg (fun x : SobolevSpace period s => asymmetricTransport period hs L hL x (U
      t)) hv).symm.trans ht
  exact hraw.trans (congrArg (fun v : SobolevSpace period s => v +
    extendPath T hT (orderZeroPath period hs T L hL C0 C z r e) t) ht')

/-- The continuous transport velocity and its higher Sobolev representative have the same actual L²
value almost everywhere. -/
theorem transport_velocity_value_ae {s : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (z : C(Icc (0 : ℝ) T, SobolevSpace period (s + 1))) (e : C(Icc (0 : ℝ) T, SobolevSpace period
        s))
    (U : TimeLp T (SobolevSpace period (s + 1)))
    (hU : (fun t => truncateOperator period s (U t)) =ᵐ[timeMeasure T] extendPath T hT e) :
    (fun t => value period (truncateOperator period s (extendPath T hT z t) + extendPath T hT e t))
        =ᵐ[timeMeasure T]
      fun t => value period (extendPath T hT z t + U t) := by
  filter_upwards [hU] with t ht
  rw [← ht]
  exact congrArg (value period) (map_add (truncateOperator period s) (extendPath T hT z t) (U
      t)).symm

end EulerTimeCorrectionStrongIdentity
