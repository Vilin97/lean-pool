/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderGraphTrace
import LeanPool.NavierStokesAndEuler.Euler.LpBochnerRealization

/-! Actual spatial L² restrictions of smooth cylinder fields. The bound is
uniform over every continuous phase graph, including arbitrarily high
oscillation frequencies. -/

@[expose] public section


noncomputable section

namespace EulerCylinderGraphTrace

open Set MeasureTheory EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLpBochnerRealization
open scoped ContDiff Topology

variable (P : ℝ) [Fact (0 < P)]

private theorem norm_sq_of_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : Lp Vector3 2 μ) (f : X → Vector3)
    (hu : (u : X → Vector3) =ᵐ[μ] f) :
    ‖u‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_integral]
  exact integral_congr_ae (hu.mono (fun _ hx =>
    congrArg (fun z : Vector3 => ‖z‖^2) hx))

variable (f : LiftDomain P → Vector3)
  (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x))
  (u v : LiftL2 P)
  (hu : (u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f)
  (hv : (v : LiftDomain P → Vector3) =ᵐ[liftMeasure P] fieldDerivative P (0, 1) f)
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

include hf hu hv hθ in
theorem graph_memLp_of_representatives :
    MemLp (fun x => f (x,θ x)) 2 volume :=
  (graph_memLp_and_energy_bound P f hf
    ((memLp_congr_ae hu).1 (Lp.memLp u))
    ((memLp_congr_ae hv).1 (Lp.memLp v)) θ hθ).1

/-- The actual L² class of the field on the prescribed phase graph. -/
def graphRealization : Lp Vector3 2 (volume : Measure Vector3) :=
  (graph_memLp_of_representatives P f hf u v hu hv θ hθ).toLp (fun x => f (x,θ x))

theorem graphRealization_ae :
    (graphRealization P f hf u v hu hv θ hθ : Vector3 → Vector3) =ᵐ[volume]
      fun x => f (x,θ x) :=
  (graph_memLp_of_representatives P f hf u v hu hv θ hθ).coeFn_toLp

include hf hu hv hθ in
/-- Any L² representative of this same graph satisfies the genuine trace bound. -/
theorem graph_norm_sq_le (w : Lp Vector3 2 (volume : Measure Vector3))
    (hw : (w : Vector3 → Vector3) =ᵐ[volume] fun x => f (x, θ x)) :
    ‖w‖^2 ≤ (2/P)*‖u‖^2+(2*P)*‖v‖^2 := by
  rw [norm_sq_of_ae volume w _ hw,
    norm_sq_of_ae (liftMeasure P) u f hu,
    norm_sq_of_ae (liftMeasure P) v _ hv]
  exact (graph_memLp_and_energy_bound P f hf
    ((memLp_congr_ae hu).1 (Lp.memLp u))
    ((memLp_congr_ae hv).1 (Lp.memLp v)) θ hθ).2

theorem graphRealization_norm_sq_le :
    ‖graphRealization P f hf u v hu hv θ hθ‖^2 ≤
      (2/P)*‖u‖^2+(2*P)*‖v‖^2 :=
  graph_norm_sq_le P f hf u v hu hv θ hθ _
    (graphRealization_ae P f hf u v hu hv θ hθ)

end EulerCylinderGraphTrace
