/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionLocal
public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatGenerator
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
import LeanPool.NavierStokesAndEuler.Euler.MildEquationBridge
import LeanPool.NavierStokesAndEuler.Euler.SobolevPressureResolvent

/-! The constructed local viscous Euler correction satisfies the actual differential equation and
pressure constraint. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionOperators

open MeasureTheory InnerProductSpace Set EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevTransport
  EulerSobolevCoefficientPressure EulerQuadraticSource EulerMildEquationBridge
  EulerSobolevHeatGenerator EulerDuhamelDifferentiation EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance equationSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance equationSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual non-pressure residual and nonlinear increment in equation (17). -/
def CorrectionData.rawSource {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q + 1)) :
        SobolevSpace period q :=
  (D.coefficients period hq).forcing t + (D.coefficients period hq).linear t e +
    (D.coefficients period hq).quadratic t e e

/-- The correction pressure is the actual unique coercive gradient solution with the sign of
equation (17). -/
def CorrectionData.pressure {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q + 1)) :
        SobolevSpace period q :=
  -(pressureSobolevOperator period (D.metric.jet t) D.κ D.direction D.coercivity D.coercivity_pos
    (D.metric_pos t) (D.rawSource period hq t e))

/-- The actual pressure belongs to the closed lifted gradient space. -/
theorem CorrectionData.pressure_mem_gradient {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q + 1)) :
    value period (D.pressure period hq t e) ∈ gradientSpace period D.κ D.direction := by
  change -value period (pressureSobolevOperator period (D.metric.jet t) D.κ D.direction D.coercivity
    D.coercivity_pos (D.metric_pos t) _) ∈ _
  exact (gradientSpace period D.κ D.direction).neg_mem
    (pressureSobolev_mem_gradient period (D.metric.jet t) D.κ D.direction D.coercivity
        D.coercivity_pos (D.metric_pos t) _)

/-- The projected source equals the literal non-pressure source plus the actual coefficient-weighted
pressure. -/
theorem CorrectionData.source_value {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q + 1)) :
    value period ((D.coefficients period hq).apply t e) =
      -value period (D.rawSource period hq t e) -
        (D.metric.coefficient t).operator (value period (D.pressure period hq t e)) := by
  change -value period (projectedSourceOperator period (D.metric.jet t) D.κ D.direction D.coercivity
    D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e)) = _
  rw [projectedSourceOperator_value]
  change -(value period (D.rawSource period hq t e) -
    (D.metric.coefficient t).operator ((D.metric.coefficient t).pressure D.κ D.direction
        D.coercivity D.coercivity_pos
      (D.metric_pos t) (value period (D.rawSource period hq t e)))) =
    -value period (D.rawSource period hq t e) - (D.metric.coefficient t).operator
      (-value period (pressureSobolevOperator period (D.metric.jet t) D.κ D.direction D.coercivity
        D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e)))
  rw [map_neg, pressureSobolevOperator_value]
  abel

/-- The constructed actual local Euler correction has zero initial error, zero lifted divergence,
and satisfies equation (17) in L² at every interior time. -/
theorem exists_local_euler_correction_PDE {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (S : ℝ) (hS : 0 < S) (D : CorrectionData period q (Icc (0 : ℝ) S)) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)),
        ‖e‖ ≤ 1 ∧ e ⟨0, le_rfl, hT.le⟩ = 0 ∧
        (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
        ∀ t (ht : t ∈ Ioo 0 T),
          HasDerivAt (fun r => value period (extendPath T hT.le e r))
            (ν • laplacianEvaluation period (q+1) (by omega) (e ⟨t,ht.1.le,ht.2.le⟩) -
              value period (D.rawSource period hq (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e
                  ⟨t,ht.1.le,ht.2.le⟩)) -
              (D.metric.coefficient (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩)).operator
                (value period (D.pressure period hq (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e
                    ⟨t,ht.1.le,ht.2.le⟩)))) t := by
  obtain ⟨T, hT, hTS, e, he, hi, hd, hsol⟩ := exists_local_euler_correction period hq ν hν S hS D
  refine ⟨T, hT, hTS, e, he, hi, hd, ?_⟩
  let F := ((D.coefficients period hq).comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q+1) => F p.1 p.2) :=
    ((D.coefficients period hq).comp (timeInclusion hTS)).continuous
  intro t ht
  have hp := viscous_mild_hasDerivAt period (by omega : 2 ≤ q) ν hν T hT.le 0 F hF e hsol t ht
  change HasDerivAt _ (ν • laplacianEvaluation period (q+1) _ (e ⟨t,ht.1.le,ht.2.le⟩) +
    value period ((D.coefficients period hq).apply (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e
        ⟨t,ht.1.le,ht.2.le⟩))) t at hp
  rw [D.source_value period hq] at hp
  convert hp using 1
  abel

end EulerCorrectionOperators
