/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderPressureCoherence
public import LeanPool.NavierStokesAndEuler.Euler.GraphPressurePotential
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderLiftedCorrection
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothPressureRepresentative

/-! Smooth actual pressure and graph potentials of the constructed common inviscid correction. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderSmoothPressure

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerAllOrderCorrectionData
  EulerAllOrderCorrectionBudget EulerAllOrderCorrectionFamily EulerAllOrderLiftedCorrection
  EulerAllOrderPressureCoherence EulerVolterraConvolution EulerMetricTransport
  EulerSmoothPressureRepresentative EulerGraphPressurePotential
open scoped Topology ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- Every strong derivative order of the common actual signed pressure is supplied by a constructed
finite Sobolev realization. -/
def pressureJet {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (n : ℕ) (t : Icc (0 : ℝ) T) : SpatialJet period standardDirection n (commonPressure period hT A
        B t) := by
  rw [← signedPressurePath_value_common period hT A B (n+6) (by omega) t]
  exact EulerH6Pressure.SpatialJet.restrict
    (toJet period (signedPressurePath period hT A B (n+6) (by omega) t)) n (by omega)

/-- The common nonlinear correction satisfies its actual signed-pressure equation in L². -/
theorem commonPath_pressure_equation {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT
    A)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le (commonPath period hT A B))
      (-value period (rawSourcePath period hT A B 6 le_rfl ⟨t,ht.1.le,ht.2.le⟩) -
        (A.metric.coefficient ⟨t,ht.1.le,ht.2.le⟩).operator
          (commonPressure period hT A B ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have h := commonPath_hasDerivAt period hT A B t ht
  rw [(A.atOrder period 6).source_value period le_rfl] at h
  exact h

/-- The constructed signed pressure has a genuine smooth spatial representative at every time. -/
theorem exists_smooth_signed_pressure {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period
    hT A) :
    ∃ p : Icc (0 : ℝ) T → LiftDomain period → Vector3,
      (∀ t x, ContDiff ℝ ∞ (localFieldLift period (p t) x)) ∧
      ∀ t, (commonPressure period hT A B t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] p
          t := by
  have h (t : Icc (0 : ℝ) T) := exists_smooth_representative period (commonPressure period hT A B t)
    (fun n => pressureJet period hT A B n t)
  choose p hp ha using h
  exact ⟨p,hp,ha⟩

/-- The actual signed correction pressure yields a smooth scalar potential on every
reciprocal-frequency graph.
The common pressure, all its strong jets, its smooth representative and its closed-gradient property
are constructed internally. -/
theorem exists_smooth_pressure_graph {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT
    A)
    (k : ℝ) (hk : k * A.κ = 1) :
    ∃ (p : Icc (0 : ℝ) T → LiftDomain period → Vector3) (Q : Icc (0 : ℝ) T → Vector3 → ℝ),
      (∀ t x, ContDiff ℝ ∞ (localFieldLift period (p t) x)) ∧
      (∀ t, (commonPressure period hT A B t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] p
          t) ∧
      (∀ t, ContDiff ℝ ∞ (Q t)) ∧
      ∀ t x, gradient (Q t) x=A.κ • p t (cylinderGraph period k A.direction x) := by
  obtain ⟨p,hp,ha⟩ := exists_smooth_signed_pressure period hT A B
  have hQ (t : Icc (0 : ℝ) T) := gradientSpace_has_graph_potential period A.κ k hk A.direction
    (commonPressure period hT A B t) (commonPressure_gradient period hT A B t) (p t) (ha t) (hp t)
  choose Q hQs hQ using hQ
  exact ⟨p,Q,hp,ha,hQs,hQ⟩

end EulerAllOrderSmoothPressure
