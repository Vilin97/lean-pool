/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderPressureCoherence
public import LeanPool.NavierStokesAndEuler.Euler.GraphPressurePotential
public import LeanPool.NavierStokesAndEuler.Euler.SobolevPointEvaluation
import LeanPool.NavierStokesAndEuler.Euler.AllOrderSmoothPressure
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothPressureRepresentative
import LeanPool.NavierStokesAndEuler.Euler.SobolevJointEvaluation

/-! A canonical, jointly continuous representative of the constructed common signed pressure. -/

@[expose] public section


noncomputable section

namespace EulerCommonPressureRepresentative

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerAllOrderCorrectionData EulerAllOrderCorrectionBudget EulerAllOrderPressureCoherence
  EulerAllOrderSmoothPressure EulerSobolevPointEvaluation EulerSobolevJointEvaluation
  EulerSmoothPressureRepresentative EulerMetricTransport EulerGraphPressurePotential
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- The canonical pointwise pressure, obtained by bounded evaluation of its actual continuous H3
realization. -/
def pointPressure {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  pointEvaluation period x (restrictOperator period (by omega : 3 ≤ 6)
    (signedPressurePath period hT A B 6 le_rfl t))

/-- The canonical pointwise pressure represents the constructed common L² pressure. -/
theorem pointPressure_ae {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) :
    (commonPressure period hT A B t : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      pointPressure period hT A B t :=
  representative_ae period (restrictOperator period (by omega : 3 ≤ 6)
    (signedPressurePath period hT A B 6 le_rfl t))

/-- The canonical pressure is jointly continuous in time and the actual cylinder point. -/
theorem pointPressure_joint_continuous {T : ℝ} (hT : 0 < T) (A : Data period T)
    (B : Budget period hT A) :
    Continuous (fun p : Icc (0 : ℝ) T × LiftDomain period => pointPressure period hT A B p.1 p.2) :=
  path_representative_joint_continuous period
    ((restrictOperator period (by omega : 3 ≤ 6)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (signedPressurePath period hT A B 6 le_rfl))

/-- The canonical pressure is continuous on each spatial slice. -/
theorem pointPressure_continuous {T : ℝ} (hT : 0 < T) (A : Data period T)
    (B : Budget period hT A) (t : Icc (0 : ℝ) T) :
    Continuous (pointPressure period hT A B t) :=
  representative_continuous period (restrictOperator period (by omega : 3 ≤ 6)
    (signedPressurePath period hT A B 6 le_rfl t))

/-- These same canonical representatives are smooth in every spatial coordinate. -/
theorem pointPressure_smooth {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (pointPressure period hT A B t) x) := by
  obtain ⟨g, hg, ha⟩ := exists_smooth_representative period (commonPressure period hT A B t)
    (fun n => pressureJet period hT A B n t)
  have he : pointPressure period hT A B t = g :=
    representative_eq period _ g (smoothField_continuous period g hg) ha
  rw [he]
  exact hg x

omit [Fact (0 < period)] in
/-- The physical phase graph is a continuous map into the periodic cylinder. -/
theorem cylinderGraph_continuous (k : ℝ) (m : Vector3) :
    Continuous (cylinderGraph period k m) := by
  unfold cylinderGraph
  exact continuous_id.prodMk ((AddCircle.continuous_mk' period).comp
    (continuous_const.mul (continuous_const.inner continuous_id)))

/-- The genuine signed graph pressure-gradient vector field. -/
def graphPressure {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (k : ℝ) (t : Icc (0 : ℝ) T) (x : Vector3) : Vector3 :=
  A.κ • pointPressure period hT A B t (cylinderGraph period k A.direction x)

/-- The actual graph pressure-gradient field is jointly continuous in time and space. -/
theorem graphPressure_joint_continuous {T : ℝ} (hT : 0 < T) (A : Data period T)
    (B : Budget period hT A) (k : ℝ) :
    Continuous (graphPressure period hT A B k).uncurry :=
  ((pointPressure_joint_continuous period hT A B).comp
    (continuous_fst.prodMk ((cylinderGraph_continuous period k A.direction).comp
        continuous_snd))).const_smul A.κ

/-- Each actual canonical graph field has a genuine smooth potential by the proved lifted
gradient-space reconstruction. -/
theorem graphPressure_has_potential {T : ℝ} (hT : 0 < T) (A : Data period T)
    (B : Budget period hT A) (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) :
    ∃ q : Vector3 → ℝ, ContDiff ℝ ∞ q ∧
      ∀ x, gradient q x = graphPressure period hT A B k t x :=
  gradientSpace_has_graph_potential period A.κ k hk A.direction
    (commonPressure period hT A B t) (commonPressure_gradient period hT A B t)
    (pointPressure period hT A B t) (pointPressure_ae period hT A B t)
    (pointPressure_smooth period hT A B t)

end EulerCommonPressureRepresentative
