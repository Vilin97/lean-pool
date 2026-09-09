/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyReconstruction
public import LeanPool.NavierStokesAndEuler.Euler.InviscidSobolevEvolution
public import LeanPool.NavierStokesAndEuler.Euler.SobolevPointMultiplication

@[expose] public section

/-! Genuine pointwise time differentiation of the generically assembled correction. -/

noncomputable section

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerAllOrderCorrectionData
  EulerCorrectionOperators EulerVolterraConvolution EulerSobolevPointEvaluation
  EulerSobolevJointEvaluation EulerSobolevPointMultiplication EulerSobolevCoefficientPressure
  EulerQuadraticSourceLimit EulerInviscidSobolevEvolution

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The canonical pointwise nonlinear raw source of the actual common correction. -/
def FiniteFamily.pointRawSource (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  pointEvaluation period x (restrictOperator period (by omega : 3 ≤ 6)
    (F.rawSourcePath period 6 le_rfl t))

/-- The canonical actual time derivative, defined by bounded evaluation of the genuine continuous Sobolev source. -/
def FiniteFamily.pointTimeDerivative (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  pointEvaluation period x (restrictOperator period (by omega : 3 ≤ 6)
    (((A.atOrder period 6).coefficients period le_rfl).apply t (F.solution 6 le_rfl t)))

/-- The actual pointwise time derivative is jointly continuous in time and space. -/
theorem FiniteFamily.pointTimeDerivative_joint_continuous (F : FiniteFamily period hT A) :
    Continuous (F.pointTimeDerivative period).uncurry :=
  path_representative_joint_continuous period
    ((restrictOperator period (by omega : 3 ≤ 6)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (sourcePath ((A.atOrder period 6).coefficients period le_rfl) (F.solution 6 le_rfl)))

/-- The pointwise time derivative is the literal raw-source and signed-pressure expression. -/
theorem FiniteFamily.pointTimeDerivative_eq_pressure (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    F.pointTimeDerivative period t x = -F.pointRawSource period t x -
      (A.metric.coefficient t).coefficient x (F.pointPressure period t x) := by
  unfold FiniteFamily.pointTimeDerivative
  rw [EulerInviscidSobolevEvolution.CorrectionData.source_sobolev]
  simp only [map_sub, map_neg]
  rw [pointEvaluation_coefficient period (by omega : 3 ≤ 6) ((A.atOrder period
    6).metric.coefficient t)
    ((A.atOrder period 6).metric.jet t)]
  rfl

/-- The canonical common field has its genuine pointwise first time derivative at every interior time. -/
theorem FiniteFamily.pointField_hasDerivAt (F : FiniteFamily period hT A)
    (x : LiftDomain period) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => F.pointField period (projIcc 0 T hT.le r) x)
      (F.pointTimeDerivative period ⟨t, ht.1.le, ht.2.le⟩ x) t := by
  have hd := sobolev_hasDerivAt period T hT.le
    ((A.atOrder period 6).coefficients period le_rfl) (F.solution 6 le_rfl)
    (F.equation 6 le_rfl) t ht
  have he := (((pointEvaluation period x).comp (restrictOperator period (by omega : 3 ≤
    6))).hasFDerivAt).comp_hasDerivAt t hd
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, restrictOperator_truncate,
    FiniteFamily.pointField, FiniteFamily.pointTimeDerivative, extendPath] using he

/-- The actual pointwise correction equation uses the reconstructed signed pressure and literal matrix multiplication. -/
theorem FiniteFamily.pointField_hasDerivAt_pressure (F : FiniteFamily period hT A)
    (x : LiftDomain period) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => F.pointField period (projIcc 0 T hT.le r) x)
      (-F.pointRawSource period ⟨t, ht.1.le, ht.2.le⟩ x -
        (A.metric.coefficient ⟨t, ht.1.le, ht.2.le⟩).coefficient x
          (F.pointPressure period ⟨t, ht.1.le, ht.2.le⟩ x)) t := by
  simpa only [F.pointTimeDerivative_eq_pressure period] using F.pointField_hasDerivAt period x t ht

end EulerCorrectionAssembly
