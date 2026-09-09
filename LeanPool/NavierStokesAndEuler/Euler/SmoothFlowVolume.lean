/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJacobian
public import LeanPool.NavierStokesAndEuler.Euler.LinearEvolutionDeterminant

@[expose] public section

/-! The actual flow of a trace-free smooth bounded velocity preserves its
Jacobian determinant and Haar volume, in every finite dimension. -/

noncomputable section


namespace EulerSmoothBanachFlow

open Set MeasureTheory EulerLinearDuhamel

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)
  (hdiv : ∀ t x, LinearMap.trace ℝ E (fderiv ℝ (A.field t : E → E) x).toLinearMap = 0)

include hdiv in
theorem jacobianEvolution_det_one (t : Icc (0 : ℝ) T) (x : E) :
    ((jacobianEvolution T hT A x).forward t).det = 1 := by
  apply constructedEvolution_det_one
  intro s
  change LinearMap.trace ℝ E (A.derivativeField s (pathFamily T hT A x s)).toLinearMap = 0
  rw [A.derivativeField_eq]
  exact hdiv s _

include hdiv in
theorem forward_det_one (t : Icc (0 : ℝ) T) (x : E) :
    (fderiv ℝ (fun y => (flowData T hT A).forward t y) x).det = 1 := by
  rw [forward_fderiv]
  exact jacobianEvolution_det_one T hT A hdiv t x

variable [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

include hdiv in
theorem forward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving ((flowData T hT A).forward t) μ μ := by
  apply EulerDeformationVolume.measurePreserving_of_det_one μ
    ((flowData T hT A).forward t) (fun x => (jacobianEvolution T hT A x).forward t)
    (forward_hasFDerivAt_label T hT A t)
  · exact ((flowData T hT A).flowHomeomorph 0 t).bijective
  · exact jacobianEvolution_det_one T hT A hdiv t

include hdiv in
theorem backward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving ((flowData T hT A).backward t) μ μ := by
  let e := (flowData T hT A).flowHomeomorph 0 t
  have hm : MeasurePreserving e.toMeasurableEquiv μ μ :=
    forward_measurePreserving T hT A hdiv μ t
  exact MeasurePreserving.symm e.toMeasurableEquiv hm

end EulerSmoothBanachFlow
