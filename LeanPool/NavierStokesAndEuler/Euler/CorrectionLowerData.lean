/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation
public import LeanPool.NavierStokesAndEuler.Euler.TimeCorrectionRestriction
import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionSplit

/-! The actual lower Sobolev equation and its continuous source and pressure paths. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionLowerData

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerCorrectionOperators
      EulerQuadraticSource
  EulerTimeCorrectionSource EulerGevreyOrderZero EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A local normed-group instance for the concrete lower Sobolev scale. -/
local instance lowerDataGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance

/-- A local real normed-space instance for the concrete lower Sobolev scale. -/
local instance lowerDataSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The same genuine correction coefficients and background restricted by one Sobolev order. -/
def lowerData {q : ℕ} {T : ℝ} (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t))) :
    CorrectionData period q (Icc (0 : ℝ) T) where
  κ := D.κ
  direction := D.direction
  scale_bound := D.scale_bound
  direction_bound := D.direction_bound
  metric := ⟨D.metric.coefficient, KG, hG⟩
  coercivity := D.coercivity
  coercivity_pos := D.coercivity_pos
  metric_pos := D.metric_pos
  linear := ⟨D.linear.coefficient, KL, hL⟩
  quadratic i := ⟨(D.quadratic i).coefficient, KQ i, hQ i⟩
  approximation := (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      D.approximation
  residual := (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) D.residual

/-- The actual nonlinear raw source along a continuous Sobolev path is continuous. -/
def rawPath {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, SobolevSpace period q) :=
  ⟨fun t => D.rawSource period hq t (e t),
    (((D.coefficients period hq).forcing.continuous.add
      ((D.coefficients period hq).linear.continuous.clm_apply e.continuous)).add
      (((D.coefficients period hq).quadratic.continuous.clm_apply e.continuous).clm_apply
          e.continuous))⟩

/-- The actual projected nonlinear mild forcing along the continuous solution. -/
def forcingPath {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, SobolevSpace period q) :=
  ⟨fun t => (D.coefficients period hq).apply t (e t),
    ((D.coefficients period hq).projection.continuous.clm_apply (rawPath period hq D
        e).continuous).neg⟩

/-- The actual signed coercive pressure along the continuous solution is continuous. -/
def pressurePath {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, SobolevSpace period q) :=
  ⟨fun t => D.pressure period hq t (e t),
    ((positivePressurePath period T D.metric D.κ D.direction D.coercivity D.coercivity_pos
        D.metric_pos).continuous.clm_apply
      (rawPath period hq D e).continuous).neg⟩

/-- The actual lower raw source is exactly the lower restriction used by the constructed Bochner
source. -/
theorem rawPath_lower {q : ℕ} (hq : 6 ≤ q) {T : ℝ}
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    rawPath period hq (lowerData period D KG KL KQ hG hL hQ) e t =
      lowerRawValue period hq T (EulerSobolevTransport.velocityComponents D.κ D.direction)
        (EulerSobolevTransport.velocityComponents_norm D.κ D.direction D.scale_bound
            D.direction_bound)
        D.linear D.quadratic KL KQ D.approximation D.residual e t :=
  correctionData_rawSource_split period (lowerData period D KG KL KQ hG hL hQ) hq t (e t)

/-- The actual continuous pressure path lies in the genuine lifted gradient space at every time. -/
theorem pressurePath_gradient {q : ℕ} (hq : 6 ≤ q) {T : ℝ}
    (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    value period (pressurePath period hq D e t) ∈ gradientSpace period D.κ D.direction :=
  D.pressure_mem_gradient period hq t (e t)

end EulerCorrectionLowerData
