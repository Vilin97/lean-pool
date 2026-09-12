/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCoefficientTower
public import LeanPool.NavierStokesAndEuler.Euler.PacketMatrixCoefficientAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing

/-! The correction coefficients constructed from the prescribed deformation.
The order-zero terms have the positive sign of the transformed equation;
the correction source subsequently applies the negative pressure projection. -/

@[expose] public section


noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set ContinuousLinearMap EulerSmoothLimit EulerPacketPointJets
  EulerPacketCylinderField EulerMeanCoefficients EulerLiftedGradientSpace
  EulerAllOrderCorrectionData

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)

/-- Raw frame, given by `D.F.field (D.clamp z.1) z.2.1`. -/
def rawFrame (z : Domain) : Space →L[ℝ] Space :=
  D.F.field (D.clamp z.1) z.2.1

/-- Raw frame time, given by `D.F₁.field (D.clamp z.1) z.2.1`. -/
def rawFrameTime (z : Domain) : Space →L[ℝ] Space :=
  D.F₁.field (D.clamp z.1) z.2.1

/-- Raw inverse, given by `D.FInv.field (D.clamp z.1) z.2.1`. -/
def rawInverse (z : Domain) : Space →L[ℝ] Space :=
  D.FInv.field (D.clamp z.1) z.2.1

/-- Frame coefficient, bundling `path`, `orbit`, `raw_eq`. -/
def frameCoefficient : MatrixCoefficient D.T (rawFrame D) where
  path := D.F.field
  orbit := D.F.translation_contDiff
  raw_eq t x θ := by simp only [rawFrame,EulerTransversePacketProvider.Data.clamp_coe]

/-- Frame time coefficient, bundling `path`, `orbit`, `raw_eq`. -/
def frameTimeCoefficient : MatrixCoefficient D.T (rawFrameTime D) where
  path := D.F₁.field
  orbit := D.F₁.translation_contDiff
  raw_eq t x θ := by simp only [rawFrameTime,EulerTransversePacketProvider.Data.clamp_coe]

/-- Inverse coefficient, bundling `path`, `orbit`, `raw_eq`. -/
def inverseCoefficient : MatrixCoefficient D.T (rawInverse D) where
  path := D.FInv.field
  orbit := D.FInv.translation_contDiff
  raw_eq t x θ := by simp only [rawInverse,EulerTransversePacketProvider.Data.clamp_coe]

/-- Raw metric, given by `(rawInverse D z).comp (rawInverse D z).adjoint`. -/
def rawMetric (z : Domain) : Space →L[ℝ] Space :=
  (rawInverse D z).comp (rawInverse D z).adjoint

/-- Raw inverse metric, given by `(rawFrame D z).adjoint.comp (rawFrame D z)`. -/
def rawInverseMetric (z : Domain) : Space →L[ℝ] Space :=
  (rawFrame D z).adjoint.comp (rawFrame D z)

/-- Raw linear, given by `(2 : ℝ) • (rawInverse D z).comp (rawFrameTime D z)`. -/
def rawLinear (z : Domain) : Space →L[ℝ] Space :=
  (2 : ℝ) • (rawInverse D z).comp (rawFrameTime D z)

/-- Raw quadratic, given by `κ • (rawInverse D z).comp (fderiv ℝ (fun x => rawFrame D
(z.1,(x,z.2.2))) z.2.1 (EuclideanSpace.single i 1))`. -/
def rawQuadratic (κ : ℝ) (i : Fin 3) (z : Domain) : Space →L[ℝ] Space :=
  κ • (rawInverse D z).comp
    (fderiv ℝ (fun x => rawFrame D (z.1,(x,z.2.2))) z.2.1
      (EuclideanSpace.single i 1))

/-- Metric coefficient, given by `(inverseCoefficient D).comp (inverseCoefficient D).adjoint`. -/
def metricCoefficient : MatrixCoefficient D.T (rawMetric D) :=
  (inverseCoefficient D).comp (inverseCoefficient D).adjoint

/-- Inverse metric coefficient, given by `(frameCoefficient D).adjoint.comp (frameCoefficient
D)`. -/
def inverseMetricCoefficient : MatrixCoefficient D.T (rawInverseMetric D) :=
  (frameCoefficient D).adjoint.comp (frameCoefficient D)

/-- Linear coefficient, given by `((inverseCoefficient D).comp (frameTimeCoefficient D)).smul
2`. -/
def linearCoefficient : MatrixCoefficient D.T (rawLinear D) :=
  ((inverseCoefficient D).comp (frameTimeCoefficient D)).smul 2

/-- Quadratic coefficient, given by `((inverseCoefficient D).comp ((frameCoefficient
D).spatialDerivative (EuclideanSpace.single i 1))).smul κ`. -/
def quadraticCoefficient (κ : ℝ) (i : Fin 3) : MatrixCoefficient D.T (rawQuadratic D κ i) :=
  ((inverseCoefficient D).comp
    ((frameCoefficient D).spatialDerivative (EuclideanSpace.single i 1))).smul κ

@[simp] theorem metricCoefficient_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (metricCoefficient D).path t x =
      (D.FInv.field t x).comp (D.FInv.field t x).adjoint := rfl

@[simp] theorem inverseMetricCoefficient_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (inverseMetricCoefficient D).path t x =
      (D.F.field t x).adjoint.comp (D.F.field t x) := rfl

@[simp] theorem linearCoefficient_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (linearCoefficient D).path t x =
      (2 : ℝ) • (D.FInv.field t x).comp (D.F₁.field t x) := rfl

theorem quadraticCoefficient_apply (κ : ℝ) (i : Fin 3)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    (quadraticCoefficient D κ i).path t x =
      κ • (D.FInv.field t x).comp
        (fderiv ℝ (D.F.field t : Space → Space →L[ℝ] Space) x
          (EuclideanSpace.single i 1)) := by
  change κ • (D.FInv.field t x).comp
    (((frameCoefficient D).spatialDerivative (EuclideanSpace.single i 1)).path t x) = _
  rw [MatrixCoefficient.spatialDerivative_path_apply]
  rfl

variable (P : ℝ) [Fact (0 < P)]

/-- Metric tower, given by `(metricCoefficient D).toCoefficientTower P`. -/
def metricTower : CoefficientTower P D.T :=
  (metricCoefficient D).toCoefficientTower P

/-- Inverse metric tower, given by `(inverseMetricCoefficient D).toCoefficientTower P`. -/
def inverseMetricTower : CoefficientTower P D.T :=
  (inverseMetricCoefficient D).toCoefficientTower P

/-- Linear tower, given by `(linearCoefficient D).toCoefficientTower P`. -/
def linearTower : CoefficientTower P D.T :=
  (linearCoefficient D).toCoefficientTower P

/-- Quadratic tower, given by `(quadraticCoefficient D κ i).toCoefficientTower P`. -/
def quadraticTower (κ : ℝ) (i : Fin 3) : CoefficientTower P D.T :=
  (quadraticCoefficient D κ i).toCoefficientTower P

@[simp] theorem metricTower_apply (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ((metricTower D P).coefficient t).coefficient x =
      (D.FInv.field t x.1).comp (D.FInv.field t x.1).adjoint := rfl

@[simp] theorem inverseMetricTower_apply (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ((inverseMetricTower D P).coefficient t).coefficient x =
      (D.F.field t x.1).adjoint.comp (D.F.field t x.1) := rfl

@[simp] theorem linearTower_apply (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ((linearTower D P).coefficient t).coefficient x =
      (2 : ℝ) • (D.FInv.field t x.1).comp (D.F₁.field t x.1) := rfl

theorem quadraticTower_apply (κ : ℝ) (i : Fin 3)
    (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ((quadraticTower D P κ i).coefficient t).coefficient x =
      κ • (D.FInv.field t x.1).comp
        (fderiv ℝ (D.F.field t : Space → Space →L[ℝ] Space) x.1
          (EuclideanSpace.single i 1)) :=
  quadraticCoefficient_apply D κ i t x.1

theorem metricTower_continuous :
    Continuous (fun t => ((metricTower D P).coefficient t).operator) :=
  MatrixCoefficient.toCoefficientTower_operator_continuous P (metricCoefficient D)

theorem inverseMetricTower_continuous :
    Continuous (fun t => ((inverseMetricTower D P).coefficient t).operator) :=
  MatrixCoefficient.toCoefficientTower_operator_continuous P (inverseMetricCoefficient D)

end EulerPacketCorrectionCoefficients
