/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionMetric
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTower

/-! Actual all-order correction data from the source deformation and two
prescribed packet fields. No correction solution or energy budget is assumed. -/

@[expose] public section


noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketCylinderField
  EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerPacketProfileRecursion

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]

/-- Correction data, bundling `κ`, `direction`, `scale_bound`, `direction_bound` and the
required compatibility proofs. -/
def correctionData (κ : ℝ) (hκ : |κ| ≤ 1)
    (approximation residual : FieldTower P D.T) : Data P D.T where
  κ := κ
  direction := D.m₀
  scale_bound := hκ
  direction_bound := D.m₀_unit.le
  metric := metricTower D P
  metric_continuous := metricTower_continuous D P
  coercivity := D.normalLower
  coercivity_pos := D.normalLower_pos
  metric_pos := metricTower_coercive D P
  linear := linearTower D P
  quadratic := quadraticTower D P κ
  approximation := approximation
  residual := residual

/-- Correction data of fields, given by `correctionData D P κ hκ Z.toFieldTower G.toFieldTower`. -/
def correctionDataOfFields (κ : ℝ) (hκ : |κ| ≤ 1)
    {z r : VectorField} (Z : Field P D.T z) (G : Field P D.T r) : Data P D.T :=
  correctionData D P κ hκ Z.toFieldTower G.toFieldTower

@[simp] theorem correctionDataOfFields_approximation (κ : ℝ) (hκ : |κ| ≤ 1)
    {z r : VectorField} (Z : Field P D.T z) (G : Field P D.T r) :
    (correctionDataOfFields D P κ hκ Z G).approximation.field = Z.path := rfl

@[simp] theorem correctionDataOfFields_residual (κ : ℝ) (hκ : |κ| ≤ 1)
    {z r : VectorField} (Z : Field P D.T z) (G : Field P D.T r) :
    (correctionDataOfFields D P κ hκ Z G).residual.field = G.path := rfl

@[simp] theorem correctionData_metric (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    (((correctionData D P κ hκ Z G).metric).coefficient t).coefficient x =
      (D.FInv.field t x.1).comp (D.FInv.field t x.1).adjoint := rfl

@[simp] theorem correctionData_linear (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    (((correctionData D P κ hκ Z G).linear).coefficient t).coefficient x =
      (2 : ℝ) • (D.FInv.field t x.1).comp (D.F₁.field t x.1) := rfl

theorem correctionData_quadratic (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (i : Fin 3) (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    (((correctionData D P κ hκ Z G).quadratic i).coefficient t).coefficient x =
      κ • (D.FInv.field t x.1).comp
        (fderiv ℝ (D.F.field t : Space → Space →L[ℝ] Space) x.1
          (EuclideanSpace.single i 1)) :=
  quadraticTower_apply D P κ i t x

end EulerPacketCorrectionCoefficients
