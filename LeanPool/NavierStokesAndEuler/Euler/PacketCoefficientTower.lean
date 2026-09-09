/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientData
public import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathSobolev

@[expose] public section

/-! Actual packet matrix coefficients provide the complete coefficient
towers required by the all-order nonlinear correction construction. -/

noncomputable section

namespace EulerPacketCylinderField.MatrixCoefficient

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevCoefficientPressure EulerCoefficientPath EulerLpCylinderRectangular
  EulerPacketPointJets

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {raw : Domain → Space →L[ℝ] Space}

def toCoefficientTower (A : MatrixCoefficient T raw) :
    EulerAllOrderCorrectionData.CoefficientTower P T where
  coefficient := smoothCoefficient P A.path A.orbit
  jet q t := coefficientJet P A.path A.orbit q t
  continuous q := sobolevOperator_continuous P A.path A.orbit q

@[simp] theorem toCoefficientTower_coefficient (A : MatrixCoefficient T raw)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    ((A.toCoefficientTower P).coefficient t).coefficient x = A.path t x.1 := rfl

theorem toCoefficientTower_raw (A : MatrixCoefficient T raw)
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    ((A.toCoefficientTower P).coefficient t).coefficient (x,(θ : AddCircle P)) =
      raw (t,(x,θ)) := (A.raw_eq t x θ).symm

theorem toCoefficientTower_operator (A : MatrixCoefficient T raw)
    (t : Icc (0 : ℝ) T) :
    ((A.toCoefficientTower P).coefficient t).operator = fullOperatorMap P (A.path t) :=
  smoothCoefficient_operator P A.path A.orbit t

theorem toCoefficientTower_operator_continuous (A : MatrixCoefficient T raw) :
    Continuous (fun t => ((A.toCoefficientTower P).coefficient t).operator) :=
  smoothCoefficient_operator_continuous P A.path A.orbit

theorem toCoefficientTower_sobolev_value (A : MatrixCoefficient T raw)
    (q : ℕ) (t : Icc (0 : ℝ) T) (u : SobolevSpace P q) :
    value P (coefficientSobolevOperator P ((A.toCoefficientTower P).jet q t) u) =
      fullOperatorMap P (A.path t) (value P u) := by
  rw [coefficientSobolevOperator_value]
  exact congrArg (fun L => L (value P u)) (toCoefficientTower_operator P A t)

end EulerPacketCylinderField.MatrixCoefficient
