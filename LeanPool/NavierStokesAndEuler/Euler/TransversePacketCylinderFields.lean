/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorSupport
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField

@[expose] public section

/-! Actual cylinder-path witnesses for the constructed transverse solution and corrector. -/

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketCylinderField
  EulerCylinderSmoothOrbit EulerLpCylinderPaths

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

def vectorField : Field P D.T (G.vector I) where
  path := G.fullVelocityPath I
  orbit := G.velocityPath_orbit I
  raw_eq t x θ := by
    change pointField P (G.fullVelocityPath I) (G.velocityPath_orbit I)
      (D.clamp t) (x,(θ : AddCircle P)) = _
    rw [Data.clamp_coe]

def vectorDerivativeField : Field P D.T (G.vectorDerivative I) where
  path := G.fullDerivativePath I
  orbit := G.derivativePath_orbit I
  raw_eq t x θ := by
    change pointField P (G.fullDerivativePath I) (G.derivativePath_orbit I)
      (D.clamp t) (x,(θ : AddCircle P)) = _
    rw [Data.clamp_coe]

theorem vectorField_time : TimeDerivative D.T_pos.le (G.vectorField I) (G.vectorDerivativeField I)
  :=
  G.fullVelocityPath_time I

def correctorField : Field P D.T (G.corrector I) where
  path := G.correctorPath I
  orbit := G.correctorPath_orbit I
  raw_eq t x θ := by
    change pointField P (G.correctorPath I) (G.correctorPath_orbit I)
      (D.clamp t) (x,(θ : AddCircle P)) = _
    rw [Data.clamp_coe]

def correctorDerivativeField : Field P D.T (G.correctorDerivative I) where
  path := G.correctorTimePath I
  orbit := G.correctorTimePath_orbit I
  raw_eq t x θ := by
    change pointField P (G.correctorTimePath I) (G.correctorTimePath_orbit I)
      (D.clamp t) (x,(θ : AddCircle P)) = _
    rw [Data.clamp_coe]

theorem correctorField_time :
    TimeDerivative D.T_pos.le (G.correctorField I) (G.correctorDerivativeField I) :=
  G.correctorPath_time I

theorem vectorField_supported (t : Icc (0 : ℝ) D.T) :
    (G.vectorField I).path t ∈ Supported P Space D.support D.support_measurable :=
  (G.velocityPath I t).property

theorem vectorDerivativeField_supported (t : Icc (0 : ℝ) D.T) :
    (G.vectorDerivativeField I).path t ∈ Supported P Space D.support D.support_measurable :=
  (G.derivativePath I t).property

theorem correctorField_supported (t : Icc (0 : ℝ) D.T) :
    (G.correctorField I).path t ∈ Supported P Space D.support D.support_measurable :=
  G.correctorPath_supported I t

theorem correctorDerivativeField_supported (t : Icc (0 : ℝ) D.T) :
    (G.correctorDerivativeField I).path t ∈ Supported P Space D.support D.support_measurable :=
  G.correctorTimePath_supported I t

end EulerTransversePacketProvider.Forcing
