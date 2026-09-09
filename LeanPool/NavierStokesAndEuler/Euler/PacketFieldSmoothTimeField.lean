/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTensorBounds
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldAlgebra

@[expose] public section

/-! The actual finite packet fields supply bounded smooth cover
coefficients. Their fixed-Hq word bounds give uniform tensor-jet bounds,
with a single fixed coordinate radius conversion. -/

noncomputable section


namespace EulerPacketCylinderField.Field

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerCylinderSmoothTimeField EulerCylinderCoordinates EulerCylinderSobolevSpace
  EulerPacketProfileRecursion EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {P T : ℝ} [Fact (0 < P)] {raw raw_t : VectorField}

private local instance (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance

def toSmoothTimeField (G : Field P T raw) : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  ofPath P G.path G.orbit

theorem toSmoothTimeField_apply (G : Field P T raw) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    G.toSmoothTimeField.field t x = raw (t,x) := (G.raw_eq t x.1 x.2).symm

theorem toSmoothTimeField_timeDerivative (G : Field P T raw) (H : Field P T raw_t)
    (hT : 0 ≤ T) (hd : TimeDerivative hT G H) :
    SmoothTimeField.TimeDerivative T hT G.toSmoothTimeField H.toSmoothTimeField := by
  intro t x
  exact pointField_hasDerivWithinAt P T hT G.path H.path G.orbit H.orbit hd t (coveringMap P x)

theorem toSmoothTimeField_map_jet (G : Field P T raw) (L : Space →L[ℝ] Space) (n : ℕ) :
    (G.map L).toSmoothTimeField.jet n = (G.toSmoothTimeField.map L).jet n := by
  apply SmoothTimeField.jet_eq_of_field_eq
  intro t x
  rw [(G.map L).toSmoothTimeField_apply, SmoothTimeField.map_apply, G.toSmoothTimeField_apply]

theorem WordBound.toSmoothTimeField_jet_bound {G : Field P T raw} {q : ℕ} {R A : ℝ}
    (hG : G.WordBound q R A 0) (hq : 3 ≤ q) (hR : 0 ≤ R) (hA : 0 ≤ A) (n : ℕ) :
    ‖G.toSmoothTimeField.jet n‖ ≤ (sobolevEmbeddingConstant P 3*A) *
      (‖coordinateEquiv.symm.toContinuousLinearMap‖*R)^n * (n.factorial : ℝ)^2 := by
  have hS := sobolevEmbeddingConstant_nonneg P 3
  apply ofPath_jet_norm_le P G.path G.orbit n _ (by positivity)
  intro t x
  have he : (fun y => pointField P G.path G.orbit t (coveringMap P y)) =
      fun y => raw (t,y) := funext (fun y => (G.raw_eq t y.1 y.2).symm)
  rw [he]
  apply (hG.raw_tensor_le hq t n x).trans_eq
  simp only [majorant, Nat.add_zero, mul_pow]
  ring

end EulerPacketCylinderField.Field
