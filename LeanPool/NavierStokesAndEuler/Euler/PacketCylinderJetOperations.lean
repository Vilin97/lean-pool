/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderSpatialJet
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAdvection
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientData

/-! The literal linear, pressure and nonlinear jet expressions have actual cylinder-path witnesses.
-/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

namespace SpatialJetField

variable {P T : ℝ} [Fact (0 < P)] {J K : Domain → VectorJet}

/-- Slow advection as an element of `Field P T (fun z => EulerPacketPointJets.slowAdvection
(inverse z) (J z) (K z))`. -/
def slowAdvection {inverse : Domain → Space →L[ℝ] Space}
    (A : MatrixCoefficient T inverse) (G : SpatialJetField P T J) (H : SpatialJetField P T K) :
    Field P T (fun z => EulerPacketPointJets.slowAdvection (inverse z) (J z) (K z)) :=
  ((A.multiply G.field).spatialTransport H.field).congr (fun t x θ => by
    change (K (t,(x,θ))).2 (spatialInjection (inverse (t,(x,θ)) (J (t,(x,θ))).1)) =
      fderiv ℝ (fun y => H.raw (t,y)) (x,θ) (inverse (t,(x,θ)) (G.raw (t,(x,θ))),0)
    rw [G.value_eq]
    exact H.spatial_eq t x θ (inverse (t,(x,θ)) (G.raw (t,(x,θ))),0))

/-- Fast advection as an element of `Field P T (fun z => EulerPacketPointJets.fastAdvection
(normal z) (J z) (K z))`. -/
def fastAdvection {normal : VectorField} (N : VectorCoefficient T normal)
    (G : SpatialJetField P T J) (H : SpatialJetField P T K) :
    Field P T (fun z => EulerPacketPointJets.fastAdvection (normal z) (J z) (K z)) :=
  (G.field.angularTransport H.field N.path N.orbit normal N.raw_eq).congr (fun t x θ => by
    change inner ℝ (normal (t,(x,θ))) (J (t,(x,θ))).1 • (K (t,(x,θ))).2 angleDirection =
      inner ℝ (normal (t,(x,θ))) (G.raw (t,(x,θ))) •
        fderiv ℝ (fun y => H.raw (t,y)) (x,θ) (0,1)
    rw [G.value_eq]
    exact congrArg (inner ℝ (normal (t,(x,θ))) (G.raw (t,(x,θ))) • ·)
      (H.spatial_eq t x θ (0,1)))

end SpatialJetField

/-- The actual spatial pressure gradient encoded by the pressure-only jet. -/
def pressureGradient (p : ScalarField) : VectorField := fun z =>
  (toDual ℝ Space).symm ((pressureJet p z).2.comp spatialInjection)

namespace Field

variable {P T : ℝ} [Fact (0 < P)]

/-- Slow pressure, given by `(A.adjoint.multiply G).congr (fun _ _ _ => rfl)`. -/
def slowPressure {inverse : Domain → Space →L[ℝ] Space}
    (A : MatrixCoefficient T inverse) (p : ScalarField) (G : Field P T (pressureGradient p)) :
    Field P T (fun z => EulerPacketPointJets.slowPressure (inverse z) (pressureJet p z)) :=
  (A.adjoint.multiply G).congr (fun _ _ _ => rfl)

/-- The linear time term uses a genuine L² time derivative of the old corrector. -/
def linearPart {strain : Domain → Space →L[ℝ] Space}
    (A : MatrixCoefficient T strain) {raw raw_t : VectorField}
    (G : Field P T raw) (H : Field P T raw_t) (hT : 0 < T)
    (hd : TimeDerivative hT.le G H) (s : Set ℝ) (hs : s = Icc (0 : ℝ) T) :
    Field P T (fun z => EulerPacketPointJets.linearPart (strain z) (slicedJet s raw z)) :=
  (H.add (A.multiply G)).congr (fun t x θ => by
    change (slicedJet s raw (t,(x,θ))).2 timeDirection + strain (t,(x,θ)) (raw (t,(x,θ))) =
      raw_t (t,(x,θ)) + strain (t,(x,θ)) (raw (t,(x,θ)))
    rw [hs,G.slicedJet_temporal hT H hd])

end Field
end EulerPacketCylinderField
