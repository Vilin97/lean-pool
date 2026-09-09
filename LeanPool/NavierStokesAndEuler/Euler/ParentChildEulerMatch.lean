/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketExactPressure

/-! The new parent is the particle map of the actual corrected Euler
velocity, and its acceleration is minus the actual constructed pressure
force. Both matches are derived from the existing parent law and Euler. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerLagrangian

variable (A : EulerParentPacketFrames.Parent)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)


variable {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos (correctionData (A.transverseData m hm J support
      hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z = V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A = B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k * κ = 1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (Y : Icc (0 : ℝ) A.T → Space → Space)
  (hYX : ∀ t x, Y t (A.position t x) = x)
  (hXY : ∀ t x, A.position t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
  (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
  (force : Icc (0 : ℝ) A.T → Space → Space)
  (hforce : Continuous (Function.uncurry force))
  (hgradient : ∀ (t : Icc (0 : ℝ) A.T) x, gradient (fun y => p (t, y)) x = force t x)
  (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x = u (t, A.position t x))
  (hu : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ u (t, x))
  (hp : ∀ (t : Icc (0 : ℝ) A.T) x, DifferentiableAt ℝ (fun y => p (t, y)) x)
  (heuler : ∀ t ∈ Ioo 0 A.T, ∀ x, momentumResidual u p (t, x) = 0)

include hV hG hYX hvelocity in
theorem child_velocity_exact (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).velocity.field t x =
      A.exactPacketVelocity m hm J support hSupport B residual k Y u
        (t,(A.child G k m hgraph nextEll hnext hnext1).position t x) := by
  have h := A.child_velocity_corrected B V hV G hG k hgraph nextEll hnext hnext1
    Y (fun s y => u (s,y)) hYX hvelocity t x
  exact h.trans
    (A.exactPacketVelocity_eq_corrected m hm J support hSupport B residual k Y u t
      ((A.child G k m hgraph nextEll hnext hnext1).position t x)).symm

include hV hG hk hYX hXY hY hforce hgradient hvelocity hu hp heuler in
theorem child_acceleration_exact (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).acceleration.field t x =
      -A.exactPacketForce m hm J support hSupport B residual k Y force t
        ((A.child G k m hgraph nextEll hnext hnext1).position t x) := by
  apply (A.child G k m hgraph nextEll hnext hnext1).acceleration_physical_of_euler
    (A.exactPacketVelocity m hm J support hSupport B residual k Y u)
    (A.exactPacketPressure m hm J support hSupport B residual k Y p)
    (A.exactPacketForce m hm J support hSupport B residual k Y force)
    (A.exactPacketForce_continuous m hm J support hSupport B residual k Y force hY hforce)
    (A.exactPacketPressure_gradient m hm J support hSupport B residual k hk Y hXY hY p force hp
        hgradient)
    (A.child_velocity_exact m hm J support hSupport B residual V hV G hG k hgraph
      nextEll hnext hnext1 Y hYX u hvelocity)
    (A.exactPacketVelocity_differentiableAt m hm J support hSupport B residual k Y hYX hXY hY u hu)
    (A.exactPacket_momentum m hm J support hSupport B residual k hk Y hYX hXY hY u p hvelocity hu
        hp heuler)
    t x

end EulerParentPacketFrames.Parent
