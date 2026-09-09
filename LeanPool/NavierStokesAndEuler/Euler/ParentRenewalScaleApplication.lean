/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalScaleCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds

/-! The fixed scalar envelope bounds the literal lowGeometry of both
source branches. Its inputs are the existing frame and neighbor costs,
with no assumed estimate for the new coupling or tilt. -/

@[expose] public section


noncomputable section

namespace EulerParentRenewalScale

open EulerPacketMovingFrame EulerPacketSourceScaleChoice

theorem sigma_mul_le_two {σ x : ℝ} (h : σ ^ 2 * x ^ 2 ≤ 2) : σ*x ≤ 2 := by
  nlinarith only [h,sq_nonneg (σ*x-2)]

theorem tilt_small_of_cost {ι : Type*} (G : PhysicalGeometryData ι)
    {cost : ℕ → ℝ} {η : ℝ} (n : ℕ) (hs : SmallSeries cost η)
    (hη : η ≤ 1 / 2) (h : G.tiltError ≤ cost n) : G.tiltError ≤ 1/2 :=
  h.trans ((hs.term_le n).trans hη)

/-- Apply this to the matching certificate proved by either actual
target-renewal constructor. It supplies exactly the finite-prefix step. -/
theorem literal_step {ι : Type*} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {D : EulerTransversePacketProvider.Data V} {G : PhysicalGeometryData ι}
    {Q : EulerPacketSourceGeometry.ParentFrame D G.targetTime}
    (H : EulerParentPacketFrames.RenewalAtTarget G Q)
    (J : ℕ) (X : ℝ) (n : ℕ) {cost : ℕ → ℝ} {η : ℝ}
    (hs : SmallSeries cost η) (hη : η ≤ 1 / 2)
    (hcost : G.couplingError ≤ cost n ∧ G.tiltError ≤ cost n)
    (hy : G.y = (scaleSequence J X (n + 1))⁻¹) :
    |Q.a/G.a-1| ≤ cost n ∧
      (1/2 ≤ Q.sigma^2*(scaleSequence J X (n+1))^2 ∧
        Q.sigma^2*(scaleSequence J X (n+1))^2 ≤ 2) := by
  have ht := tilt_small_of_cost G n hs hη hcost.2
  have hi := H.tilt_interval ht
  rw [hy,inv_inv] at hi
  refine ⟨H.coupling_error.trans hcost.1,?_,?_⟩ <;> nlinarith only [hi.1,hi.2]

end EulerParentRenewalScale

namespace EulerPacketSourceGeometry.Guards

open Set EulerSmoothLimit EulerPacketMovingFrame EulerTransversePacketProvider
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketSourceScaleActual
  EulerPacketSourceScales EulerParentRenewalScale

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)} (A : Guards hτ hτT P H)
  (hball : (1 / 2 : ℝ) ≤ A.radius)

theorem renewal_errors_on_scales
    (J D0 : ℕ) (hJ : 2 ≤ J) (C c CF X a : ℝ) (hC : 1 ≤ C) (hCF : 1 ≤ CF)
    (hX : 1 ≤ X) (ha : a ≤ 2) (n : ℕ)
    (haMatch : P.a = a) (hShear : P.shear = previousShear J X n)
    (hTheta : P.horizon ≤ sourceTheta J C (scaleSequence J X) n)
    (hG : P.G ≤ CF * (1 + olderShear J X n))
    (hError : P.error ≤ priorError J D0 X n)
    (hNeighbor : P.neighborCost hτ hτT H A.CM A.CH * A.radius ≤ neighborError J D0 X c n)
    (hY : A.y = (scaleSequence J X (n + 1))⁻¹)
    (hSigma : P.sigma ^ 2 * (scaleSequence J X n) ^ 2 ≤ 2) :
    (A.lowGeometry hball).couplingError ≤ renewalCost J D0 C c CF X n ∧
      (A.lowGeometry hball).tiltError ≤ renewalCost J D0 C c CF X n := by
  apply actual_errors_le_cost (A.lowGeometry hball) J D0 hJ C c CF X a hC hCF hX ha n
  · change P.epsilon=epsilon J X a n
    simp only [ParentFrame.epsilon,epsilon,haMatch,hShear]
  · exact hTheta
  · exact hG
  · exact add_le_add hError hNeighbor
  · exact hY
  · exact sigma_mul_le_two hSigma

end EulerPacketSourceGeometry.Guards

namespace EulerPacketSourceGeometry.ForwardGuards

open Set EulerSmoothLimit EulerPacketMovingFrame EulerTransversePacketProvider
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketSourceScaleActual
  EulerPacketSourceScales EulerParentRenewalScale

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {P : ParentFrame D 0} (A : ForwardGuards P)
  (hball : (1 / 2 : ℝ) ≤ A.radius)

theorem renewal_errors_on_scales
    (J D0 : ℕ) (hJ : 2 ≤ J) (C c CF X a : ℝ) (hC : 1 ≤ C) (hCF : 1 ≤ CF)
    (hX : 1 ≤ X) (ha : a ≤ 2) (n : ℕ)
    (haMatch : P.a = a) (hShear : P.shear = previousShear J X n)
    (hTheta : P.horizon ≤ sourceTheta J C (scaleSequence J X) n)
    (hG : P.G ≤ CF * (1 + olderShear J X n))
    (hError : P.error ≤ priorError J D0 X n)
    (hNeighbor : ‖D.M.derivative.field‖ * A.radius ≤ neighborError J D0 X c n)
    (hY : A.y = (scaleSequence J X (n + 1))⁻¹)
    (hSigma : P.sigma ^ 2 * (scaleSequence J X n) ^ 2 ≤ 2) :
    (A.lowGeometry hball).couplingError ≤ renewalCost J D0 C c CF X n ∧
      (A.lowGeometry hball).tiltError ≤ renewalCost J D0 C c CF X n := by
  apply actual_errors_le_cost (A.lowGeometry hball) J D0 hJ C c CF X a hC hCF hX ha n
  · change P.epsilon=epsilon J X a n
    simp only [ParentFrame.epsilon,epsilon,haMatch,hShear]
  · exact hTheta
  · exact hG
  · exact add_le_add hError hNeighbor
  · exact hY
  · exact sigma_mul_le_two hSigma

end EulerPacketSourceGeometry.ForwardGuards
