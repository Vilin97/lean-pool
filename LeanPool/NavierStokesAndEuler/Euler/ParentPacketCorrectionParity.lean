/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketParity
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionParity

@[expose] public section

/-! Actual odd parent fields supply the parity data for both initialized
packet branches. The resulting corrected coefficient, and hence the
actual next particle map, retain oddness without a new symmetry premise. -/

noncomputable section

namespace EulerParentPacketFrames.OddData

open Set EulerSmoothLimit EulerSpatialCutoffs EulerPacketTerminalDatum
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCorrectionAssembly
  EulerTimeIntervalRestriction EulerGraphInvariantFlow EulerAllOrderCorrectionData
  EulerAllOrderDriftCorrection

variable {A : Parent} (O : OddData A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (hSym : ∀ x, -x ∈ S ↔ x ∈ S)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ S) (α : ℝ)

include O hSym

theorem forwardCorrectionParity (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    ParityData period
      (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm R S hS) rfl
        δ hδ ξ hs α (A.sourceAgreement m hm R S hS H) N hN k hk) :=
  forwardInitializedCorrectionParityData (A.meanData H) (A.transverseData m hm R S hS) rfl
    δ hδ ξ hs α (O.meanEvenData H) hSym O.frame_even O.strain_even
    (A.sourceAgreement m hm R S hS H) N hN k hk

theorem joinedCorrectionParity (τ : ℝ) (hτ : 0 < τ) (hτT : τ < A.T)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    ParityData period
      (initializedCorrectionData (A.meanData H) (A.transverseData m hm R S hS) rfl
        τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) δ hδ ξ hs α
        (A.sourceAgreement m hm R S hS H) N hN k hk) := by
  apply initializedCorrectionParityData (A.meanData H) (A.transverseData m hm R S hS) rfl
    τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) δ hδ ξ hs α
    (O.meanEvenData H) hSym O.frame_even O.strain_even
    _ (A.sourceAgreement m hm R S hS H) N hN k hk
  intro t x
  exact O.curvature_even (initialInclusion A.T τ hτT.le t) x

omit hSym [CompleteSpace U] in
theorem childOfPacket {P : ℝ} [Fact (0 < P)] {C : EulerAllOrderCorrectionData.Data P A.T}
    (B : Budget P A.T_pos C) (E : ParityData P C)
    {raw : VectorField} (V : Field P A.T raw) (hV : C.approximation=V.toFieldTower)
    (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A=B.liftedPacketCoefficient P V)
    (k : ℝ) (hgraph : ∀ t z, graphConstraint k C.direction (G.A.field t z)=0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1) :
    OddData (A.child G k C.direction hgraph nextEll hnext hnext1) := by
  apply O.child G _ k C.direction hgraph nextEll hnext hnext1
  intro t
  rw [hG]
  exact B.liftedPacketCoefficient_odd P V hV E t

end EulerParentPacketFrames.OddData
