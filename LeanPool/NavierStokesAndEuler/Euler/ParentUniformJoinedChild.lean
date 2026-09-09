/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketUniversalFrequency
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactPressureError
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedOutputCosts
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedUniformChild

/-! The positive-history packet at the fixed frequency constructs the
actual next parent, with the same errors and the k^80 label bound. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketSourceFrequency EulerAllOrderDriftCorrection EulerGraphInvariantFlow
  EulerPacketPrimaryFactorization EulerPeriodicProfile EulerPacketTerminalDatum

variable {A : Parent} (L : LabelData A) (I : ParticleInverse A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < A.T)
  (J : JoinedInputs (A.meanData H) (A.transverseData m hm R S hS) τ hτ hτT
    (A.historyOn H m hm R S hS τ hτ hτT))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ S) (α : ℝ) (hα : 0 < α)
  (W : ℝ)
  (hW : EulerPacketRadiusPolynomial.RadiusPrimitives J.mean J.linear J.normal
    (joinedCoefficientBudget period (A.meanData H) (A.transverseData m hm R S hS)
      rfl τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) J.normal) δ ξ W)
  (hprofile : ∀ t, α * J.linear.fullProfile t ≤ W)
  (k : ℝ) (hk : UniversalFrequency k)
  (hfrequency : EulerPacketInitializedOutputCost.uniformConstant *
    W ^ EulerPacketInitializedOutputCost.uniformPower ≤ smallPower k)
  (hKk : L.K ≤ k) (hinv : A.ell⁻¹ ≤ k ^ (3 / 4 : ℝ))
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

include hδ1 hα J hW hprofile hfrequency hKk hinv in
theorem joined_uniform_child :
    ∃ (hn : 1 ≤ truncation k)
      (Q : Budget period A.T_pos
        (initializedCorrectionData (A.meanData H) (A.transverseData m hm R S hS)
          rfl τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) δ hδ ξ hs α
          (A.sourceAgreement m hm R S hS H) (truncation k) hn k hk.four))
      (G : EulerPhysicalGraphFlowBounds.Data period A.T)
      (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0),
      G.A=Q.liftedPacketCoefficient period
        (initializedNormalizedField (A.meanData H) (A.transverseData m hm R S hS)
          rfl τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) δ hδ ξ hs α (truncation k) k) ∧
      (∀ (t : Icc (0 : ℝ) A.T) (x : Space),
        ‖fderiv ℝ (initializedExactPhysicalVelocity (A.meanData H)
          (A.transverseData m hm R S hS) rfl τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT)
          δ hδ ξ hs α (A.sourceAgreement m hm R S hS H)
          (truncation k) hn k hk.four Q t (I.normalized t)) x -
          (α*deriv (profile δ) (k*⟪m,I.normalized t x⟫_ℝ)) •
            rankOne ℝ (canonicalVelocity τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT)
              ξ hs t (I.normalized t x))
              ((A.transverseData m hm R S hS).normal.field t (I.normalized t x))‖ ≤ k^(-(1/4 : ℝ)) ∧
        ‖fderiv ℝ (gradient (initializedExactPhysicalPressure (A.meanData H)
          (A.transverseData m hm R S hS) rfl τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT)
          δ hδ ξ hs α (A.sourceAgreement m hm R S hS H)
          (truncation k) hn k hk.four Q t (I.normalized t))) x -
          (EulerPacketPrimaryPressure.coefficient τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT)
            ξ hs α t (I.normalized t x)*deriv (profile δ) (k*⟪m,I.normalized t x⟫_ℝ)) •
              rankOne ℝ ((A.transverseData m hm R S hS).normal.field t (I.normalized t x))
                ((A.transverseData m hm R S hS).normal.field t (I.normalized t x))‖ ≤ k^(-(1/4 :
                    ℝ))) ∧
      (∀ (t : Icc (0 : ℝ) A.T) (x : Space),
        ‖(G.displacementField k m A.ell A.ell_pos t).field x‖ ≤ k^(-(1/4 : ℝ))) ∧
      ∃ LC : LabelData (A.child G k m hgraph nextEll hnext hnext1), LC.K=k^80 := by
  obtain ⟨hn,Q,G,E,_,_,hG,_,hgraph,_,herror,hmatch,hlabel,hdisplacement⟩ :=
    initialized_uniform_child_label_bounds (A.meanData H) (A.transverseData m hm R S hS) rfl
      τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT)
      δ hδ hδ1 ξ hs α hα J.linear J.normal (JoinedInputs.mean (U := U) J)
      (A.sourceAgreement m hm R S hS H) W hW hprofile k hk.four hk.expansion_bound hk.log_bound
      hfrequency hk.delta_bound hk.root_bound hk.trace_bound
      (fun t x => A.packetPosition (t,x)) I.normalized
      A.packetPosition_contDiff (fun t x => (A.packetPosition_spatial t x).fderiv)
      I.normalized_right I.normalized_continuous A.frame_det
      A.ell A.ell_pos A.ell_le_one L.displacement L.velocity L.acceleration L.K L.K_one
      L.displacement_bound L.velocity_bound L.acceleration_bound 6
      hk.child_bound hKk hk.embedding_bound hk.derivative_bound hinv
  let LC := L.child G k m hgraph nextEll hnext hnext1 E
    (fun t => (hmatch t).1) (fun t => (hmatch t).2.1) (fun t => (hmatch t).2.2.1)
    (fun t => (hmatch t).2.2.2.1) (fun t => (hmatch t).2.2.2.2.1)
    (fun t => (hmatch t).2.2.2.2.2.1)
    (k^80) (one_le_pow₀ hk.one_le) hlabel
  exact ⟨hn,Q,G,hgraph,hG,herror,hdisplacement,LC,rfl⟩

end EulerParentPacketFrames.LabelData
