/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketUniversalFrequency
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCoefficientBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardExactFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedOutputCosts
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketForwardInput
public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardUniformChild

/-! The uniform direct-forward source comparison constructs the actual
next parent and its k^80 labels, with the same global physical errors. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketSourceFrequency EulerAllOrderDriftCorrection EulerGraphInvariantFlow
  EulerPacketForwardFactorization EulerPeriodicProfile EulerPacketTerminalDatum

variable {A : Parent} (L : LabelData A) (I : ParticleInverse A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  (J : ForwardInputs (A.meanData H) (A.transverseData m hm R S hS))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ S) (α : ℝ) (hα : 0 < α)
  (W : ℝ)
  (hW : EulerPacketForwardRadius.RadiusPrimitives J.linear J.mean J.normal
    (forwardCoefficientBudget period (A.meanData H) (A.transverseData m hm R S hS)
      rfl J.normal) δ ξ W)
  (hprofile : ∀ t, α * J.linear.g t ≤ W)
  (k : ℝ) (hk : UniversalFrequency k)
  (hfrequency : EulerPacketInitializedOutputCost.uniformConstant *
    W ^ EulerPacketInitializedOutputCost.uniformPower ≤ smallPower k)
  (hKk : L.K ≤ k) (hinv : A.ell⁻¹ ≤ k ^ (3 / 4 : ℝ))
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

include hδ1 hα J hW hprofile hfrequency hKk hinv in
theorem forward_uniform_child :
    ∃ (hn : 1 ≤ truncation k)
      (Q : Budget period A.T_pos
        (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm R S hS)
          rfl δ hδ ξ hs α (A.sourceAgreement m hm R S hS H) (truncation k) hn k hk.four))
      (G : EulerPhysicalGraphFlowBounds.Data period A.T)
      (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0),
      G.A=Q.liftedPacketCoefficient period
        (forwardInitializedNormalizedField (A.meanData H) (A.transverseData m hm R S hS)
          rfl δ hδ ξ hs α (truncation k) k) ∧
      (∀ (t : Icc (0 : ℝ) A.T) (x : Space),
        ‖fderiv ℝ (forwardInitializedExactPhysicalVelocity (A.meanData H)
          (A.transverseData m hm R S hS) rfl δ hδ ξ hs α
          (A.sourceAgreement m hm R S hS H) (truncation k) hn k hk.four Q t (I.normalized t)) x -
          (α*deriv (profile δ) (k*⟪m,I.normalized t x⟫_ℝ)) •
            rankOne ℝ (canonicalVelocity (A.transverseData m hm R S hS) ξ t (I.normalized t x))
              ((A.transverseData m hm R S hS).normal.field t (I.normalized t x))‖ ≤ k^(-(1/4 : ℝ)) ∧
        ‖fderiv ℝ (gradient (forwardInitializedExactPhysicalPressure (A.meanData H)
          (A.transverseData m hm R S hS) rfl δ hδ ξ hs α
          (A.sourceAgreement m hm R S hS H) (truncation k) hn k hk.four Q t (I.normalized t))) x -
          (EulerPacketForwardShear.pressureCoefficient (A.transverseData m hm R S hS) ξ α t
            (I.normalized t x)*deriv (profile δ) (k*⟪m,I.normalized t x⟫_ℝ)) •
              rankOne ℝ ((A.transverseData m hm R S hS).normal.field t (I.normalized t x))
                ((A.transverseData m hm R S hS).normal.field t (I.normalized t x))‖ ≤ k^(-(1/4 :
                    ℝ))) ∧
      (∀ (t : Icc (0 : ℝ) A.T) (x : Space),
        ‖(G.displacementField k m A.ell A.ell_pos t).field x‖ ≤ k^(-(1/4 : ℝ))) ∧
      ∃ LC : LabelData (A.child G k m hgraph nextEll hnext hnext1), LC.K=k^80 := by
  obtain ⟨hn,Q,G,E,_,_,hG,_,hgraph,_,herror,hmatch,hlabel,hdisplacement⟩ :=
    forward_uniform_child_label_bounds (A.meanData H) (A.transverseData m hm R S hS) rfl
      δ hδ hδ1 ξ hs α hα J.linear J.normal (ForwardInputs.mean (U := U) J)
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
