/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketForwardInput
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedChildShear

@[expose] public section

/-! The first, zero-history packet produces an actual next parent with
the H⁶ label bound k^80, a continuous two-sided inverse, and the same
correction and global shear/Hessian estimates used in its construction. -/

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set Filter InnerProductSpace EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerAllOrderDriftCorrection
  EulerLiftedGradientSpace EulerGraphInvariantFlow EulerPhysicalGraphFlowBounds
  EulerPacketForwardFactorization EulerGraphPressurePotential EulerPeriodicProfile
  EulerSobolevGevreyOperators EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerGevrey EulerMeanClassicalWordBounds EulerPacketParentLabelBounds
  EulerPacketTerminalDatum

variable {A : Parent} (L : LabelData A) (I : ParticleInverse A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S)


variable (J : ForwardInputs (A.meanData H) (A.transverseData m hm R S hS))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ S) (α : ℝ) (hα : 0 < α)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)


include L I J hδ1 hα in
theorem forward_child_eventually :
    ∃ ρ0 γ Cw Cv Cp : ℝ, 0 < ρ0 ∧ 0 < γ ∧ 0 < Cw ∧ 0 < Cv ∧ 0 < Cp ∧
      ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period ((A.transverseData m hm R S hS)).T_pos
          (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm R S hS) rfl δ hδ
            ξ hs α (A.sourceAgreement m hm R S hS H)
            (truncation k) hn k hk))
        (G : EulerPhysicalGraphFlowBounds.Data period A.T)
        (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=γ ∧
        G.A = Q.liftedPacketCoefficient period
          (forwardInitializedNormalizedField (A.meanData H) (A.transverseData m hm R S hS) rfl δ hδ
            ξ hs α (truncation k) k) ∧
        G.A₁ = Q.liftedPacketDerivativeCoefficient period
          (forwardInitializedNormalizedDerivativeField (A.meanData H) (A.transverseData m hm R S
            hS) rfl δ hδ ξ hs α (truncation k) k) ∧
        (∀ (s n : ℕ), n+6 ≤ s → ∀ t : Icc (0 : ℝ) A.T,
          weightedNorm period 6 n (ρ0/4) ((Q.fieldTower period).realization s t) ≤ Cw*delta
            (expansion k) ∧
          weightedNorm period 6 n (ρ0/4) ((Q.pressureTower period).realization s t) ≤ Cw*delta
            (expansion k) ∧
          weightedNorm period 6 n (ρ0/4) ((Q.timeDerivativeTower period).realization s t) ≤
            Cw*delta (expansion k)) ∧
        (∀ (t : Icc (0 : ℝ) A.T) (x : Space),
          ‖fderiv ℝ (forwardInitializedExactPhysicalVelocity (A.meanData H) (A.transverseData m hm
            R S hS) rfl δ hδ ξ hs α
            (A.sourceAgreement m hm R S hS H) (truncation k) hn k hk Q t (I.normalized t)) x -
            (α*deriv (profile δ) (k*⟪m,I.normalized t x⟫_ℝ)) •
              rankOne ℝ (canonicalVelocity (A.transverseData m hm R S hS) ξ t (I.normalized t x))
                (((A.transverseData m hm R S hS)).normal.field t (I.normalized t x))‖ < Cv/k ∧
          ‖fderiv ℝ (gradient (forwardInitializedExactPhysicalPressure (A.meanData H)
            (A.transverseData m hm R S hS) rfl δ hδ ξ hs α
            (A.sourceAgreement m hm R S hS H) (truncation k) hn k hk Q t (I.normalized t))) x -
            (EulerPacketForwardShear.pressureCoefficient (A.transverseData m hm R S hS) ξ α t
              (I.normalized t x) *
              deriv (profile δ) (k*⟪m,I.normalized t x⟫_ℝ)) •
            rankOne ℝ (((A.transverseData m hm R S hS)).normal.field t (I.normalized t x))
              (((A.transverseData m hm R S hS)).normal.field t (I.normalized t x))‖ < Cp/k) ∧
        ∃ (LC : LabelData (A.child G k m hgraph nextEll hnext hnext1))
          (_IC : ParticleInverse (A.child G k m hgraph nextEll hnext hnext1)), LC.K=k^80 := by
  obtain ⟨ρ0,γ,Cw,Cv,Cp,hρ,hγ,hCw,hCv,hCp,hsource⟩ :=
    forwardInitialized_child_label_and_shear_eventually (A.meanData H) (U := U) (A.transverseData m
      hm R S hS) rfl δ hδ hδ1 ξ hs α hα
      J.linear J.normal (ForwardInputs.mean (U := U) J) (A.sourceAgreement m hm R S hS H)
      (fun t x => A.packetPosition (t,x)) I.normalized
      A.packetPosition_contDiff (fun t x => (A.packetPosition_spatial t x).fderiv)
      I.normalized_right I.normalized_continuous A.frame_det
      A.ell A.ell_pos A.ell_le_one
      L.displacement L.velocity L.acceleration L.K L.K_one
      L.displacement_bound L.velocity_bound L.acceleration_bound 6
  refine ⟨ρ0,γ,Cw,Cv,Cp,hρ,hγ,hCw,hCv,hCp,?_⟩
  filter_upwards [hsource] with k hkdata
  obtain ⟨hk,hn,Q,G,E,hδQ,hρQ,hγQ,hG,hG1,hgraph,hweighted,herror,hmatch,hlabel⟩ := hkdata
  let LC := L.child G k m hgraph nextEll hnext hnext1 E
    (fun t => (hmatch t).1) (fun t => (hmatch t).2.1) (fun t => (hmatch t).2.2.1)
    (fun t => (hmatch t).2.2.2.1) (fun t => (hmatch t).2.2.2.2.1)
    (fun t => (hmatch t).2.2.2.2.2.1)
    (k^80) (one_le_pow₀ (by linarith : (1 : ℝ) ≤ k)) hlabel
  exact ⟨hk,hn,Q,G,hgraph,hδQ,hρQ,hγQ,hG,hG1,hweighted,herror,
    LC,I.child G k m hgraph nextEll hnext hnext1,rfl⟩

end EulerParentPacketFrames.LabelData
