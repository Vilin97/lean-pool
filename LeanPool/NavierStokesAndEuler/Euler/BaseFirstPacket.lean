/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BasePacketLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedState
public import LeanPool.NavierStokesAndEuler.Euler.ParentFirstPacketLowGuards

@[expose] public section

/-! The first packet over the concrete base solution produces an actual
smooth Euler state and its localized source bounds. All analytic input
comes from the same initialized correction, graph flow, and error bounds. -/

noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketTerminalDatum
  EulerPacketFirstLowBounds EulerMeanHarmonic

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)

def firstPacketMeanData : EulerMeanPacketProvider.Data :=
  (packetBaseParent β hβ ell hell hell1 T hT hTB).meanData
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)

theorem firstPacketAgreement : EulerPacketCylinderField.SourceCoefficientAgreement
    (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
    (firstPacketData β hβ ell hell hell1 T hT hTB) :=
  (packetBaseParent β hβ ell hell hell1 T hT hTB).sourceAgreement
    firstNormal firstNormal_unit firstFrame support compact
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)

variable (δ : ℝ) (hδ : 0 < δ) (hchild : ℝ)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period hT
    (forwardInitializedCorrectionData (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
      (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate
      (subset_refl _) (δ*hchild) (firstPacketAgreement β hβ ell hell hell1 T hT hTB) N hN k hk))
  (G : EulerPhysicalGraphFlowBounds.Data period T)
  (hG : G.A=Q.liftedPacketCoefficient period
    (forwardInitializedNormalizedField (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
      (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate (subset_refl _)
        (δ*hchild) N k))
  (hgraph : ∀ t q, graphConstraint k firstNormal (G.A.field t q)=0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

def firstPacketState
    (labels : LabelData ((packetBaseParent β hβ ell hell hell1 T hT hTB).child
      G k firstNormal hgraph nextEll hnext hnext1)) :
    SmoothState ((packetBaseParent β hβ ell hell hell1 T hT hTB).child
      G k firstNormal hgraph nextEll hnext hnext1) :=
  (packetBaseState β hβ ell hell hell1 T hT hTB).forwardChild
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)
    firstNormal firstNormal_unit firstFrame support compact symmetric
    δ hδ firstCoordinate (subset_refl _) (δ*hchild) N hN k hk Q G hG hgraph nextEll hnext hnext1
      labels

def firstPacketLowBounds (hquarter : ell ≤ 1/4) (hδ1 : δ ≤ 1) (hhchild : 0 ≤ hchild)
    (ev ep : ℝ)
    (herr : (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.HomogeneousSourceErrors
      firstNormal firstNormal_unit firstFrame support compact Q
      (forwardInitializedApproximationResidual (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
        (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate (subset_refl _)
          (δ*hchild)
        (firstPacketAgreement β hβ ell hell hell1 T hT hTB) N hN k hk)
      k δ hchild firstCoordinate ev ep)
    (hsmall : (initialCoefficientCost+2*initialCoefficientCost*δ*(hchild*firstRatio)+ep)*(T^2/2)+
      initialCoefficientCost*T+
      boundaryLocalizationC2*(initialCoefficientCost+hchild*firstRatio+ev)*ell^3*T ≤ 1/2) :
    LowBounds ((packetBaseParent β hβ ell hell hell1 T hT hTB).child
      G k firstNormal hgraph nextEll hnext hnext1) :=
  (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.firstChildLowBounds
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)
    firstNormal firstNormal_unit firstFrame support compact δ hδ hδ1 hchild hhchild
    firstCoordinate (subset_refl _) N hN k hk Q G hG hgraph nextEll hnext hnext1
    rfl hquarter (subset_halfBall.trans Metric.ball_subset_closedBall)
    ev ep initialCoefficientCost initialCoefficientCost herr
    (firstPacket_primary_size β hβ ell hell hell1 T hT hTB)
    (firstPacket_primary_flux β hβ ell hell hell1 T hT hTB)
    (packetBase_physical_strain β hβ ell hell hell1 T hT hTB)
    (packetBase_physical_force β hβ ell hell hell1 T hT hTB) hsmall

end EulerBaseDatum
