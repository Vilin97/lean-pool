/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacket
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardInitialSupport
public import LeanPool.NavierStokesAndEuler.Euler.BasePacketUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.ParentUniformForwardChild

@[expose] public section

/-! One actual first-packet correction, its physical flow, labels and
source errors. The uniform scalar frequency guard constructs the record. -/

noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketTerminalDatum
  EulerPacketSourceFrequency EulerPacketUniformSource EulerPacketPhysicalLowBounds
  EulerPacketFirstLowBounds EulerMeanHarmonic

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)
  (δ : ℝ) (hδ : 0 < δ) (hchild k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

section ConstructorInjectivity

attribute [local irreducible] Parent.child initialParent

structure FirstPacketChoice where
  hn : 1 ≤ truncation k
  Q : Budget period hT
    (forwardInitializedCorrectionData (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
      (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate
      (subset_refl _) (δ*hchild) (firstPacketAgreement β hβ ell hell hell1 T hT hTB)
      (truncation k) hn k hk.four)
  G : EulerPhysicalGraphFlowBounds.Data period T
  graph : ∀ t q, graphConstraint k firstNormal (G.A.field t q)=0
  coefficient : G.A=Q.liftedPacketCoefficient period
    (forwardInitializedNormalizedField (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
      (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate (subset_refl _)
      (δ*hchild) (truncation k) k)
  labels : LabelData ((packetBaseParent β hβ ell hell hell1 T hT hTB).child
    G k firstNormal graph nextEll hnext hnext1)
  label_constant : labels.K=k^80
  displacement_bound : ∀ (t : Icc (0 : ℝ) T) (x : Space),
    ‖(G.displacementField k firstNormal ell hell t).field x‖ ≤ k^(-(1/4 : ℝ))
  errors : (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.HomogeneousSourceErrors
    firstNormal firstNormal_unit firstFrame support compact Q
    (forwardInitializedApproximationResidual (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
      (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate (subset_refl _)
      (δ*hchild) (firstPacketAgreement β hβ ell hell hell1 T hT hTB) (truncation k) hn k hk.four)
    k δ hchild firstCoordinate (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ)))

end ConstructorInjectivity

theorem exists_firstPacketChoice (hδ1 : δ ≤ 1) (hh : 0 < hchild)
    (hfrequency : EulerPacketInitializedOutputCost.uniformConstant*
      (profileEnvelope (firstParameterSize T δ
        hchild))^EulerPacketInitializedOutputCost.uniformPower ≤
        smallPower k)
    (hKk : solutionLabelConstant ≤ k) (hinv : ell⁻¹ ≤ k^(3/4 : ℝ)) :
    Nonempty (FirstPacketChoice β hβ ell hell hell1 T hT hTB δ hδ hchild k hk nextEll hnext hnext1)
      := by
  let A := packetBaseParent β hβ ell hell hell1 T hT hTB
  let S := packetBaseState β hβ ell hell hell1 T hT hTB
  let H := packetBaseLowBounds β hβ ell hell hell1 T hT hTB
  let J := firstPacketInputs β hβ ell hell hell1 T hT hTB
  have hp := firstPacket_uniform_primitives β hβ ell hell hell1 T hT hTB δ hδ hδ1 hchild hh.le
  obtain ⟨hn,Q,G,hgraph,hG,herror,hdisplacement,LC,hLC⟩ := S.labels.forward_uniform_child
    S.evolution.inverse H
    firstNormal firstNormal_unit firstFrame support compact J δ hδ hδ1 firstCoordinate (subset_refl
      _)
    (δ*hchild) (mul_pos hδ hh) (profileEnvelope (firstParameterSize T δ hchild)) hp.1 hp.2.1
    k hk hfrequency hKk hinv nextEll hnext hnext1
  refine ⟨⟨hn,Q,G,hgraph,hG,LC,hLC,hdisplacement,?_⟩⟩
  intro t x
  constructor
  · erw [A.normalizedPacketVelocity_forwardInitialized H firstNormal firstNormal_unit
      firstFrame support compact δ hδ firstCoordinate (subset_refl _) (δ*hchild)
      (truncation k) hn k hk.four Q S.evolution.inverse t]
    exact (herror t x).1
  · erw [A.normalizedPacketPressure_forwardInitialized H firstNormal firstNormal_unit
      firstFrame support compact δ hδ firstCoordinate (subset_refl _) (δ*hchild)
      (truncation k) hn k hk.four Q S.evolution.inverse t]
    conv_lhs =>
      enter [1, 2]
      erw [forwardPressureTerm_eq_coefficient
        (D := A.transverseData firstNormal firstNormal_unit firstFrame support compact)
        firstCoordinate]
    exact (herror t x).2

namespace FirstPacketChoice

variable (F : FirstPacketChoice β hβ ell hell hell1 T hT hTB δ hδ hchild k hk nextEll hnext hnext1)

def parent : Parent := (packetBaseParent β hβ ell hell hell1 T hT hTB).child
  F.G k firstNormal F.graph nextEll hnext hnext1

def state : SmoothState F.parent :=
  firstPacketState β hβ ell hell hell1 T hT hTB δ hδ hchild (truncation k) F.hn k hk.four
    F.Q F.G F.coefficient F.graph nextEll hnext hnext1 F.labels

theorem state_label_constant : F.state.labels.K=k^80 := F.label_constant

def lowBounds (hquarter : ell ≤ 1/4) (hδ1 : δ ≤ 1) (hh : 0 ≤ hchild)
    (hsmall : (initialCoefficientCost+2*initialCoefficientCost*δ*(hchild*firstRatio)+k^(-(1/4 :
      ℝ)))*(T^2/2)+
      initialCoefficientCost*T+
      boundaryLocalizationC2*(initialCoefficientCost+hchild*firstRatio+k^(-(1/4 : ℝ)))*ell^3*T ≤
        1/2) :
    LowBounds F.parent :=
  firstPacketLowBounds β hβ ell hell hell1 T hT hTB δ hδ hchild (truncation k) F.hn k hk.four
    F.Q F.G F.coefficient F.graph nextEll hnext hnext1 hquarter hδ1 hh
    (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) F.errors hsmall

end FirstPacketChoice
end EulerBaseDatum
