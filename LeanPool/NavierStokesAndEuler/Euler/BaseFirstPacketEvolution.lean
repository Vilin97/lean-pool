/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacketChoice
public import LeanPool.NavierStokesAndEuler.Euler.BasePacketFrameValues
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketStateGeometry

@[expose] public section

/-! The first constructed packet supplies the physical low bounds and
the actual center expansion needed by the first normal stage. -/

noncomputable section

namespace EulerParentPacketFrames.SmoothState

open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketTerminalDatum
  EulerPacketProfileRecursion EulerSpatialCutoffs

variable {A : Parent} (S : SmoothState A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (hSym : ∀ x, -x ∈ support ↔ x ∈ support)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ support) (α : ℝ)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)

/-- Transfer the center error before specializing the parent to its concrete flow. -/
private theorem forwardChild_center_error
    (Q : Budget period A.T_pos
      (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm J support hSupport)
        rfl δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk))
    (G : EulerPhysicalGraphFlowBounds.Data period A.T)
    (hG : G.A=Q.liftedPacketCoefficient period
      (forwardInitializedNormalizedField (A.meanData H) (A.transverseData m hm J support hSupport)
        rfl δ hδ ξ hs α N k))
    (hgraph : ∀ t q, graphConstraint k m (G.A.field t q)=0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
    (labels : LabelData (A.child G k m hgraph nextEll hnext hnext1))
    (C : Icc (0 : ℝ) A.T → Space →L[ℝ] Space) (error : ℝ)
    (herr : ∀ t, ‖fderiv ℝ
      (A.normalizedPacketVelocity m hm J support hSupport Q
        (forwardInitializedApproximationResidual (A.meanData H)
          (A.transverseData m hm J support hSupport) rfl δ hδ ξ hs α
          (A.sourceAgreement m hm J support hSupport H) N hN k hk)
        k S.evolution.inverse t) 0-C t‖ ≤ error)
    (t : Icc (0 : ℝ) A.T) :
    ‖fderiv ℝ (S.velocityIncrement
      (S.forwardChild H m hm J support hSupport hSym δ hδ ξ hs α N hN k hk
        Q G hG hgraph nextEll hnext hnext1 labels) t) 0-C t‖ ≤ error := by
  exact S.packetChild_center_error m hm J support hSupport Q
    (forwardInitializedApproximationResidual (A.meanData H)
      (A.transverseData m hm J support hSupport) rfl δ hδ ξ hs α
      (A.sourceAgreement m hm J support hSupport H) N hN k hk)
    (forwardInitializedNormalizedField (A.meanData H)
      (A.transverseData m hm J support hSupport) rfl δ hδ ξ hs α N k) rfl
    (S.odd.forwardCorrectionParity H m hm J support hSupport hSym δ hδ ξ hs α N hN k hk)
    G hG k (mul_inv_cancel₀ (by linarith : k ≠ 0)) hgraph nextEll hnext hnext1 labels C error herr t

end EulerParentPacketFrames.SmoothState

namespace EulerBaseDatum.FirstPacketChoice

-- Keep type unification from expanding the concrete initial flow.
attribute [local irreducible] initialParent

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerParentPacketFrames
  EulerPacketSupport EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketFirstLowBounds EulerPacketPhysicalLowBounds EulerPacketSourceGeometry
  EulerPacketForwardFactorization EulerPeriodicProfile EulerTransverseFrameCoordinates

variable {β : ℝ} {hβ : |β| ≤ 1} {ell : ℝ} {hell : 0 < ell} {hell1 : ell ≤ 1}
  {T : ℝ} {hT : 0 < T} {hTB : T ≤ initialTime}
  {δ : ℝ} {hδ : 0 < δ} {hchild k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : FirstPacketChoice β hβ ell hell hell1 T hT hTB δ hδ hchild k hk nextEll hnext hnext1)

theorem physical_bounds (hδ1 : δ ≤ 1) (hh : 0 ≤ hchild)
    (t : Icc (0 : ℝ) T) (x : Space) :
    ‖fderiv ℝ (fun y => F.state.evolution.velocity (t,y)) x‖ ≤
      initialCoefficientCost+hchild*firstRatio+k^(-(1/4 : ℝ)) ∧
    ‖fderiv ℝ (F.state.evolution.force t) x‖ ≤
      initialCoefficientCost+2*initialCoefficientCost*(hchild*firstRatio)+k^(-(1/4 : ℝ)) := by
  let S := packetBaseState β hβ ell hell hell1 T hT hTB
  let M := firstPacketMeanData β hβ ell hell hell1 T hT hTB
  let D := firstPacketData β hβ ell hell hell1 T hT hTB
  let res := forwardInitializedApproximationResidual M D rfl δ hδ firstCoordinate (subset_refl _)
    (δ*hchild) (firstPacketAgreement β hβ ell hell hell1 T hT hTB) (truncation k) F.hn k hk.four
  have h := S.evolution.exactHomogeneousPacket_low_bounds
    firstNormal firstNormal_unit firstFrame support compact F.Q res k (mul_inv_cancel₀ hk.pos.ne')
    δ hchild firstCoordinate hδ hδ1 hh
    (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) initialCoefficientCost initialCoefficientCost
      initialCoefficientCost
    F.errors (firstPacket_primary_size β hβ ell hell hell1 T hT hTB)
    (firstPacket_primary_flux β hβ ell hell hell1 T hT hTB) t x
    (packetBase_physical_strain β hβ ell hell hell1 T hT hTB t x)
    (packetBase_physical_force β hβ ell hell hell1 T hT hTB t x)
    (S.evolution.force_quadratic_upper_of_lowBounds (packetBaseLowBounds β hβ ell hell hell1 T hT
      hTB) t x)
  dsimp only [S, M, D, res, firstPacketMeanData, firstPacketData] at h
  constructor
  · dsimp only [state, firstPacketState, SmoothState.forwardChild,
      SmoothState.packetChild, Evolution.child]
    with_reducible exact h.1
  · refine (congrArg (fun M : Space →L[ℝ] Space => ‖M‖)
      (F.state.evolution.pressure_hessian_eq_force t x).symm).trans_le ?_
    dsimp only [state, firstPacketState, SmoothState.forwardChild,
      SmoothState.packetChild, Evolution.child]
    with_reducible exact h.2.1

theorem center_error (t : Icc (0 : ℝ) T) :
    ‖fderiv ℝ ((packetBaseState β hβ ell hell hell1 T hT hTB).velocityIncrement F.state t) 0-
      ((δ*hchild)*deriv (profile δ)
        (k*⟪firstNormal,(packetBaseState β hβ ell hell hell1 T hT hTB).evolution.inverse.normalized
          t 0⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity (firstPacketData β hβ ell hell hell1 T hT hTB) firstCoordinate
          t
          ((packetBaseState β hβ ell hell hell1 T hT hTB).evolution.inverse.normalized t 0))
          ((firstPacketData β hβ ell hell hell1 T hT hTB).normal.field t
            ((packetBaseState β hβ ell hell hell1 T hT hTB).evolution.inverse.normalized t 0))‖ ≤
              k^(-(1/4 : ℝ)) := by
  let S := packetBaseState β hβ ell hell hell1 T hT hTB
  let H := packetBaseLowBounds β hβ ell hell hell1 T hT hTB
  let D := firstPacketData β hβ ell hell hell1 T hT hTB
  let C (s : Icc (0 : ℝ) T) : Space →L[ℝ] Space := shearTerm (δ*hchild)
    (deriv (profile δ) (k*⟪firstNormal,S.evolution.inverse.normalized s 0⟫_ℝ))
    (D.normal.field s (S.evolution.inverse.normalized s 0))
    (canonicalVelocity D firstCoordinate s (S.evolution.inverse.normalized s 0))
  dsimp only [state, firstPacketState]
  exact S.forwardChild_center_error H
    firstNormal firstNormal_unit firstFrame support compact symmetric δ hδ firstCoordinate
    (subset_refl _) (δ*hchild) (truncation k) F.hn k hk.four F.Q F.G F.coefficient F.graph
    nextEll hnext hnext1 F.labels C (k^(-(1/4 : ℝ))) (fun s => (F.errors s 0).1) t

end EulerBaseDatum.FirstPacketChoice
