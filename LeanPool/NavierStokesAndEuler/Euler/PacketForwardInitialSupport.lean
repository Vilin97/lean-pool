/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardExactFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialSupport
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceInitialMean

@[expose] public section

/-! With the base boundary parameter zero, the entire actual forward
initial increment is supported in the small physical packet ball. The
exact correction starts from zero, so it adds no initial tail. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPhysicalL2Scaling
  EulerAllOrderDriftCorrection EulerPacketCoordinates

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def forwardInitializedInitialHigh (N : ℕ) (k : ℝ) : Space → Space :=
  scale M.ℓ (fun x => EulerPacketInitial.high N k⁻¹ 0
    (forwardInitializedProfiles M D δ hδ ξ hs α) (0,(x,k*inner ℝ D.m₀ x)))

def forwardInitializedInitialMean (N : ℕ) (k : ℝ) : Space → Space :=
  scale M.ℓ (fun x => EulerPacketInitial.mean N k⁻¹ 0
    (forwardInitializedProfiles M D δ hδ ξ hs α) (0,(x,k*inner ℝ D.m₀ x)))

include hTime in
theorem forwardInitializedInitialHigh_support
    (hS : D.support ⊆ Metric.closedBall 0 (1/2 : ℝ)) (N : ℕ) (k : ℝ) :
    tsupport (forwardInitializedInitialHigh M D δ hδ ξ hs α N k) ⊆
      Metric.closedBall 0 (M.ℓ/2) := by
  have h := EulerPacketInitial.high_scaled_support
    (fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i)
    ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹ k D.m₀ M.ℓ M.ℓ_pos (1/2) hS
  simpa only [forwardInitializedInitialHigh,div_eq_mul_inv,one_mul] using h

include hTime in
theorem forwardInitializedInitialMean_zero (hL : M.L=0) (N : ℕ) (k : ℝ) :
    forwardInitializedInitialMean M D δ hδ ξ hs α N k = 0 := by
  funext x
  change M.ℓ • EulerPacketInitial.mean N k⁻¹ 0
    (forwardInitializedProfiles M D δ hδ ξ hs α)
    (0,(M.ℓ⁻¹ • x,k*inner ℝ D.m₀ (M.ℓ⁻¹ • x))) = 0
  rw [EulerPacketInitial.mean_eq]
  simp only [EulerPacketPointJets.fieldSum,EulerFiniteGrades.evaluate,EulerPacketInitial.timeSlice]
  have hz (i : ℕ) := source_mean_initial_zero period M D hTime (InitialData.zero period D)
    (initialData D δ hδ (α • ξ) hs) hL i (M.ℓ⁻¹ • x) (k*inner ℝ D.m₀ (M.ℓ⁻¹ • x))
  simp only [show ∀ i, (forwardInitializedProfiles M D δ hδ ξ hs α i).mean
      (0,(M.ℓ⁻¹ • x,k*inner ℝ D.m₀ (M.ℓ⁻¹ • x))) = 0 from hz,
    smul_zero,Finset.sum_const_zero]

theorem forwardInitializedInitial_split (N : ℕ) (k : ℝ) :
    scale M.ℓ (fun x => forwardInitializedVelocity M D δ hδ ξ hs α N k⁻¹
      (0,(x,k*inner ℝ D.m₀ x))) =
      forwardInitializedInitialHigh M D δ hδ ξ hs α N k +
      forwardInitializedInitialMean M D δ hδ ξ hs α N k := by
  funext x
  have h := congrFun (EulerPacketInitial.packet_split N k⁻¹ 0
    (forwardInitializedProfiles M D δ hδ ξ hs α))
    (0,(M.ℓ⁻¹ • x,k*inner ℝ D.m₀ (M.ℓ⁻¹ • x)))
  simp only [EulerPacketInitial.timeSlice,Pi.add_apply] at h
  simpa only [forwardInitializedInitialHigh,forwardInitializedInitialMean,scale,Pi.add_apply,
    smul_add,forwardInitializedVelocity] using congrArg (fun v : Space => M.ℓ • v) h

variable (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period D.T_pos
    (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk))

theorem forwardInitializedExactPhysicalVelocity_initial (x : Space) :
    forwardInitializedExactPhysicalVelocity M D hTime δ hδ ξ hs α Cagree N hN k hk Q
      ⟨0,le_rfl,D.T_pos.le⟩ id x =
      forwardInitializedVelocity M D δ hδ ξ hs α N k⁻¹ (0,(x,k*inner ℝ D.m₀ x)) := by
  rw [forwardInitializedExactPhysicalVelocity_eq,Q.pointField_initial,map_zero,smul_zero,add_zero]
  rfl

theorem forwardInitializedExactPhysicalVelocity_initial_split :
    scale M.ℓ (forwardInitializedExactPhysicalVelocity M D hTime δ hδ ξ hs α
      Cagree N hN k hk Q ⟨0,le_rfl,D.T_pos.le⟩ id) =
      forwardInitializedInitialHigh M D δ hδ ξ hs α N k +
      forwardInitializedInitialMean M D δ hδ ξ hs α N k := by
  rw [funext (forwardInitializedExactPhysicalVelocity_initial M D hTime δ hδ ξ hs α
    Cagree N hN k hk Q)]
  exact forwardInitializedInitial_split M D δ hδ ξ hs α N k

theorem forwardInitializedExactPhysicalVelocity_initial_support (hL : M.L=0)
    (hS : D.support ⊆ Metric.closedBall 0 (1/2 : ℝ)) :
    tsupport (scale M.ℓ (forwardInitializedExactPhysicalVelocity M D hTime δ hδ ξ hs α
      Cagree N hN k hk Q ⟨0,le_rfl,D.T_pos.le⟩ id)) ⊆ Metric.closedBall 0 (M.ℓ/2) := by
  rw [forwardInitializedExactPhysicalVelocity_initial_split,
    forwardInitializedInitialMean_zero M D hTime δ hδ ξ hs α hL N k,add_zero]
  exact forwardInitializedInitialHigh_support M D hTime δ hδ ξ hs α hS N k

end EulerPacketTerminalDatum
