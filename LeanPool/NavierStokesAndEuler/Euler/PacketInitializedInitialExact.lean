/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedInitial
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactShearError
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds

/-! The exact correction has zero initial value, so the two actual
compactly supported initial increments are precisely the finite-packet
high and mean fields whose physical Sobolev bounds were proved above. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set MeasureTheory EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPhysicalL2Scaling EulerAllOrderDriftCorrection EulerPacketCoordinates

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem initializedInitial_split (N : ℕ) (k : ℝ) :
    scale M.ℓ (fun x => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (0,(x,k*inner ℝ D.m₀ x))) =
      initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k +
      initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k := by
  funext x
  have h := congrFun (EulerPacketInitial.packet_split N k⁻¹ 0
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α))
    (0,(M.ℓ⁻¹ • x,k*inner ℝ D.m₀ (M.ℓ⁻¹ • x)))
  simp only [EulerPacketInitial.timeSlice,Pi.add_apply] at h
  simpa only [initializedInitialHigh,initializedInitialMean,scale,Pi.add_apply,
    smul_add,initializedVelocity] using congrArg (fun v : Space => M.ℓ • v) h

include hTime in
theorem initializedInitialHigh_memLp (N n : ℕ) (k : ℝ) :
    MemLp (iteratedFDeriv ℝ n (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k)) 2 volume :=
        by
  let G := EulerPacketInitial.highField
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
    ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹
  exact scale_jet_memLp M.ℓ M.ℓ_pos _ (G.raw_graph_contDiff ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀) n
    (G.raw_graph_tensor_memLp ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀ n)

include hTime in
theorem initializedInitialMean_memLp (N n : ℕ) (k : ℝ) :
    MemLp (iteratedFDeriv ℝ n (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k)) 2 volume :=
        by
  let G := EulerPacketInitial.meanField
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
    ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹
  exact scale_jet_memLp M.ℓ M.ℓ_pos _ (G.raw_graph_contDiff ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀) n
    (G.raw_graph_tensor_memLp ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀ n)

include hTime in
theorem initializedInitial_compact
    (hS : D.support ⊆ Metric.closedBall 0 (1 / 2 : ℝ)) (N : ℕ) (k : ℝ) :
    HasCompactSupport (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k) ∧
      HasCompactSupport (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k) := by
  have h := initializedInitial_common_support M D hTime τ hτ hτT B δ hδ ξ hs α hS N k
  exact ⟨(isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) h.1,
    (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) h.2⟩

variable (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period D.T_pos
    (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk))

theorem initializedExactPhysicalVelocity_initial (x : Space) :
    initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk Q
      ⟨0,le_rfl,D.T_pos.le⟩ id x =
      initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹ (0,(x,k*inner ℝ D.m₀ x)) := by
  rw [initializedExactPhysicalVelocity_eq,Q.pointField_initial,map_zero,smul_zero,add_zero]
  rfl

theorem initializedExactPhysicalVelocity_initial_split :
    scale M.ℓ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk Q ⟨0,le_rfl,D.T_pos.le⟩ id) =
      initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k +
      initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k := by
  rw [funext (initializedExactPhysicalVelocity_initial M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree N hN k hk Q)]
  exact initializedInitial_split M D τ hτ hτT B δ hδ ξ hs α N k

end EulerPacketTerminalDatum
