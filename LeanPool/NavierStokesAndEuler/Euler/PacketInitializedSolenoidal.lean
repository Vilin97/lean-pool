/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionData

/-! The initialized approximation satisfies the actual lifted divergence
constraint whenever the source deformation is a volume-preserving Jacobian. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerLiftedGradientSpace
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (Cagree : SourceCoefficientAgreement M D)

include Cagree

theorem initializedPacketField_mem (N : ℕ) (κ : ℝ) (t : Icc (0 : ℝ) M.T)
    (Ξ : Space → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hF : ∀ x, fderiv ℝ Ξ x = D.F.field (sourceTime M D hTime t) x)
    (hdet : ∀ x, (EulerPacketPiola.operatorMatrix (D.F.field (sourceTime M D hTime t) x)).det = 1) :
    (initializedPacketField M D hTime τ hτ hτT B δ hδ ξ hs α N κ).path t ∈
      divergenceFreeSpace period κ D.m₀ :=
  joinedPacketPullbackField_mem period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    rfl rfl
    (fun t x => EulerTransversePacketPrimary.vector_mean_zero τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs) t.val x)
    (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    Cagree N κ t Ξ hΞ hF hdet

theorem initializedCorrectionData_divergence (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
    (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)
    (t : Icc (0 : ℝ) D.T) :
    (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k
        hk).approximation.field t ∈
      divergenceFreeSpace period k⁻¹ D.m₀ := by
  let tm : Icc (0 : ℝ) M.T := ⟨t.val,by simpa only [hTime] using t.property⟩
  let G := initializedPacketField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹
  have hm : G.path tm ∈ divergenceFreeSpace period k⁻¹ D.m₀ :=
    initializedPacketField_mem M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N k⁻¹ tm
      (Ξ t) (hΞ t) (hF t) (hdet t)
  change ((G.smul k).changeTime hTime).path t ∈ divergenceFreeSpace period k⁻¹ D.m₀
  rw [(G.smul k).changeTime_apply hTime tm]
  exact (divergenceFreeSpace period k⁻¹ D.m₀).smul_mem k hm

end EulerPacketTerminalDatum
