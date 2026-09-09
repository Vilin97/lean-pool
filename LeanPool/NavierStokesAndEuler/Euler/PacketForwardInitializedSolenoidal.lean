/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionData

@[expose] public section

/-! The zero-history initialized approximation satisfies the lifted divergence
constraint for an actual volume-preserving source deformation. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerLiftedGradientSpace
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (Cagree : SourceCoefficientAgreement M D)

include Cagree

theorem forwardInitializedPacketField_mem (N : ℕ) (κ : ℝ) (t : Icc (0 : ℝ) M.T)
    (Ξ : Space → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hF : ∀ x, fderiv ℝ Ξ x = D.F.field (sourceTime M D hTime t) x)
    (hdet : ∀ x, (EulerPacketPiola.operatorMatrix
      (D.F.field (sourceTime M D hTime t) x)).det = 1) :
    (forwardInitializedPacketField M D hTime δ hδ ξ hs α N κ).path t ∈
      divergenceFreeSpace period κ D.m₀ :=
  sourcePacketPullbackField_mem period M D hTime (InitialData.zero period D)
    (initialData D δ hδ (α • ξ) hs) Cagree N κ t Ξ hΞ hF hdet

theorem forwardInitializedCorrectionData_divergence (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
    (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)
    (t : Icc (0 : ℝ) D.T) :
    (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk).approximation.field t
      ∈
      divergenceFreeSpace period k⁻¹ D.m₀ := by
  let tm : Icc (0 : ℝ) M.T := ⟨t.val,by simpa only [hTime] using t.property⟩
  let G := forwardInitializedPacketField M D hTime δ hδ ξ hs α N k⁻¹
  have hm : G.path tm ∈ divergenceFreeSpace period k⁻¹ D.m₀ :=
    forwardInitializedPacketField_mem M D hTime δ hδ ξ hs α Cagree N k⁻¹ tm
      (Ξ t) (hΞ t) (hF t) (hdet t)
  change ((G.smul k).changeTime hTime).path t ∈ divergenceFreeSpace period k⁻¹ D.m₀
  rw [(G.smul k).changeTime_apply hTime tm]
  exact (divergenceFreeSpace period k⁻¹ D.m₀).smul_mem k hm

end EulerPacketTerminalDatum
