/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedInitialExact
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField

@[expose] public section

/-! Ordinary smooth square-integrable fields realizing both actual
initial increments, with the same concrete high and mean functions. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set MeasureTheory EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPhysicalL2Scaling EulerLpTranslation

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def initializedInitialHighField (N : ℕ) (k : ℝ) : SmoothL2Field Space where
  field := initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k
  smooth := by
    let G := EulerPacketInitial.highField
      (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
      ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹
    exact scale_contDiff M.ℓ _ (G.raw_graph_contDiff ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀)
  integrable n := initializedInitialHigh_memLp M D hTime τ hτ hτT B δ hδ ξ hs α N n k

def initializedInitialMeanField (N : ℕ) (k : ℝ) : SmoothL2Field Space where
  field := initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k
  smooth := by
    let G := EulerPacketInitial.meanField
      (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
      ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹
    exact scale_contDiff M.ℓ _ (G.raw_graph_contDiff ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀)
  integrable n := initializedInitialMean_memLp M D hTime τ hτ hτT B δ hδ ξ hs α N n k

theorem initializedInitialHighField_field (N : ℕ) (k : ℝ) :
    (initializedInitialHighField M D hTime τ hτ hτT B δ hδ ξ hs α N k).field=
      initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k := rfl

theorem initializedInitialMeanField_field (N : ℕ) (k : ℝ) :
    (initializedInitialMeanField M D hTime τ hτ hτT B δ hδ ξ hs α N k).field=
      initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k := rfl

end EulerPacketTerminalDatum
