/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimarySourceParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceProfiles

@[expose] public section

/-! Every initialized profile inherits reflection parity from the actual
terminal wave and the prescribed source coefficient symmetries. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

include hTime in
theorem initializedProfiles_parity (eM : EulerMeanPacketProvider.EvenData M)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hBH : ∀ t x, B.H.field t (-x) = B.H.field t x) (p : ℕ) :
    ProfileParity M.T (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α p) := by
  have hp := primary_profile_parity τ hτ hτT B δ hδ (α • ξ) hs
    (joinedSourceOperators period M D τ hτ hτT B) rfl hSym hF hDM hBH
  have hpM : ProfileParity M.T
      (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs)) :=
    hp.changeTime hTime.symm
  exact joinedSourceProfiles_parity period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs))
    eM hSym hF hDM hBH hpM p

end EulerPacketTerminalDatum
