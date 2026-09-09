/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalAdmissible

@[expose] public section

/-! Reflection parity of every zero-history profile, derived from the
literal terminal wave and the prescribed coefficient symmetries. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCylinderFieldReflection
  EulerLpCylinderTranslation

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

include hTime in
theorem forwardInitializedProfiles_parity (eM : EulerMeanPacketProvider.EvenData M)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x) (p : ℕ) :
    ProfileParity M.T (forwardInitializedProfiles M D δ hδ ξ hs α p) := by
  apply sourceProfiles_parity period M D (InitialData.zero period D)
    (initialData D δ hδ (α • ξ) hs) hTime eM hSym hF hDM
  · change reflection period (0 : CylinderL2 period U) = -0
    simp only [map_zero,neg_zero]
  · exact terminal_reflection δ hδ (α • ξ)

end EulerPacketTerminalDatum
