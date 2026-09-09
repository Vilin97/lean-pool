/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedFieldParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionCoefficientParity

@[expose] public section

/-! The actual zero-history correction data have all the joint parities
required by the drift-aware correction and pressure construction. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketCorrectionCoefficients
  EulerCylinderFieldReflection

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem forwardInitializedCorrectionParityData (eM : EulerMeanPacketProvider.EvenData M)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
      (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k) :
    EulerCorrectionAssembly.ParityData period
      (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk) := by
  refine {
    metric := metricTower_even D hF period
    linear := linearTower_even D hF hDM period
    quadratic := quadraticTower_odd D hF period k⁻¹
    approximation := ?_
    residual := ?_ }
  · intro t
    change -reflection period
      ((forwardInitializedNormalizedField M D hTime δ hδ ξ hs α N k).path t) = _
    rw [forwardInitializedNormalizedField_odd M D hTime δ hδ ξ hs α
      eM hSym hF hDM N k t,neg_neg]
    rfl
  · intro t
    change -reflection period
      ((forwardInitializedNormalizedResidualField M D hTime δ hδ ξ hs α
        Cagree N hN k hk).path t) = _
    rw [forwardInitializedNormalizedResidualField_odd M D hTime δ hδ ξ hs α
      eM hSym hF hDM Cagree N hN k hk t,neg_neg]
    rfl

end EulerPacketTerminalDatum
