/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionData
import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionCoefficientParity
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedFieldParity

/-! The actual initialized correction data have all the joint parities
required by the drift-aware correction and pressure construction. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketCorrectionCoefficients
  EulerCylinderFieldReflection

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem initializedCorrectionParityData (eM : EulerMeanPacketProvider.EvenData M)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hBH : ∀ t x, B.H.field t (-x) = B.H.field t x)
    (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k) :
    EulerCorrectionAssembly.ParityData period
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk) := by
  refine {
    metric := metricTower_even D hF period
    linear := linearTower_even D hF hDM period
    quadratic := quadraticTower_odd D hF period k⁻¹
    approximation := ?_
    residual := ?_ }
  · intro t
    change -reflection period
      ((initializedNormalizedField M D hTime τ hτ hτT B δ hδ ξ hs α N k).path t) = _
    rw [initializedNormalizedField_odd M D hTime τ hτ hτT B δ hδ ξ hs α
      eM hSym hF hDM hBH N k t,neg_neg]
    rfl
  · intro t
    change -reflection period
      ((initializedNormalizedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α
        Cagree N hN k hk).path t) = _
    rw [initializedNormalizedResidualField_odd M D hTime τ hτ hτT B δ hδ ξ hs α
      eM hSym hF hDM hBH Cagree N hN k hk t,neg_neg]
    rfl

end EulerPacketTerminalDatum
