/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedExactLifted
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedResidualEquation
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionChoice
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionParity

@[expose] public section

/-! Source budgets and the actual zero-history initialized residual construct exact
corrected lifted packets at every sufficiently large frequency. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerAllOrderDriftCorrection
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerCylinderReflection
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def forwardInitializedExactPacket (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (Q : Budget period D.T_pos
      (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk)) :
    ExactLiftedPacket period D.T_pos
      (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk) Q :=
  exactPacketOfResidual period Q
    (forwardInitializedApproximationResidual M D hTime δ hδ ξ hs α Cagree N hN k hk)

theorem forwardInitializedExactPacket_velocity_odd
    (eM : EulerMeanPacketProvider.EvenData M)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k)
    (Q : Budget period D.T_pos
      (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk))
    (t : Icc (0 : ℝ) D.T) :
    -reflection period
      ((forwardInitializedExactPacket M D hTime δ hδ ξ hs α Cagree N hN k hk Q).velocity.field t) =
      (forwardInitializedExactPacket M D hTime δ hδ ξ hs α Cagree N hN k hk Q).velocity.field t :=
  exactPacketOfResidual_velocity_odd period Q _
    (forwardInitializedCorrectionParityData M D hTime δ hδ ξ hs α
      eM hSym hF hDM Cagree N hN k hk) t

/-- No inverse budget, residual equation or pressure is postulated here.
The original source data construct the budget and the exact corrected pair
for every sufficiently large frequency, with fixed positive radius and cost. -/
theorem forwardInitialized_exact_lifted_packets_eventually
    (hδ1 : δ ≤ 1) (hα : 0 < α)
    (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
    (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
    {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
    (Cagree : SourceCoefficientAgreement M D)
    (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
    (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1) :
    ∃ ρ0 C : ℝ, 0 < ρ0 ∧ 0 < C ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : Budget period D.T_pos
          (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree (truncation k) hn k hk)),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=C ∧
          Nonempty (ExactLiftedPacket period D.T_pos
            (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree (truncation k) hn k hk)
              Q) := by
  obtain ⟨ρ0,C,hρ,hC,he⟩ := forwardInitialized_correction_budgets_eventually M D hTime
    δ hδ hδ1 ξ hs α hα L NB LM Cagree Ξ hΞ hF hdet
  refine ⟨ρ0,C,hρ,hC,?_⟩
  filter_upwards [he] with k hk
  obtain ⟨hk,hn,Q,hδQ,hρQ,hCQ⟩ := hk
  exact ⟨hk,hn,Q,hδQ,hρQ,hCQ,
    ⟨forwardInitializedExactPacket M D hTime δ hδ ξ hs α Cagree (truncation k) hn k hk Q⟩⟩

end EulerPacketTerminalDatum
