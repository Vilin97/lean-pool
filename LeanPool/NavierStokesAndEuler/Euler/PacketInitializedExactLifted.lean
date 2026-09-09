/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedResidualEquation
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionChoice
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionParity

@[expose] public section

/-! Source budgets and the actual initialized residual construct exact
corrected lifted packets at every sufficiently large frequency. -/

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerGevreyMetricEstimate
  EulerCorrectionOperators EulerSobolevCoefficientPressure EulerVolterraConvolution
  EulerCorrectionAssembly EulerCylinderReflection EulerCorrectionResidualCancellation

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} (hT : 0 < T) (A : Data P T)

/-- The output fields and all their properties are conclusions of the
constructed correction and the verified approximate residual. -/
structure ExactLiftedPacket (B : Budget P hT A) where
  velocity : FieldTower P T
  pressure : FieldTower P T
  zero_initial_correction : ∀ q,
    velocity.realization q ⟨0,le_rfl,hT.le⟩-A.approximation.realization q ⟨0,le_rfl,hT.le⟩=0
  divergence : ∀ t, velocity.field t ∈ divergenceFreeSpace P A.κ A.direction
  gradient : ∀ t, pressure.field t ∈ gradientSpace P A.κ A.direction
  energy : ∀ (n : ℕ) t,
    energyNorm P n (by omega : n+6 ≤ (n+6)+1) (B.radius t) (B.metric.operatorPath P t)
        (velocity.realization ((n+6)+1) t-A.approximation.realization ((n+6)+1) t) ≤
      2*(B.spatial (n+6) (by omega)).full.residual*Real.exp (3*B.growthCoefficient*t.val) ∧
    energyNorm P n (by omega : n+6 ≤ (n+6)+1) (B.radius t) (B.metric.operatorPath P t)
        (velocity.realization ((n+6)+1) t-A.approximation.realization ((n+6)+1) t) ≤ B.delta/2
  equation : ∀ (q : ℕ) (hq : 6 ≤ q) t (ht : t ∈ Ioo 0 T),
    HasDerivAt (extendPath T hT.le (velocity.realization q))
      (-nonlinearity P (A.atOrder P q) hq ⟨t,ht.1.le,ht.2.le⟩
        (velocity.realization (q+1) ⟨t,ht.1.le,ht.2.le⟩)-
        coefficientSobolevOperator P (A.metric.jet q ⟨t,ht.1.le,ht.2.le⟩)
          (pressure.realization q ⟨t,ht.1.le,ht.2.le⟩)) t

variable {hT A}

def exactPacketOfResidual (B : Budget P hT A) (R : ApproximationResidual P hT A) :
    ExactLiftedPacket P hT A B where
  velocity := B.correctedFieldTower P
  pressure := B.correctedPressureTower P R
  zero_initial_correction q := by rw [B.correctedFieldTower_initial P q,sub_self]
  divergence := B.correctedFieldTower_divergence P
  gradient := B.correctedPressureTower_gradient P R
  energy := B.correctedFieldTower_error_energy P
  equation := B.correctedFieldTower_hasDerivAt P R

theorem exactPacketOfResidual_velocity_odd (B : Budget P hT A)
    (R : ApproximationResidual P hT A) (E : ParityData P A) (t : Icc (0 : ℝ) T) :
    -reflection P ((exactPacketOfResidual P B R).velocity.field t) =
      (exactPacketOfResidual P B R).velocity.field t := by
  change -reflection P (A.approximation.field t+B.commonPath P t) =
    A.approximation.field t+B.commonPath P t
  rw [map_add,neg_add,E.approximation,B.commonPath_odd P E]

end EulerAllOrderDriftCorrection

namespace EulerPacketTerminalDatum

open Set Filter EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerAllOrderDriftCorrection
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerCylinderReflection
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def initializedExactPacket (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (Q : Budget period D.T_pos
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk)) :
    ExactLiftedPacket period D.T_pos
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk) Q :=
  exactPacketOfResidual period Q
    (initializedApproximationResidual M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk)

theorem initializedExactPacket_velocity_odd
    (eM : EulerMeanPacketProvider.EvenData M)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hBH : ∀ t x, B.H.field t (-x) = B.H.field t x)
    (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k)
    (Q : Budget period D.T_pos
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk))
    (t : Icc (0 : ℝ) D.T) :
    -reflection period
      ((initializedExactPacket M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk Q).velocity.field
        t) =
      (initializedExactPacket M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk Q).velocity.field t
        :=
  exactPacketOfResidual_velocity_odd period Q _
    (initializedCorrectionParityData M D hTime τ hτ hτT B δ hδ ξ hs α
      eM hSym hF hDM hBH Cagree N hN k hk) t

/-- No inverse budget, residual equation or pressure is postulated here.
The original source data construct the budget and the exact corrected pair
for every sufficiently large frequency, with fixed positive radius and cost. -/
theorem initialized_exact_lifted_packets_eventually
    (hδ1 : δ ≤ 1) (hα : 0 < α)
    (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
    (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
    {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
    (Cagree : SourceCoefficientAgreement M D)
    (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
    (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1) :
    ∃ ρ0 C : ℝ, 0 < ρ0 ∧ 0 < C ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree (truncation k) hn k
            hk)),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=C ∧
          Nonempty (ExactLiftedPacket period D.T_pos
            (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree (truncation k) hn k
              hk) Q) := by
  obtain ⟨ρ0,C,hρ,hC,he⟩ := initialized_correction_budgets_eventually M D hTime τ hτ hτT B
    δ hδ hδ1 ξ hs α hα L NB LM Cagree Ξ hΞ hF hdet
  refine ⟨ρ0,C,hρ,hC,?_⟩
  filter_upwards [he] with k hk
  obtain ⟨hk,hn,Q,hδQ,hρQ,hCQ⟩ := hk
  exact ⟨hk,hn,Q,hδQ,hρQ,hCQ,
    ⟨initializedExactPacket M D hTime τ hτ hτT B δ hδ ξ hs α Cagree (truncation k) hn k hk Q⟩⟩

end EulerPacketTerminalDatum
