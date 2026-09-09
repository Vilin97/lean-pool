/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionGrowth
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants
public import LeanPool.NavierStokesAndEuler.Euler.DriftCorrectionBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionNorms

/-! Actual finite-order correction budgets for the zero-history initialized packet.
All coefficient and field bounds are supplied by the checked constructions. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant EulerPacketCorrectionConstants
  EulerPacketCorrectionCoefficients EulerCorrectionEnergyData EulerCorrectionEnergyMajorants

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (Cagree : SourceCoefficientAgreement M D)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)

/-- Forward initialized metric budget, constructed using `sourceMetricBudgetOfFields`. -/
def forwardInitializedMetricBudget (q : ℕ) :
    MetricBudget period D.T D.T_pos.le
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk).atOrder period
          (q+1)) :=
  sourceMetricBudgetOfFields D period k⁻¹
    (by rw [abs_of_pos (inv_pos.mpr (by linarith : 0 < k))]
        exact inv_le_one_of_one_le₀ (by linarith))
    (forwardInitializedNormalizedField M D hTime δ hδ ξ hs α N k)
    (forwardInitializedNormalizedResidualField M D hTime δ hδ ξ hs α Cagree N hN k hk) q

variable
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData period M D (InitialData.zero period D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.g)
  (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
  (X : ℝ) (hcoef : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ)) (hX : 6 ≤ X) (hNX : X - 1 ≤ (N : ℝ))
  (Kc : CorrectionCoefficientBudget D period)
  (ρ : C(Icc (0 : ℝ) D.T, ℝ)) (hρ : ∀ t, 0 < ρ t)
  (hpacket : ∀ t, ρ t * (4 * L.R) ≤ 1 / 2)
  (hpressure : ∀ t, 4 * Kc.M * (ρ t * Kc.Rc) ≤ 1)

/-- All four field estimates and all coefficient estimates are actual
properties of the initialized source data at this finite Sobolev order. -/
def forwardInitializedSpatialBudget (q : ℕ) (hq : 6 ≤ q) :
    SpatialBudget period (by omega : 6 ≤ (q+1)+1)
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk).atOrder period
          ((q+1)+1))
      (q-4) ρ where
  Rc := Kc.Rc
  M := Kc.M
  B := Kc.B
  B0 := 2*velocity L.R S.H0 BC.multiplierCost
  B1 := 12*velocity L.R S.H0 BC.multiplierCost*(4*L.R)
  A0 := Kc.A0
  A2 := Kc.A2
  residual := 2*Real.exp (-(7/10)*X*Real.log k)
  Rc_nonneg := Kc.Rc_nonneg
  M_one_le := Kc.M_one_le
  B_nonneg := Kc.B_nonneg
  B0_nonneg := mul_nonneg (by norm_num)
    (velocity_nonneg L.R S.H0 BC.multiplierCost (zero_le_one.trans L.radius_one)
        BC.multiplierCost_nonneg)
  B1_nonneg := mul_nonneg (mul_nonneg (by norm_num)
    (velocity_nonneg L.R S.H0 BC.multiplierCost (zero_le_one.trans L.radius_one)
        BC.multiplierCost_nonneg))
    (mul_nonneg (by norm_num) (zero_le_one.trans L.radius_one))
  A0_nonneg := Kc.A0_nonneg
  A2_nonneg := Kc.A2_nonneg
  residual_pos := mul_pos (by norm_num) (Real.exp_pos _)
  radius_pos := hρ
  inverse_five t := Kc.inverse_five ((q+1)+1) (by omega) t
  inverse_six t := Kc.inverse_six ((q+1)+1) (by omega) t
  radius_small := hpressure
  metric_derivatives t l hl _ := Kc.metric_derivatives ((q+1)+1) t l hl
  metric_base t r hr := Kc.metric_base ((q+1)+1) t r hr
  background t := forwardInitializedCorrection_background M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth Cagree N hN k hk hbase
    (((q+1)+1)+1) (q-4) (by omega) (ρ t) (hρ t) (hpacket t) t
  background_derivative t := forwardInitializedCorrection_background_derivative M D hTime δ hδ ξ hs
      α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth Cagree N hN k hk hbase
    ((q+1)+1) (q-4) (by omega) (ρ t) (hρ t) (hpacket t) t
  linear t := Kc.linear ((q+1)+1) (q-4) (ρ t) (hρ t) (hpressure t) t
  quadratic t := Kc.quadratic k⁻¹
    (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk).scale_bound
    ((q+1)+1) (q-4) (ρ t) (hρ t) (hpressure t) t
  residual_bound t := forwardInitializedCorrection_residual M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth Cagree N hN k hk hbase
    X hcoef hX hNX ((q+1)+1) (q-4) (by omega) (ρ t) (hρ t) (hpacket t) t

/-- The small drift envelope is kept separate from the full background. -/
def forwardInitializedDriftBudget (q : ℕ) (hq : 6 ≤ q) :
    EulerDriftCorrectionBudget.Budget period (by omega : 6 ≤ (q+1)+1)
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk).atOrder period
          ((q+1)+1))
      (q-4) ρ where
  full := forwardInitializedSpatialBudget M D hTime δ hδ ξ hs α Cagree N hN k hk
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth hbase X hcoef hX hNX Kc ρ hρ hpacket hpressure
        q hq
  drift := drift L.R S.H0 BC.multiplierCost/k
  drift_nonneg := div_nonneg
    (drift_nonneg L.R S.H0 BC.multiplierCost (zero_le_one.trans L.radius_one)
        BC.multiplierCost_nonneg)
    (by linarith)
  drift_bound t := forwardInitializedCorrection_drift M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth Cagree N hN k hk hbase
    (((q+1)+1)+1) (q-4) (by omega) (ρ t) (hρ t) (hpacket t) t

theorem forwardInitializedDriftBudget_growth (q : ℕ) (hq : 6 ≤ q) :
    combinedConstant period
      (forwardInitializedDriftBudget M D hTime δ hδ ξ hs α Cagree N hN k hk
        L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth hbase X hcoef hX hNX Kc ρ hρ hpacket
            hpressure q hq).full
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk).metricBudget
          period D.T_pos.le
        (forwardInitializedMetricBudget M D hTime δ hδ ξ hs α Cagree N hN k hk 0) (q+1)) =
      growthCoefficient D period Kc (2*velocity L.R S.H0 BC.multiplierCost)
        (12*velocity L.R S.H0 BC.multiplierCost*(4*L.R)) := rfl

end EulerPacketTerminalDatum
