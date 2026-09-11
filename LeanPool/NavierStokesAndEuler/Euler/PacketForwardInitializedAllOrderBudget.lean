/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceFrequency
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionGrowth
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants
public import LeanPool.NavierStokesAndEuler.Euler.DriftCorrectionBudget
public import LeanPool.NavierStokesAndEuler.Euler.SobolevDriftNorm
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldDrift
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolevBudget

/-! The literal zero-history initialized packet supplies a complete drift-aware
all-order correction budget, from fixed source data and explicit scalar
frequency guards. No solution or energy estimate is assumed. -/

section

/-! Actual finite-order correction budgets for the zero-history initialized packet.
All coefficient and field bounds are supplied by the checked constructions. -/

section

/-! Cutoff-independent background, derivative, drift and residual budgets
for the actual zero-history correction data. -/

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant EulerPacketCorrectionConstants
  EulerCylinderSobolevSpace EulerSobolevGevreyOperators EulerSobolevDriftNorm
  EulerFunctionalVelocity EulerSobolevTransport

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
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
  (Cagree : SourceCoefficientAgreement M D)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth hbase

theorem forwardInitializedCorrection_background (s Q : ℕ) (hQ : Q + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ * (4 * L.R) ≤ 1 / 2) (t : Icc (0 : ℝ) D.T) :
    weightedNorm period 6 Q ρ
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k
          hk).approximation.realization s t)
        ≤ 2*velocity L.R S.H0 BC.multiplierCost := by
  have hz := forwardInitializedNormalizedField_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  exact hz.toFieldTower_weightedNorm_le_two (by have := L.radius_one; linarith)
    (velocity_nonneg L.R S.H0 BC.multiplierCost (zero_le_one.trans L.radius_one)
      BC.multiplierCost_nonneg) s Q hQ ρ hρ hsmall t

theorem forwardInitializedCorrection_background_derivative (s Q : ℕ) (hQ : Q + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ * (4 * L.R) ≤ 1 / 2) (t : Icc (0 : ℝ) D.T) :
    (∑ i : Fin 4, weightedNorm period 6 Q ρ (derivativeOperator period s i
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k
          hk).approximation.realization (s+1) t)))
        ≤ 12*velocity L.R S.H0 BC.multiplierCost*(4*L.R) := by
  have hz := forwardInitializedNormalizedField_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  exact hz.toFieldTower_weightedDerivativeNorm_le_twelve (by have := L.radius_one; linarith)
    (velocity_nonneg L.R S.H0 BC.multiplierCost (zero_le_one.trans L.radius_one)
      BC.multiplierCost_nonneg) s Q hQ ρ hρ hsmall t

theorem forwardInitializedCorrection_drift (s Q : ℕ) (hQ : Q + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ * (4 * L.R) ≤ 1 / 2) (t : Icc (0 : ℝ) D.T) :
    weightedDriftNorm period 6 Q ρ (velocityMap (velocityComponents k⁻¹ D.m₀))
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k
          hk).approximation.realization s t)
        ≤ drift L.R S.H0 BC.multiplierCost/k := by
  have hz := forwardInitializedNormalizedField_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  have hn := forwardInitializedNormalizedField_normal_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  have hR0 := zero_le_one.trans L.radius_one
  have hk0 : 0 < k := by linarith
  have hd := hz.toFieldTower_weightedDrift_le_two k⁻¹ D.m₀ hn (by linarith)
    (velocity_nonneg L.R S.H0 BC.multiplierCost hR0 BC.multiplierCost_nonneg)
    (div_nonneg (normal_nonneg L.R S.H0 BC.multiplierCost hR0 BC.multiplierCost_nonneg) hk0.le)
    s Q hQ ρ hρ hsmall t
  exact hd.trans_eq (drift_div_frequency L.R S.H0 BC.multiplierCost k hk0)

theorem forwardInitializedCorrection_residual (X : ℝ)
    (hcoef : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ)) (hX : 6 ≤ X) (hNX : X - 1 ≤ (N : ℝ))
    (s Q : ℕ) (hQ : Q + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (hsmall : ρ * (4 * L.R) ≤ 1 / 2) (t : Icc (0 : ℝ) D.T) :
    weightedNorm period 6 Q ρ
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k
          hk).residual.realization s t)
        ≤ 2*Real.exp (-(7/10)*X*Real.log k) := by
  have hr := forwardInitializedNormalizedResidualField_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth Cagree N hN k X hk hbase hcoef hX hNX
  exact hr.toFieldTower_weightedNorm_le_two (by have := L.radius_one; linarith)
    (Real.exp_pos _).le s Q hQ ρ hρ hsmall t

end EulerPacketTerminalDatum

end
end

end

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

end
end

end

section

/-! The zero-history initialized approximation satisfies the lifted divergence
constraint for an actual volume-preserving source deformation. -/

@[expose] public section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant EulerPacketCorrectionConstants
  EulerPacketCorrectionCoefficients EulerPacketCorrectionScalar EulerPacketSourceFrequency
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (Cagree : SourceCoefficientAgreement M D)
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
  (Kc : CorrectionCoefficientBudget D period)

local notation "cg" => growthCoefficient D period Kc (2*velocity L.R S.H0 BC.multiplierCost)
  (12*velocity L.R S.H0 BC.multiplierCost*(4*L.R))
local notation "dg" => drift L.R S.H0 BC.multiplierCost
local notation "ρg" => initialRadius L.R Kc.M Kc.Rc

/-- Explicit scalar guards suffice because every analytic input to the
all-order correction theorem is supplied by the constructed packet. -/
def forwardInitializedAllOrderBudget (k : ℝ) (hk : 4 ≤ k)
    (hX : 64 ≤ expansion k) (hlog : 1 ≤ Real.log k)
    (htail : tailPolynomialConstant L.R S.H0 BC.termCost ≤ smallPower k)
    (hcoefficient : BC.multiplierCost ≤ smallPower k)
    (hgrowthCost : 12 * cg * D.T ≤ smallPower k)
    (hdriftCost : 8 * cg * D.T * dg / ρg ≤ smallPower k)
    (herrorCost : 8 * cg * D.T / ρg ≤ smallPower k)
    (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
    (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1) :
    EulerAllOrderDriftCorrection.Budget period D.T_pos
      (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree
        (truncation k) (truncation_bounds k (by linarith)).1 k hk) := by
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hn := (truncation_bounds k hk1).1
  have hnx := (truncation_bounds k hk1).2.1
  have hR0 := zero_le_one.trans L.radius_one
  have hM0 := zero_le_one.trans Kc.M_one_le
  have hb := tailBase_frequency L.R S.H0 BC.termCost k BC.termCost_nonneg hk1 htail
  have hc := hcoefficient.trans (smallPower_le_gradeCap k hk1)
  have hx6 : 6 ≤ expansion k := by linarith
  have hv := velocity_nonneg L.R S.H0 BC.multiplierCost hR0 BC.multiplierCost_nonneg
  have hcg : 0 < cg := growthCoefficient_pos D period Kc _ _ (by positivity) (by positivity)
  have hdg := drift_nonneg L.R S.H0 BC.multiplierCost hR0 BC.multiplierCost_nonneg
  have hinit := initialRadius_bounds L.R Kc.M Kc.Rc hR0 hM0 Kc.Rc_nonneg
  have hscalar := correction_guards cg D.T dg ρg k hk1 hinit.1 hX hlog
    hgrowthCost hdriftCost herrorCost
  let ρ := radius D.T cg dg ρg k (expansion k)
  have hρbounds (t : Icc (0 : ℝ) D.T) : ρg/2 ≤ ρ t ∧ ρ t ≤ ρg :=
    radius_bounds D.T cg dg ρg k (expansion k) hcg.le hdg hk0 hscalar.2 t
  have hρ (t : Icc (0 : ℝ) D.T) : 0 < ρ t :=
    (half_pos hinit.1).trans_le (hρbounds t).1
  have hpacket (t : Icc (0 : ℝ) D.T) : ρ t*(4*L.R) ≤ 1/2 :=
    (mul_le_mul_of_nonneg_right (hρbounds t).2 (by positivity)).trans hinit.2.1
  have hpressure (t : Icc (0 : ℝ) D.T) : 4*Kc.M*(ρ t*Kc.Rc) ≤ 1 :=
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hρbounds t).2 Kc.Rc_nonneg) (by positivity)).trans hinit.2.2.1
  refine {
    metric := forwardInitializedMetricBudget M D hTime δ hδ ξ hs α Cagree (truncation k) hn k hk 0
    radius := ρ
    growthCoefficient := cg
    delta := delta (expansion k)
    initialRadius := ρg
    spatial := fun q hq => forwardInitializedDriftBudget M D hTime δ hδ ξ hs α Cagree
      (truncation k) hn k hk L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth hb
      (expansion k) hc hx6 hnx Kc ρ hρ hpacket hpressure q hq
    growth_bound := ?_
    delta_pos := delta_pos (expansion k)
    delta_le_one := delta_le_one (expansion k)
    radius_pos := hinit.1
    decay := ?_
    scale := ?_
    small := ?_
    radius_eq := ?_
    divergence := ?_ }
  · intro q hq
    exact (forwardInitializedDriftBudget_growth M D hTime δ hδ ξ hs α Cagree
      (truncation k) hn k hk L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth hb
      (expansion k) hc hx6 hnx Kc ρ hρ hpacket hpressure q hq).le
  · intro q hq
    exact hscalar.2
  · intro q hq
    exact hinit.2.2.2
  · intro q hq
    exact hscalar.1
  · intro q hq t
    rfl
  · exact forwardInitializedCorrectionData_divergence M D hTime δ hδ ξ hs α Cagree
      (truncation k) hn k hk Ξ hΞ hF hdet

end EulerPacketTerminalDatum
