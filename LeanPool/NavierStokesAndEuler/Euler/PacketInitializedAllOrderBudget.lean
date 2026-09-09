/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedSpatialBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceFrequency
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedSolenoidal

/-! The literal initialized packet supplies a complete drift-aware
all-order correction budget, from fixed source data and explicit scalar
frequency guards. No solution or energy estimate is assumed. -/

@[expose] public section


noncomputable section

namespace EulerPacketCorrectionConstants

open EulerPacketCorrectionCoefficients

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (Kc : CorrectionCoefficientBudget D P)

/-- Growth, given by `growthCoefficient D P Kc (2*velocity R H C) (12*velocity R H C*(4*R))`. -/
def growth (R H C : ℝ) : ℝ :=
  growthCoefficient D P Kc (2*velocity R H C) (12*velocity R H C*(4*R))

theorem growth_pos (R H C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    0 < growth D P Kc R H C := by
  have hv := velocity_nonneg R H C hR hC
  exact growthCoefficient_pos D P Kc _ _ (by positivity) (by positivity)

end EulerPacketCorrectionConstants

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant EulerPacketCorrectionConstants
  EulerPacketCorrectionCoefficients EulerPacketCorrectionScalar EulerPacketSourceFrequency
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (Cagree : SourceCoefficientAgreement M D)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := period) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData period M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)
  (Kc : CorrectionCoefficientBudget D period)

local notation "cg" => growth D period Kc L.R S.H0 BC.multiplierCost
local notation "dg" => drift L.R S.H0 BC.multiplierCost
local notation "ρg" => initialRadius L.R Kc.M Kc.Rc

/-- Explicit scalar guards suffice because every analytic input to the
all-order correction theorem is supplied by the constructed packet. -/
def initializedAllOrderBudget (k : ℝ) (hk : 4 ≤ k)
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
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
        (truncation k) (truncation_bounds k (by linarith)).1 k hk) := by
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hn := (truncation_bounds k hk1).1
  have hnx := (truncation_bounds k hk1).2.1
  have hR0 := zero_le_one.trans L.radius_bounds.1
  have hM0 := zero_le_one.trans Kc.M_one_le
  have hb := tailBase_frequency L.R S.H0 BC.termCost k BC.termCost_nonneg hk1 htail
  have hc := hcoefficient.trans (smallPower_le_gradeCap k hk1)
  have hx6 : 6 ≤ expansion k := by linarith
  have hcg := growth_pos D period Kc L.R S.H0 BC.multiplierCost hR0 BC.multiplierCost_nonneg
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
    metric := initializedMetricBudget M D hTime τ hτ hτT B δ hδ ξ hs α Cagree (truncation k) hn k
        hk 0
    radius := ρ
    growthCoefficient := cg
    delta := delta (expansion k)
    initialRadius := ρg
    spatial := fun q hq => initializedDriftBudget M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
      (truncation k) hn k hk L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth hb
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
    exact (initializedDriftBudget_growth M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
      (truncation k) hn k hk L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth hb
      (expansion k) hc hx6 hnx Kc ρ hρ hpacket hpressure q hq).le
  · intro q hq
    exact hscalar.2
  · intro q hq
    exact hinit.2.2.2
  · intro q hq
    exact hscalar.1
  · intro q hq t
    rfl
  · exact initializedCorrectionData_divergence M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
      (truncation k) hn k hk Ξ hΞ hF hdet

end EulerPacketTerminalDatum
