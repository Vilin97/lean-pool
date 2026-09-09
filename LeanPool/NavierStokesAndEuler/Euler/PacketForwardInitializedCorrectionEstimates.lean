/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedAllOrderBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCommonRadius
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCoefficientBudgets

@[expose] public section

/-! The zero-history source data construct actual correction budgets for all
sufficiently large frequencies. All primary, coefficient, radius and frequency
guards follow from the fixed source data. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCoarseMajorant EulerPacketCorrectionConstants EulerPacketCorrectionScalar
  EulerPacketSourceFrequency EulerPacketCorrectionCoefficients EulerSobolevGevreyOperators
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)

include hδ1 hα L NB LM hΞ hF hdet

theorem forwardInitialized_correction_estimates_eventually :
    ∃ ρ0 γ C : ℝ, 0 < ρ0 ∧ 0 < γ ∧ 0 < C ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree
            (truncation k) hn k hk)),
        Q.delta = delta (expansion k) ∧ Q.initialRadius = ρ0 ∧ Q.growthCoefficient = γ ∧
        ∀ (s N : ℕ), N+6 ≤ s → ∀ t : Icc (0 : ℝ) D.T,
          weightedNorm period 6 N (ρ0/4) ((Q.fieldTower period).realization s t) ≤ C*delta
            (expansion k) ∧
          weightedNorm period 6 N (ρ0/4) ((Q.pressureTower period).realization s t) ≤ C*delta
            (expansion k) ∧
          weightedNorm period 6 N (ρ0/4) ((Q.timeDerivativeTower period).realization s t) ≤ C*delta
            (expansion k) := by
  classical
  let BC := forwardCoefficientBudget period M D hTime NB
  let Kc := L.correctionCoefficients NB period
  have hC : 0 ≤ wordCost (Fin 4) 6 δ*‖ξ‖ :=
    mul_nonneg (wordCost_nonneg 6 δ) (norm_nonneg ξ)
  obtain ⟨R',hM,hL,wm,wf,wp,hcost,hrc,hterminal⟩ :=
    EulerPacketForwardCommonRadius.exists_common_radius LM L NB BC
      (wordCost (Fin 4) 6 δ*‖ξ‖) (wordRadius (Fin 4) δ) hC
  let L' := L.enlargeRadius R' hL
  let N' := NB.enlargeRadius R' hL
  let M' := LM.enlargeRadius R' hM
  let S := Scales.ofTimeProfile L.g L.positive hTime.symm α hα
  have hgrowth : timeProfileChange S.growth hTime = α • L'.g :=
    Scales.ofTimeProfile_growth L.g L.positive hTime.symm α hα
  let cg := growthCoefficient D period Kc (2*velocity L'.R S.H0 BC.multiplierCost)
    (12*velocity L'.R S.H0 BC.multiplierCost*(4*L'.R))
  let dg := drift L'.R S.H0 BC.multiplierCost
  let ρ0 := initialRadius L'.R Kc.M Kc.Rc
  have hR0 := zero_le_one.trans L'.radius_one
  have hρ : 0 < ρ0 := (initialRadius_bounds L'.R Kc.M Kc.Rc
    hR0 (zero_le_one.trans Kc.M_one_le) Kc.Rc_nonneg).1
  have hv := velocity_nonneg L'.R S.H0 BC.multiplierCost hR0 BC.multiplierCost_nonneg
  have hcg : 0 < cg := growthCoefficient_pos D period Kc _ _ (by positivity) (by positivity)
  let Ce := correctionBase D
  let Cp := correctionPressureCost D period Kc L'.R S.H0 BC.multiplierCost
  let Ct := correctionTimeCost D period Kc L'.R S.H0 BC.multiplierCost
  let C := 1+|Ce|+|Cp|+|Ct|
  have hCe : Ce ≤ C := by dsimp [C]; linarith [le_abs_self Ce,abs_nonneg Cp,abs_nonneg Ct]
  have hCp : Cp ≤ C := by dsimp [C]; linarith [le_abs_self Cp,abs_nonneg Ce,abs_nonneg Ct]
  have hCt : Ct ≤ C := by dsimp [C]; linarith [le_abs_self Ct,abs_nonneg Ce,abs_nonneg Cp]
  refine ⟨ρ0,cg,C,hρ,hcg,by dsimp [C]; positivity,?_⟩
  filter_upwards [fixed_costs_eventually
    ({tailPolynomialConstant L'.R S.H0 BC.termCost,BC.multiplierCost,
      12*cg*D.T,8*cg*D.T*dg/ρ0,8*cg*D.T/ρ0} : Finset ℝ)] with k hk
  obtain ⟨hk,hX,hlog,hc⟩ := hk
  have hn : 1 ≤ truncation k := (truncation_bounds k (by linarith)).1
  let Q := forwardInitializedAllOrderBudget M D hTime δ hδ ξ hs α Cagree
    L' N' wf M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth Kc k hk hX hlog
    (hc _ (by simp)) (hc _ (by simp)) (hc _ (by simp [cg]))
    (hc _ (by simp [cg,dg,ρ0])) (hc _ (by simp [cg,ρ0]))
    Ξ hΞ hF hdet
  refine ⟨hk,hn,Q,rfl,rfl,rfl,?_⟩
  intro s N hN t
  have hδQ : Q.delta=delta (expansion k) := by simp only [Q,forwardInitializedAllOrderBudget]
  have hrQ : Q.reducedRadius period=ρ0/4 := by
    simp only [Q,EulerAllOrderDriftCorrection.Budget.reducedRadius,forwardInitializedAllOrderBudget,ρ0]
  have heQ : Q.correctionSize period=Ce*delta (expansion k) := by
    simp only [Q,EulerAllOrderDriftCorrection.Budget.correctionSize,forwardInitializedAllOrderBudget,
      forwardInitializedMetricBudget,sourceMetricBudgetOfFields,sourceMetricBudget,Ce,correctionBase]
    ring
  have hpQ : Q.pressureCost period (N+6) (by omega)=Cp := by
    simp only [Q,EulerAllOrderDriftCorrection.Budget.pressureCost,
      EulerAllOrderDriftCorrection.Budget.sourceCost,EulerAllOrderDriftCorrection.Budget.baseCorrectionSize,
      forwardInitializedAllOrderBudget,forwardInitializedDriftBudget,forwardInitializedSpatialBudget,
      forwardInitializedMetricBudget,sourceMetricBudgetOfFields,sourceMetricBudget,Cp,
      correctionPressureCost,correctionSourceCost,correctionBase]
  have htQ : Q.timeDerivativeCost period (N+6) (by omega)=Ct := by
    simp only [Q,EulerAllOrderDriftCorrection.Budget.timeDerivativeCost,
      EulerAllOrderDriftCorrection.Budget.sourceCost,EulerAllOrderDriftCorrection.Budget.baseCorrectionSize,
      forwardInitializedAllOrderBudget,forwardInitializedDriftBudget,forwardInitializedSpatialBudget,
      forwardInitializedMetricBudget,sourceMetricBudgetOfFields,sourceMetricBudget,Ct,
      correctionTimeCost,correctionSourceCost,correctionBase]
  have he := Q.fieldTower_reducedNorm period s N hN t
  have hp := Q.pressureTower_reducedNorm_delta period (N+6) (by omega) N (by omega) s hN t
  have ht := Q.timeDerivativeTower_reducedNorm_delta period (N+6) (by omega) N (by omega) s hN t
  rw [hrQ,heQ] at he
  rw [hrQ,hpQ,hδQ] at hp
  rw [hrQ,htQ,hδQ] at ht
  exact ⟨he.trans (mul_le_mul_of_nonneg_right hCe (delta_pos _).le),
    hp.trans (mul_le_mul_of_nonneg_right hCp (delta_pos _).le),
    ht.trans (mul_le_mul_of_nonneg_right hCt (delta_pos _).le)⟩

end EulerPacketTerminalDatum
