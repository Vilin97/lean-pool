/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionChoice
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionRapidDecay

@[expose] public section

/-! Source-only frequency choices with quantitative bounds for the actual
correction, its pressure gradient and its time derivative. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCoarseMajorant EulerPacketCorrectionConstants EulerPacketCorrectionScalar
  EulerPacketSourceFrequency EulerSobolevGevreyOperators EulerPacketCorrectionCoefficients
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)

include hδ1 hα L NB LM hΞ hF hdet

/-- Original source budgets determine fixed positive constants and a
fixed positive radius for all sufficiently large frequencies. Every
norm is evaluated on the actual correction selected by the drift-aware
construction, with no pressure or time estimate as an input. -/
theorem initialized_correction_estimates_eventually :
    ∃ ρ0 G C : ℝ, 0 < ρ0 ∧ 0 < G ∧ 0 < C ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
            (truncation k) hn k hk)),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=G ∧
        ∀ (s N : ℕ), N+6 ≤ s → ∀ t : Icc (0 : ℝ) D.T,
          weightedNorm period 6 N (ρ0/4) ((Q.fieldTower period).realization s t) ≤ C*delta
            (expansion k) ∧
          weightedNorm period 6 N (ρ0/4) ((Q.pressureTower period).realization s t) ≤ C*delta
            (expansion k) ∧
          weightedNorm period 6 N (ρ0/4) ((Q.timeDerivativeTower period).realization s t) ≤ C*delta
            (expansion k) := by
  classical
  let BC := joinedCoefficientBudget period M D hTime τ hτ hτT B NB
  let Kc := L.correctionCoefficients NB period
  obtain ⟨L',H',N',M',hprofile,wj,wm,wp,hterminal,hcost,hrc⟩ :=
    exists_initialized_budgets LM L NB BC δ ξ
  let S := Scales.ofTimeProfile L.fullProfile L.fullProfile_pos hTime.symm α hα
  have hgrowth : timeProfileChange S.growth hTime=α • L'.fullProfile := by
    rw [hprofile]
    exact Scales.ofTimeProfile_growth L.fullProfile L.fullProfile_pos hTime.symm α hα
  let cg := growth D period Kc L'.R S.H0 BC.multiplierCost
  let dg := drift L'.R S.H0 BC.multiplierCost
  let ρ0 := initialRadius L'.R Kc.M Kc.Rc
  let Ce := correctionBase D
  let Cp := correctionPressureCost D period Kc L'.R S.H0 BC.multiplierCost
  let Ct := correctionTimeCost D period Kc L'.R S.H0 BC.multiplierCost
  let C := 1+|Ce|+|Cp|+|Ct|
  have hCe : Ce ≤ C := by dsimp [C]; linarith [le_abs_self Ce, abs_nonneg Cp, abs_nonneg Ct]
  have hCp : Cp ≤ C := by dsimp [C]; linarith [le_abs_self Cp, abs_nonneg Ce, abs_nonneg Ct]
  have hCt : Ct ≤ C := by dsimp [C]; linarith [le_abs_self Ct, abs_nonneg Ce, abs_nonneg Cp]
  have hρ : 0 < ρ0 := (initialRadius_bounds L'.R Kc.M Kc.Rc
    (zero_le_one.trans L'.radius_bounds.1) (zero_le_one.trans Kc.M_one_le) Kc.Rc_nonneg).1
  have hcg : 0 < cg := growth_pos D period Kc L'.R S.H0 BC.multiplierCost
    (zero_le_one.trans L'.radius_bounds.1) BC.multiplierCost_nonneg
  refine ⟨ρ0,cg,C,hρ,hcg,by dsimp [C]; positivity,?_⟩
  filter_upwards [fixed_costs_eventually
    ({tailPolynomialConstant L'.R S.H0 BC.termCost,BC.multiplierCost,
      12*cg*D.T,8*cg*D.T*dg/ρ0,8*cg*D.T/ρ0} : Finset ℝ)] with k hk
  obtain ⟨hk,hX,hlog,hc⟩ := hk
  have hn : 1 ≤ truncation k := (truncation_bounds k (by linarith)).1
  let Q := initializedAllOrderBudget M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
    L' H' N' wj M' wm BC hrc hcost hδ1 hα hterminal wp S hgrowth Kc k hk hX hlog
    (hc _ (by simp)) (hc _ (by simp)) (hc _ (by simp [cg]))
    (hc _ (by simp [cg,dg,ρ0])) (hc _ (by simp [cg,ρ0]))
    Ξ hΞ hF hdet
  refine ⟨hk,hn,Q,rfl,rfl,rfl,?_⟩
  intro s N hN t
  have hδQ : Q.delta=delta (expansion k) := by simp only [Q,initializedAllOrderBudget]
  have hrQ : Q.reducedRadius period=ρ0/4 := by
    simp only [Q,EulerAllOrderDriftCorrection.Budget.reducedRadius,initializedAllOrderBudget,ρ0]
  have heQ : Q.correctionSize period=Ce*delta (expansion k) := by
    simp only [Q,EulerAllOrderDriftCorrection.Budget.correctionSize,initializedAllOrderBudget,
      initializedMetricBudget,sourceMetricBudgetOfFields,sourceMetricBudget,Ce,correctionBase]
    ring
  have hpQ : Q.pressureCost period (N+6) (by omega)=Cp := by
    simp only [Q,EulerAllOrderDriftCorrection.Budget.pressureCost,
      EulerAllOrderDriftCorrection.Budget.sourceCost,EulerAllOrderDriftCorrection.Budget.baseCorrectionSize,
      initializedAllOrderBudget,initializedDriftBudget,initializedSpatialBudget,initializedMetricBudget,
      sourceMetricBudgetOfFields,sourceMetricBudget,Cp,correctionPressureCost,correctionSourceCost,correctionBase]
  have htQ : Q.timeDerivativeCost period (N+6) (by omega)=Ct := by
    simp only [Q,EulerAllOrderDriftCorrection.Budget.timeDerivativeCost,
      EulerAllOrderDriftCorrection.Budget.sourceCost,EulerAllOrderDriftCorrection.Budget.baseCorrectionSize,
      initializedAllOrderBudget,initializedDriftBudget,initializedSpatialBudget,initializedMetricBudget,
      sourceMetricBudgetOfFields,sourceMetricBudget,Ct,correctionTimeCost,correctionSourceCost,correctionBase]
  have he := Q.fieldTower_reducedNorm period s N hN t
  have hp := Q.pressureTower_reducedNorm_delta period (N+6) (by omega) N (by omega) s hN t
  have ht := Q.timeDerivativeTower_reducedNorm_delta period (N+6) (by omega) N (by omega) s hN t
  rw [hrQ,heQ] at he
  rw [hrQ,hpQ,hδQ] at hp
  rw [hrQ,htQ,hδQ] at ht
  exact ⟨he.trans (mul_le_mul_of_nonneg_right hCe (delta_pos _).le),
    hp.trans (mul_le_mul_of_nonneg_right hCp (delta_pos _).le),
    ht.trans (mul_le_mul_of_nonneg_right hCt (delta_pos _).le)⟩

/-- Every fixed polynomial loss can be paid while making all three
actual weighted H⁶ norms smaller than any prescribed inverse power.
The chosen frequency works simultaneously at every finite cutoff. -/
theorem initialized_correction_with_power_loss_eventually
    (physicalCost loss p : ℝ) (hphysicalCost : 0 ≤ physicalCost) :
    ∃ ρ0 G : ℝ, 0 < ρ0 ∧ 0 < G ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
            (truncation k) hn k hk)),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=G ∧
        ∀ (s N : ℕ), N+6 ≤ s → ∀ t : Icc (0 : ℝ) D.T,
          physicalCost*k^loss*weightedNorm period 6 N (ρ0/4)
              ((Q.fieldTower period).realization s t) < k^(-p) ∧
          physicalCost*k^loss*weightedNorm period 6 N (ρ0/4)
              ((Q.pressureTower period).realization s t) < k^(-p) ∧
          physicalCost*k^loss*weightedNorm period 6 N (ρ0/4)
              ((Q.timeDerivativeTower period).realization s t) < k^(-p) := by
  obtain ⟨ρ0,G,C,hρ,hG,_hC,hQ⟩ := initialized_correction_estimates_eventually
    M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα L NB LM Cagree Ξ hΞ hF hdet
  refine ⟨ρ0,G,hρ,hG,?_⟩
  filter_upwards [hQ,correction_with_power_loss_eventually (physicalCost*C) loss p] with k hQ
    hkbound
  obtain ⟨hk,hn,Q,hδQ,hρQ,hGQ,hbounds⟩ := hQ
  refine ⟨hk,hn,Q,hδQ,hρQ,hGQ,?_⟩
  intro s N hN t
  have hscale : 0 ≤ physicalCost*k^loss := mul_nonneg hphysicalCost (Real.rpow_nonneg (by linarith)
    _)
  have hb (x : ℝ) (hx : x ≤ C*delta (expansion k)) : physicalCost*k^loss*x < k^(-p) := by
    apply (mul_le_mul_of_nonneg_left hx hscale).trans_lt
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hkbound
  exact ⟨hb _ (hbounds s N hN t).1,hb _ (hbounds s N hN t).2.1,hb _ (hbounds s N hN t).2.2⟩

end EulerPacketTerminalDatum
