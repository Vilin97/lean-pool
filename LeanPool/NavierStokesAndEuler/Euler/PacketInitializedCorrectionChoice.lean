/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedAllOrderBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketGevreyProfileChoice
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedCoefficientBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGradeBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryCommonRadius
import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalEnvelope

/-! The original source budgets produce actual correction budgets for all
sufficiently large frequencies. Primary estimates, coefficient estimates,
radius guards and frequency guards are conclusions of the construction. -/

section

/-! One source-dependent radius accommodates the literal terminal wave, the
primary endpoint solve, all later linear solves, and every recursive grade. -/

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open EulerPacketCylinderField EulerPacketProfileRecursion EulerParameterWordGevrey

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le)}
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (BC : CoefficientBudget C) (δ : ℝ) (ξ : U)

include LM NB

/-- The terminal amplitude and the recursive grade do not enter this radius
choice.  The original time profile is preserved exactly. -/
theorem exists_initialized_budgets :
    ∃ (L' : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
      (H' : EulerTransversePacketPrimary.Budget L')
      (N' : EulerTransversePacketJoin.NormalBudget D 6 L'.R)
      (M' : EulerMeanPacketProvider.Budget M 6 L'.R),
      L'.fullProfile = L.fullProfile ∧
      EulerTransversePacketJoin.Budget.GradeGuards (P := period) L' N' ∧
      EulerMeanPacketProvider.Budget.GradeGuards M' ∧
      EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H' N'
        (wordCost (Fin 4) 6 δ*‖ξ‖) ∧
      wordRadius (Fin 4) δ ≤ L'.R ∧ BC.termCost ≤ L'.R ∧
      sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L'.R := by
  let Lp := EulerTransversePacketPrimary.enlargeForPrimary L (wordRadius (Fin 4) δ)
  have hLp : L.R ≤ Lp.R := EulerTransversePacketPrimary.le_requiredRadius L _
  let Np := NB.enlargeRadius Lp.R hLp
  let Hp := EulerTransversePacketPrimary.requiredBudget L (wordRadius (Fin 4) δ)
  let terminalCost := wordCost (Fin 4) 6 δ*‖ξ‖
  have ht : 0 ≤ terminalCost := mul_nonneg (wordCost_nonneg 6 δ) (norm_nonneg ξ)
  let R' := max (EulerPacketCommonRadius.commonRadius LM Lp Np BC)
    (Hp.gradeRadius (P := period) Np terminalCost)
  obtain ⟨hm,hl,wm,wl,hc,hrc⟩ :=
    EulerPacketCommonRadius.commonRadius_guards LM Lp Np BC R' (le_max_left _ _)
  obtain ⟨hl',wp⟩ := Hp.gradeRadius_guards Np terminalCost ht R' (le_max_right _ _)
  refine ⟨Lp.enlargeRadius R' hl, Hp.enlargeRadius R' hl,
    Np.enlargeRadius R' hl, LM.enlargeRadius R' hm, rfl, wl, wm, ?_, ?_, hc, hrc⟩
  · exact wp
  · exact (EulerTransversePacketPrimary.extra_le_requiredRadius L (wordRadius (Fin 4) δ)).trans hl

end EulerPacketTerminalDatum

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCoarseMajorant EulerPacketCorrectionConstants EulerPacketCorrectionScalar
  EulerPacketSourceFrequency
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)

include hδ1 hα L NB LM hΞ hF hdet

/-- One source-dependent initial radius and growth constant work at all
sufficiently large frequencies for the literal truncation floor(k^ϑ). -/
theorem initialized_correction_budgets_eventually :
    ∃ ρ0 C : ℝ, 0 < ρ0 ∧ 0 < C ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
            (truncation k) hn k hk)),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=C := by
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
  have hρ : 0 < ρ0 := (initialRadius_bounds L'.R Kc.M Kc.Rc
    (zero_le_one.trans L'.radius_bounds.1) (zero_le_one.trans Kc.M_one_le) Kc.Rc_nonneg).1
  have hcg : 0 < cg := growth_pos D period Kc L'.R S.H0 BC.multiplierCost
    (zero_le_one.trans L'.radius_bounds.1) BC.multiplierCost_nonneg
  refine ⟨ρ0,cg,hρ,hcg,?_⟩
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
  refine ⟨hk,hn,Q,?_,?_,?_⟩ <;>
    simp only [Q,initializedAllOrderBudget,ρ0,cg]

end EulerPacketTerminalDatum
