/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGradeBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryCommonRadius
import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalEnvelope

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
