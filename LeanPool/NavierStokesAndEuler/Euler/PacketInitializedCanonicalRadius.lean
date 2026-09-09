/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryCommonRadius
import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalEnvelope

/-! The literal common radius of the initialized packet, with named
budgets that retain it. Quantitative bounds must concern this radius,
rather than an arbitrary witness of a radius-existence theorem. -/

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

/-- Primary radius budget: an abbreviation for `EulerTransversePacketPrimary.enlargeForPrimary L
(wordRadius (Fin 4) δ)`. -/
abbrev primaryRadiusBudget := EulerTransversePacketPrimary.enlargeForPrimary L (wordRadius (Fin 4)
    δ)

/-- Primary radius normal: an abbreviation for `NB.enlargeRadius (primaryRadiusBudget L δ).R
(EulerTransversePacketPrimary.le_requiredRadius L _)`. -/
abbrev primaryRadiusNormal := NB.enlargeRadius (primaryRadiusBudget L δ).R
  (EulerTransversePacketPrimary.le_requiredRadius L _)

/-- Primary radius primary: an abbreviation for `EulerTransversePacketPrimary.requiredBudget L
(wordRadius (Fin 4) δ)`. -/
abbrev primaryRadiusPrimary := EulerTransversePacketPrimary.requiredBudget L (wordRadius (Fin 4) δ)

/-- Initialized radius, constructed using `max`. -/
def initializedRadius : ℝ :=
  max (EulerPacketCommonRadius.commonRadius LM (primaryRadiusBudget L δ) (primaryRadiusNormal L NB
      δ) BC)
    ((primaryRadiusPrimary L δ).gradeRadius (P := period) (primaryRadiusNormal L NB δ)
      (wordCost (Fin 4) 6 δ*‖ξ‖))

include NB BC ξ in
theorem primary_le_initializedRadius :
    (primaryRadiusBudget L δ).R ≤ initializedRadius LM L NB BC δ ξ :=
  (EulerPacketCommonRadius.commonRadius_bounds LM (primaryRadiusBudget L δ)
    (primaryRadiusNormal L NB δ) BC).2.1.trans (le_max_left _ _)

include L NB BC δ ξ in
theorem mean_le_initializedRadius : Rm ≤ initializedRadius LM L NB BC δ ξ :=
  (EulerPacketCommonRadius.commonRadius_bounds LM (primaryRadiusBudget L δ)
    (primaryRadiusNormal L NB δ) BC).1.trans (le_max_left _ _)

/-- Initialized joined budget, given by `(primaryRadiusBudget L δ).enlargeRadius
(initializedRadius LM L NB BC δ ξ) (primary_le_initializedRadius LM L NB BC δ ξ)`. -/
def initializedJoinedBudget : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6 :=
  (primaryRadiusBudget L δ).enlargeRadius (initializedRadius LM L NB BC δ ξ)
    (primary_le_initializedRadius LM L NB BC δ ξ)

theorem initializedPrimaryBudget : EulerTransversePacketPrimary.Budget
    (initializedJoinedBudget LM L NB BC δ ξ) :=
  (primaryRadiusPrimary L δ).enlargeRadius (initializedRadius LM L NB BC δ ξ)
    (primary_le_initializedRadius LM L NB BC δ ξ)

/-- Initialized normal budget, given by `(primaryRadiusNormal L NB δ).enlargeRadius
(initializedRadius LM L NB BC δ ξ) (primary_le_initializedRadius LM L NB BC δ ξ)`. -/
def initializedNormalBudget : EulerTransversePacketJoin.NormalBudget D 6
    (initializedRadius LM L NB BC δ ξ) :=
  (primaryRadiusNormal L NB δ).enlargeRadius (initializedRadius LM L NB BC δ ξ)
    (primary_le_initializedRadius LM L NB BC δ ξ)

/-- Initialized mean budget, given by `LM.enlargeRadius (initializedRadius LM L NB BC δ ξ)
(mean_le_initializedRadius LM L NB BC δ ξ)`. -/
def initializedMeanBudget : EulerMeanPacketProvider.Budget M 6
    (initializedRadius LM L NB BC δ ξ) :=
  LM.enlargeRadius (initializedRadius LM L NB BC δ ξ) (mean_le_initializedRadius LM L NB BC δ ξ)

@[simp] theorem initializedJoinedBudget_radius :
    (initializedJoinedBudget LM L NB BC δ ξ).R=initializedRadius LM L NB BC δ ξ := rfl

@[simp] theorem initializedJoinedBudget_profile :
    (initializedJoinedBudget LM L NB BC δ ξ).fullProfile=L.fullProfile := rfl

/-- All the actual constructed budgets use the named canonical radius.
The profile and every coefficient cost are unchanged by enlargement. -/
theorem initializedRadius_guards :
    EulerTransversePacketJoin.Budget.GradeGuards (P := period)
      (initializedJoinedBudget LM L NB BC δ ξ) (initializedNormalBudget LM L NB BC δ ξ) ∧
    EulerMeanPacketProvider.Budget.GradeGuards (initializedMeanBudget LM L NB BC δ ξ) ∧
    EulerTransversePacketPrimary.Budget.GradeGuards (P := period)
      (initializedPrimaryBudget LM L NB BC δ ξ) (initializedNormalBudget LM L NB BC δ ξ)
      (wordCost (Fin 4) 6 δ*‖ξ‖) ∧
    wordRadius (Fin 4) δ ≤ initializedRadius LM L NB BC δ ξ ∧
    BC.termCost ≤ initializedRadius LM L NB BC δ ξ ∧
    sobolevCoefficientRadius (Fin 4) BC.Rc ≤ initializedRadius LM L NB BC δ ξ := by
  have hc := EulerPacketCommonRadius.commonRadius_guards LM (primaryRadiusBudget L δ)
    (primaryRadiusNormal L NB δ) BC (initializedRadius LM L NB BC δ ξ) (le_max_left _ _)
  have hp := (primaryRadiusPrimary L δ).gradeRadius_guards (primaryRadiusNormal L NB δ)
    (wordCost (Fin 4) 6 δ*‖ξ‖) (mul_nonneg (wordCost_nonneg 6 δ) (norm_nonneg ξ))
    (initializedRadius LM L NB BC δ ξ) (le_max_right _ _)
  obtain ⟨hm,hl,wm,wl,hcost,hrc⟩ := hc
  obtain ⟨hl',wp⟩ := hp
  exact ⟨wl,wm,wp,(EulerTransversePacketPrimary.extra_le_requiredRadius L _).trans
    (primary_le_initializedRadius LM L NB BC δ ξ),hcost,hrc⟩

end EulerPacketTerminalDatum
