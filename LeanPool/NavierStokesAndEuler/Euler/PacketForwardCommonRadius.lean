/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCommonRadius

@[expose] public section

/-! One finite source radius accommodates the zero-history primary, every
forced direct-forward grade, the mean solve and the nonlinear coefficients.
Neither the positive packet amplitude nor the recursive grade enters it. -/

noncomputable section

namespace EulerTransversePacketForward.Budget

open EulerTransversePacketProvider

variable {P : ℝ}
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (L : Budget D (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R) (C : ℝ)

def gradeRadius : ℝ :=
  max L.R (max (L.commonCost*C) (max (L.correctorAmplitude (P := P) N*C)
    (max (L.correctorTimeAmplitude (P := P) N*C) (3*L.pressureAmplitude (P := P) N*C))))

theorem gradeRadius_bounds :
    L.R ≤ L.gradeRadius (P := P) N C ∧
    L.commonCost*C ≤ L.gradeRadius (P := P) N C ∧
    L.correctorAmplitude (P := P) N*C ≤ L.gradeRadius (P := P) N C ∧
    L.correctorTimeAmplitude (P := P) N*C ≤ L.gradeRadius (P := P) N C ∧
    3*L.pressureAmplitude (P := P) N*C ≤ L.gradeRadius (P := P) N C := by
  unfold gradeRadius
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))),
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))⟩

theorem gradeRadius_guards (hC : 0 ≤ C) (R' : ℝ)
    (hR : L.gradeRadius (P := P) N C ≤ R') :
    ∃ h : L.R ≤ R', GradeGuards (P := P) (L.enlargeRadius R' h)
      (N.enlargeRadius R' h) C := by
  have hb := L.gradeRadius_bounds (P := P) N C
  refine ⟨hb.1.trans hR, ?_⟩
  exact ⟨hC,hb.2.1.trans hR,hb.2.2.1.trans hR,hb.2.2.2.1.trans hR,hb.2.2.2.2.trans hR⟩

theorem exists_grade_radius (hC : 0 ≤ C) (extra : ℝ) :
    ∃ R' : ℝ, extra ≤ R' ∧ ∃ h : L.R ≤ R',
      GradeGuards (P := P) (L.enlargeRadius R' h) (N.enlargeRadius R' h) C :=
  ⟨max extra (L.gradeRadius (P := P) N C),le_max_left _ _,
    L.gradeRadius_guards N C hC _ (le_max_right _ _)⟩

end EulerTransversePacketForward.Budget

namespace EulerPacketForwardCommonRadius

open EulerPacketCylinderField EulerPacketProfileRecursion EulerParameterWordGevrey

variable {P Tc : ℝ} [Fact (0 < P)] {O : Operators} {C : CoefficientData P Tc O}
  {DM : EulerMeanPacketProvider.Data} {Rm : ℝ} (M : EulerMeanPacketProvider.Budget DM 6 Rm)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R) (CB : CoefficientBudget C)
  (terminalCost extra : ℝ)

def commonRadius : ℝ :=
  Rm+L.R+CB.termCost+sobolevCoefficientRadius (Fin 4) CB.Rc+
    M.velocityCost+M.derivativeCost+M.pressureGradientCost+
      L.gradeRadius (P := P) N 1+L.gradeRadius (P := P) N terminalCost+max 0 extra

theorem commonRadius_bounds :
    Rm ≤ commonRadius M L N CB terminalCost extra ∧
    L.R ≤ commonRadius M L N CB terminalCost extra ∧
    CB.termCost ≤ commonRadius M L N CB terminalCost extra ∧
    sobolevCoefficientRadius (Fin 4) CB.Rc ≤ commonRadius M L N CB terminalCost extra ∧
    M.velocityCost ≤ commonRadius M L N CB terminalCost extra ∧
    M.derivativeCost ≤ commonRadius M L N CB terminalCost extra ∧
    M.pressureGradientCost ≤ commonRadius M L N CB terminalCost extra ∧
    L.gradeRadius (P := P) N 1 ≤ commonRadius M L N CB terminalCost extra ∧
    L.gradeRadius (P := P) N terminalCost ≤ commonRadius M L N CB terminalCost extra ∧
    extra ≤ commonRadius M L N CB terminalCost extra := by
  have hm : 0 ≤ Rm := zero_le_one.trans M.radius_bounds.1
  have hl : 0 ≤ L.R := zero_le_one.trans L.radius_one
  have hc := CB.termCost_nonneg
  have hrc := sobolevCoefficientRadius_nonneg (ι := Fin 4) CB.Rc CB.Rc_nonneg
  have hmv := M.costs_nonneg.1
  have hmt := M.costs_nonneg.2.1
  have hmp := M.costs_nonneg.2.2.2
  have hlf := hl.trans (L.gradeRadius_bounds (P := P) N 1).1
  have hlp := hl.trans (L.gradeRadius_bounds (P := P) N terminalCost).1
  have he := le_max_left (0 : ℝ) extra
  have he' := le_max_right (0 : ℝ) extra
  dsimp only [commonRadius]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem commonRadius_guards (hC : 0 ≤ terminalCost) (R' : ℝ)
    (hR : commonRadius M L N CB terminalCost extra ≤ R') :
    ∃ (hM : Rm ≤ R') (hL : L.R ≤ R'),
      EulerMeanPacketProvider.Budget.GradeGuards (M.enlargeRadius R' hM) ∧
      EulerTransversePacketForward.Budget.GradeGuards (P := P)
        (L.enlargeRadius R' hL) (N.enlargeRadius R' hL) 1 ∧
      EulerTransversePacketForward.Budget.GradeGuards (P := P)
        (L.enlargeRadius R' hL) (N.enlargeRadius R' hL) terminalCost ∧
      CB.termCost ≤ R' ∧ sobolevCoefficientRadius (Fin 4) CB.Rc ≤ R' ∧ extra ≤ R' := by
  obtain ⟨hm,hl,hc,hrc,hmv,hmt,hmp,hlf,hlp,he⟩ := commonRadius_bounds M L N CB terminalCost extra
  obtain ⟨_,wf⟩ := L.gradeRadius_guards (P := P) N 1 zero_le_one R' (hlf.trans hR)
  obtain ⟨_,wp⟩ := L.gradeRadius_guards (P := P) N terminalCost hC R' (hlp.trans hR)
  exact ⟨hm.trans hR,hl.trans hR,⟨hmv.trans hR,hmt.trans hR,hmp.trans hR⟩,
    wf,wp,hc.trans hR,hrc.trans hR,he.trans hR⟩

theorem exists_common_radius (hC : 0 ≤ terminalCost) :
    ∃ (R' : ℝ) (hM : Rm ≤ R') (hL : L.R ≤ R'),
      EulerMeanPacketProvider.Budget.GradeGuards (M.enlargeRadius R' hM) ∧
      EulerTransversePacketForward.Budget.GradeGuards (P := P)
        (L.enlargeRadius R' hL) (N.enlargeRadius R' hL) 1 ∧
      EulerTransversePacketForward.Budget.GradeGuards (P := P)
        (L.enlargeRadius R' hL) (N.enlargeRadius R' hL) terminalCost ∧
      CB.termCost ≤ R' ∧ sobolevCoefficientRadius (Fin 4) CB.Rc ≤ R' ∧ extra ≤ R' :=
  ⟨commonRadius M L N CB terminalCost extra,
    commonRadius_guards M L N CB terminalCost extra hC _ le_rfl⟩

end EulerPacketForwardCommonRadius
