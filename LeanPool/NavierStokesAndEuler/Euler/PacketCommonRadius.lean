/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget

@[expose] public section

/-! Monotone enlargement of the actual source budgets and a common external
radius for the mean, forced transverse and nonlinear packet estimates. -/

noncomputable section

namespace EulerMeanPacketProvider.Budget

variable {D : Data} {q : ℕ} {R : ℝ} (M : Budget D q R)

/-- Only the three upper-radius guards change.  Every coefficient, inverse
constant, and actual source solver is preserved. -/
def enlargeRadius (R' : ℝ) (h : R ≤ R') : Budget D q R' where
  toSobolevData := { M.toSobolevData with
    radius_budget := M.radius_budget.trans h
    acceleration_budget := M.acceleration_budget.trans h
    continuous_acceleration_budget := M.continuous_acceleration_budget.trans h }
  forcing_one := M.forcing_one
  forcing_time := M.forcing_time

@[simp] theorem enlargeRadius_velocityCost (R' : ℝ) (h : R ≤ R') :
    (M.enlargeRadius R' h).velocityCost = M.velocityCost := rfl

@[simp] theorem enlargeRadius_derivativeCost (R' : ℝ) (h : R ≤ R') :
    (M.enlargeRadius R' h).derivativeCost = M.derivativeCost := rfl

@[simp] theorem enlargeRadius_pressureGradientCost (R' : ℝ) (h : R ≤ R') :
    (M.enlargeRadius R' h).pressureGradientCost = M.pressureGradientCost := rfl

end EulerMeanPacketProvider.Budget

namespace EulerTransversePacketJoin

open EulerTransversePacketProvider

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}

/-- The homogeneous propagator, time profile and all source constants are
unchanged.  The five external-radius inequalities are monotone. -/
def Budget.enlargeRadius (L : Budget D τ hτ hτT B ι q) (R' : ℝ) (h : L.R ≤ R') :
    Budget D τ hτ hτT B ι q :=
  { L with
    R := R'
    history_weak := L.history_weak.trans h
    history_strong := L.history_strong.trans h
    history_uniform := L.history_uniform.trans h
    forcing_radius := L.forcing_radius.trans h
    forward_radius := L.forward_radius.trans h }

@[simp] theorem Budget.enlargeRadius_R (L : Budget D τ hτ hτT B ι q)
    (R' : ℝ) (h : L.R ≤ R') : (L.enlargeRadius R' h).R = R' := rfl

@[simp] theorem Budget.enlargeRadius_fullProfile (L : Budget D τ hτ hτT B ι q)
    (R' : ℝ) (h : L.R ≤ R') : (L.enlargeRadius R' h).fullProfile = L.fullProfile := rfl

@[simp] theorem Budget.enlargeRadius_commonCost (L : Budget D τ hτ hτT B ι q)
    (R' : ℝ) (h : L.R ≤ R') : (L.enlargeRadius R' h).commonCost = L.commonCost := rfl

/-- The normal inverse radius and the actual inverse-frame/strain jets stay
fixed; only the target radius of their multiplier bound is enlarged. -/
def NormalBudget.enlargeRadius {R : ℝ} (N : NormalBudget D q R) (R' : ℝ) (h : R ≤ R') :
    NormalBudget D q R' := { N with radius := N.radius.trans h }

variable {P : ℝ}
  (L : Budget D τ hτ hτT B (Fin 4) q) (N : NormalBudget D q L.R)

@[simp] theorem Budget.enlargeRadius_pressureAmplitude (R' : ℝ) (h : L.R ≤ R') :
    (L.enlargeRadius R' h).pressureAmplitude (P := P) (N.enlargeRadius R' h) =
      L.pressureAmplitude (P := P) N := rfl

@[simp] theorem Budget.enlargeRadius_correctorAmplitude (R' : ℝ) (h : L.R ≤ R') :
    (L.enlargeRadius R' h).correctorAmplitude (P := P) (N.enlargeRadius R' h) =
      L.correctorAmplitude (P := P) N := rfl

@[simp] theorem Budget.enlargeRadius_correctorTimeAmplitude (R' : ℝ) (h : L.R ≤ R') :
    (L.enlargeRadius R' h).correctorTimeAmplitude (P := P) (N.enlargeRadius R' h) =
      L.correctorTimeAmplitude (P := P) N := rfl

end EulerTransversePacketJoin

namespace EulerMeanPacketProvider.Budget.GradeGuards

variable {D : Data} {R : ℝ} {M : Budget D 6 R}

theorem enlargeRadius (W : GradeGuards M) (R' : ℝ) (h : R ≤ R') :
    GradeGuards (M.enlargeRadius R' h) :=
  ⟨W.velocity.trans h,W.derivative.trans h,W.pressureGradient.trans h⟩

end EulerMeanPacketProvider.Budget.GradeGuards

namespace EulerTransversePacketJoin.Budget.GradeGuards

open EulerTransversePacketProvider

variable {P : ℝ}
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  {L : Budget D τ hτ hτT B (Fin 4) 6} {N : NormalBudget D 6 L.R}

theorem enlargeRadius (W : GradeGuards (P := P) L N) (R' : ℝ) (h : L.R ≤ R') :
    GradeGuards (P := P) (L.enlargeRadius R' h) (N.enlargeRadius R' h) :=
  ⟨W.common.trans h,W.corrector.trans h,W.correctorTime.trans h,W.pressureGradient.trans h⟩

end EulerTransversePacketJoin.Budget.GradeGuards

namespace EulerPacketCylinderField.Field

open EulerPacketProfileRecursion EulerGevrey EulerOperatorGevreyCalculus

theorem WordBound.mono_radius {P T : ℝ} [Fact (0 < P)]
    {raw : VectorField} {G : Field P T raw} {q d : ℕ} {R R' A : ℝ}
    (hG : G.WordBound q R A d) (hR : 0 ≤ R) (hA : 0 ≤ A) (h : R ≤ R') :
    G.WordBound q R' A d := fun n => (hG n).trans
      (mul_le_mul_of_nonneg_left (majorant_radius_mono R R' hR h d n) hA)

end EulerPacketCylinderField.Field

namespace EulerPacketCommonRadius

open EulerPacketCylinderField EulerPacketProfileRecursion EulerParameterWordGevrey

variable {P Tc : ℝ} [Fact (0 < P)] {O : Operators} {C : CoefficientData P Tc O}
  {DM : EulerMeanPacketProvider.Data} {Rm : ℝ} (M : EulerMeanPacketProvider.Budget DM 6 Rm)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le)}
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R) (CB : CoefficientBudget C)

/-- Every summand is a fixed source quantity.  There is no occurrence of the
new target radius, the forcing amplitude, or the recursive grade on the right. -/
def commonRadius : ℝ :=
  Rm + L.R + CB.termCost + sobolevCoefficientRadius (Fin 4) CB.Rc +
    M.velocityCost + M.derivativeCost + M.pressureGradientCost +
      L.commonCost + L.correctorAmplitude (P := P) N +
        L.correctorTimeAmplitude (P := P) N + 3*L.pressureAmplitude (P := P) N

theorem commonRadius_bounds :
    Rm ≤ commonRadius M L N CB ∧
    L.R ≤ commonRadius M L N CB ∧
    CB.termCost ≤ commonRadius M L N CB ∧
    sobolevCoefficientRadius (Fin 4) CB.Rc ≤ commonRadius M L N CB ∧
    M.velocityCost ≤ commonRadius M L N CB ∧
    M.derivativeCost ≤ commonRadius M L N CB ∧
    M.pressureGradientCost ≤ commonRadius M L N CB ∧
    L.commonCost ≤ commonRadius M L N CB ∧
    L.correctorAmplitude (P := P) N ≤ commonRadius M L N CB ∧
    L.correctorTimeAmplitude (P := P) N ≤ commonRadius M L N CB ∧
    3*L.pressureAmplitude (P := P) N ≤ commonRadius M L N CB := by
  have hm : 0 ≤ Rm := zero_le_one.trans M.radius_bounds.1
  have hl : 0 ≤ L.R := zero_le_one.trans L.radius_bounds.1
  have hc := CB.termCost_nonneg
  have hrc := sobolevCoefficientRadius_nonneg (ι := Fin 4) CB.Rc CB.Rc_nonneg
  have hmv := M.costs_nonneg.1
  have hmt := M.costs_nonneg.2.1
  have hmp := M.costs_nonneg.2.2.2
  have hlv := L.commonCost_nonneg
  have hlc := L.correctorAmplitude_nonneg (P := P) N
  have hlct := L.correctorTimeAmplitude_nonneg (P := P) N
  have hlp := L.pressureAmplitude_nonneg (P := P) N
  dsimp only [commonRadius]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

/-- Every target radius at least this fixed threshold allows the actual
enlarged budgets, with their original source constants and time profile. -/
theorem commonRadius_guards (R' : ℝ) (h : commonRadius M L N CB ≤ R') :
    ∃ (hM : Rm ≤ R') (hL : L.R ≤ R'),
      EulerMeanPacketProvider.Budget.GradeGuards (M.enlargeRadius R' hM) ∧
      EulerTransversePacketJoin.Budget.GradeGuards (P := P)
        (L.enlargeRadius R' hL) (N.enlargeRadius R' hL) ∧
      CB.termCost ≤ R' ∧ sobolevCoefficientRadius (Fin 4) CB.Rc ≤ R' := by
  obtain ⟨hm,hl,hc,hrc,hmv,hmt,hmp,hlv,hlc,hlct,hlp⟩ := commonRadius_bounds M L N CB
  refine ⟨hm.trans h,hl.trans h,?_,?_,hc.trans h,hrc.trans h⟩
  · exact ⟨hmv.trans h,hmt.trans h,hmp.trans h⟩
  · exact ⟨hlv.trans h,hlc.trans h,hlct.trans h,hlp.trans h⟩

/-- Concrete source-preserving rebudgeting at one common radius closes all
linear grade guards and the nonlinear coefficient/finite-sum guards. -/
theorem exists_common_radius :
    ∃ (R' : ℝ) (hM : Rm ≤ R') (hL : L.R ≤ R'),
      EulerMeanPacketProvider.Budget.GradeGuards (M.enlargeRadius R' hM) ∧
      EulerTransversePacketJoin.Budget.GradeGuards (P := P)
        (L.enlargeRadius R' hL) (N.enlargeRadius R' hL) ∧
      CB.termCost ≤ R' ∧ sobolevCoefficientRadius (Fin 4) CB.Rc ≤ R' :=
  ⟨commonRadius M L N CB,commonRadius_guards M L N CB _ le_rfl⟩

end EulerPacketCommonRadius
