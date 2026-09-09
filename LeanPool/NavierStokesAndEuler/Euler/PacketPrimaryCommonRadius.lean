/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryRadius

/-! The primary grade imposes only finitely many fixed lower bounds on the
external radius.  Enlarging it leaves the time profile and every source cost
unchanged, including the terminal amplitude before its scalar multiplier. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketPrimary.Budget

open EulerTransversePacketProvider

variable {P : ℝ}
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6}
  (H : Budget L) (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (C : ℝ)

/-- Grade radius, constructed using `max`. -/
def gradeRadius : ℝ :=
  max L.R (max (H.commonCost*C) (max (H.correctorAmplitude (P := P) N*C)
    (max (H.correctorTimeAmplitude (P := P) N*C) (3*H.pressureAmplitude (P := P) N*C))))

theorem gradeRadius_bounds :
    L.R ≤ H.gradeRadius (P := P) N C ∧
    H.commonCost*C ≤ H.gradeRadius (P := P) N C ∧
    H.correctorAmplitude (P := P) N*C ≤ H.gradeRadius (P := P) N C ∧
    H.correctorTimeAmplitude (P := P) N*C ≤ H.gradeRadius (P := P) N C ∧
    3*H.pressureAmplitude (P := P) N*C ≤ H.gradeRadius (P := P) N C := by
  unfold gradeRadius
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))),
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))⟩

theorem gradeRadius_guards (hC : 0 ≤ C) (R' : ℝ)
    (hR : H.gradeRadius (P := P) N C ≤ R') :
    ∃ h : L.R ≤ R', GradeGuards (P := P) (H.enlargeRadius R' h)
      (N.enlargeRadius R' h) C := by
  have hb := H.gradeRadius_bounds (P := P) N C
  refine ⟨hb.1.trans hR, ?_⟩
  exact ⟨hC, hb.2.1.trans hR, hb.2.2.1.trans hR,
    hb.2.2.2.1.trans hR, hb.2.2.2.2.trans hR⟩

/-- An arbitrary extra requirement can be included without changing any
source cost or the primary time profile. -/
theorem exists_grade_radius (hC : 0 ≤ C) (extra : ℝ) :
    ∃ R' : ℝ, extra ≤ R' ∧ ∃ h : L.R ≤ R',
      GradeGuards (P := P) (H.enlargeRadius R' h) (N.enlargeRadius R' h) C :=
  ⟨max extra (H.gradeRadius (P := P) N C), le_max_left _ _,
    H.gradeRadius_guards N C hC _ (le_max_right _ _)⟩

namespace GradeGuards

variable {H N C}

theorem enlargeRadius (W : GradeGuards (P := P) H N C) (R' : ℝ) (h : L.R ≤ R') :
    GradeGuards (P := P) (H.enlargeRadius R' h) (N.enlargeRadius R' h) C :=
  ⟨W.terminal_nonneg, W.common.trans h, W.corrector.trans h,
    W.correctorTime.trans h, W.pressureGradient.trans h⟩

end GradeGuards
end EulerTransversePacketPrimary.Budget
