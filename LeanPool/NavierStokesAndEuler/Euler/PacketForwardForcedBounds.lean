/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardGradeBounds
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity

/-! Every forced direct-forward grade starts from zero and obeys the genuine
five-field grade budget at the common radius. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketForward.Budget

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerContinuousTimeWeight EulerParameterWordGevrey
  EulerGevrey EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderSobolev
  EulerPacketShiftArithmetic

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (L : Budget D (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : GradeGuards (P := P) L N 1) {raw : VectorField}
  (G : Forcing P D raw) (F : Field P D.T raw) (c : ℝ) (hc : 0 < c)
  (p : ℕ) (hp : 2 ≤ p)
  (hforce : (F.normalized D.T_pos.le (c • L.g)
    (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highForceShift p))

include W hc hp hforce

theorem forced_grade_bounds :
    ((G.vectorField (InitialData.zero P D)).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((G.vectorDerivativeField (InitialData.zero P D)).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((G.curlCorrectorField (InitialData.zero P D)).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((G.correctorDerivativeField (InitialData.zero P D)).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((G.scalarGradientField (InitialData.zero P D)).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highShift p) := by
  have hf : (G.forcingField.normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R (c*1) (highForceShift p) :=
    (hforce.unscale_profile D.T_pos.le L.g L.positive c hc).transfer _
  have hi (n : ℕ) : block standardDirection 6
      (fun a => translate P a ((InitialData.zero P D).value : CylinderL2 P U)) n 0 ≤
        (c*1)*majorant L.R (highForceShift p) n := by
    simpa only [InitialData.zero,Submodule.coe_zero,map_zero,block_zero_function,mul_one] using
      mul_nonneg hc.le (majorant_nonneg L.R (zero_le_one.trans L.radius_one) (highForceShift p) n)
  exact L.grade_fields N 1 W G (InitialData.zero P D) c hc (highForceShift p) (highShift p)
    (by simp only [highForceShift,highShift]; omega) hf hi

end EulerTransversePacketForward.Budget
