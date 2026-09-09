/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardFullBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedGradeBounds

@[expose] public section

/-! Fixed source costs close the direct-forward packet grade bounds.  The
profile's positive scalar factor cancels exactly; one spare shift pays the
fixed operator costs, with no change of external radius. -/

noncomputable section

namespace EulerTransversePacketForward.Budget

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerContinuousTimeWeight EulerParameterWordGevrey
  EulerGevrey EulerSourceNormalResidualBounds EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSobolev

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (L : Budget D (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)

theorem pressureAmplitude_nonneg : 0 ≤ L.pressureAmplitude (P := P) N := by
  have hi := N.Ri_nonneg
  have hc := N.C_nonneg
  have hl := L.commonCost_nonneg
  have hp := (Fact.out : 0 < P).le
  have hm := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 (4*N.Ri) (3*N.Ri*N.C)
    (by positivity) (by positivity)
  have hM := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 (4*N.Ri) N.C
    (by positivity) hc
  unfold pressureAmplitude pressureCost
  positivity

theorem correctorAmplitude_nonneg : 0 ≤ L.correctorAmplitude (P := P) N := by
  have hl := L.commonCost_nonneg
  have hp := (Fact.out : 0 < P).le
  unfold correctorAmplitude
  positivity

theorem correctorTimeAmplitude_nonneg : 0 ≤ L.correctorTimeAmplitude (P := P) N := by
  have hl := L.commonCost_nonneg
  have hp := (Fact.out : 0 < P).le
  unfold correctorTimeAmplitude
  positivity

/-- The unscaled data cost is fixed before the positive amplitude and grade.
It is one for forced profiles and the literal compact-wave cost for the primary. -/
structure GradeGuards (C : ℝ) : Prop where
  data_nonneg : 0 ≤ C
  common : L.commonCost*C ≤ L.R
  corrector : L.correctorAmplitude (P := P) N*C ≤ L.R
  correctorTime : L.correctorTimeAmplitude (P := P) N*C ≤ L.R
  pressureGradient : 3*L.pressureAmplitude (P := P) N*C ≤ L.R

variable (C : ℝ) (W : GradeGuards (P := P) L N C)
  {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)
  (c : ℝ) (hc : 0 < c) (d e : ℕ) (hroom : d+3 ≤ e)
  (hforce : ∀ n, block standardDirection 6 (fun a => pathTranslate P a
    (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (c*C)*majorant L.R d n)
  (hinitial : ∀ n, block standardDirection 6
    (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ (c*C)*majorant L.R d n)

include W hc hroom hforce hinitial

theorem grade_fields :
    ((G.vectorField I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e ∧
    ((G.vectorDerivativeField I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e ∧
    ((G.curlCorrectorField I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e ∧
    ((G.correctorDerivativeField I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e ∧
    ((G.scalarGradientField I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e := by
  have ha := mul_nonneg hc.le W.data_nonneg
  have hd : ∀ i : Fin 4, ‖standardDirection i‖ ≤ 1 := by
    intro i
    cases i using Fin.cases <;> simp [Prod.norm_def]
  have hv : ((G.vectorField I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((L.commonCost*C)*c) (d+1) := by
    intro n
    simpa only [Field.normalized_path,Forcing.vectorField,mul_assoc,mul_left_comm,mul_comm] using
      L.velocity_common_bound G I standardDirection hd (c*C) ha d hforce hinitial n
  have ht : ((G.vectorDerivativeField I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((L.commonCost*C)*c) (d+1) := by
    intro n
    simpa only [Field.normalized_path,Forcing.vectorDerivativeField,mul_assoc,mul_left_comm,mul_comm] using
      L.derivative_common_bound G I standardDirection hd (c*C) ha d hforce hinitial n
  have hC : ((G.curlCorrectorField I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((L.correctorAmplitude (P := P) N*C)*c) (d+2) := by
    intro n
    simpa only [Field.normalized_path,Forcing.curlCorrectorField,mul_assoc,mul_left_comm,mul_comm]
      using
      L.corrector_bound N G I (c*C) ha d hforce hinitial n
  have hCt : ((G.correctorDerivativeField I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((L.correctorTimeAmplitude (P := P) N*C)*c) (d+2) := by
    intro n
    simpa only [Field.normalized_path,Forcing.correctorDerivativeField,mul_assoc,mul_left_comm,mul_comm] using
      L.corrector_time_bound N G I (c*C) ha d hforce hinitial n
  have hπ : ((G.scalarGradientField I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((3*L.pressureAmplitude (P := P) N*C)*c) (d+2) := by
    intro n
    simpa only [Field.normalized_path,mul_assoc,mul_left_comm,mul_comm] using
      L.pressure_gradient_bound N G I (c*C) ha d hforce hinitial n
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (hv.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
      L.radius_one (mul_nonneg L.commonCost_nonneg W.data_nonneg) W.common (by omega)
  · exact (ht.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
      L.radius_one (mul_nonneg L.commonCost_nonneg W.data_nonneg) W.common (by omega)
  · exact (hC.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
      L.radius_one (mul_nonneg (L.correctorAmplitude_nonneg N) W.data_nonneg) W.corrector (by omega)
  · exact (hCt.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
      L.radius_one (mul_nonneg (L.correctorTimeAmplitude_nonneg N) W.data_nonneg) W.correctorTime
        (by omega)
  · exact (hπ.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
      L.radius_one (mul_nonneg (mul_nonneg (by norm_num) (L.pressureAmplitude_nonneg N))
        W.data_nonneg)
      W.pressureGradient (by omega)

end EulerTransversePacketForward.Budget
