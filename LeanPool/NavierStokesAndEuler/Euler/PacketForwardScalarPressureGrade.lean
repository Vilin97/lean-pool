/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScalarPressureGrade
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardForcedBounds

@[expose] public section

/-! Scalar pressure and angular pressure-gradient grade bounds for the actual
zero-history solve. Forced grades have zero initial data; the primary keeps
the literal compact initial-data amplitude. All bounds retain the same radius. -/

noncomputable section

namespace EulerTransversePacketForward

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerContinuousTimeWeight EulerParameterWordGevrey
  EulerGevrey EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderSobolev
  EulerPacketShiftArithmetic EulerCylinderScalarPrimitive
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField}

def scalarField (G : Forcing P D raw) (I : InitialData P D) :
    Field P D.T (fun z => scalarEmbed (G.scalar I z)) :=
  scalarEmbeddingField (G.scalar I) (G.pressurePath I)
    (G.pressurePath_orbit I) (G.scalar_eq_pointField I)

def angularField (G : Forcing P D raw) (I : InitialData P D) :
    Field P D.T (fun z => (EulerPacketPointJets.pressureJet (G.scalar I) z).2
      EulerPacketPointJets.angleDirection • D.m₀) :=
  EulerPacketPressure.angularGradientField P (G.scalar I) (G.pressurePath I)
    (G.pressurePath_orbit I) (G.scalar_eq_pointField I) D.m₀

namespace Budget

variable (L : Budget D (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)

theorem scalar_grade_bound_pred (C : ℝ) (W : GradeGuards (P := P) L N C)
    (G : Forcing P D raw) (I : InitialData P D)
    (c : ℝ) (hc : 0 < c) (d e : ℕ) (hroom : d+3 ≤ e)
    (hforce : ∀ n, block standardDirection 6 (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (c*C)*majorant L.R d n)
    (hinitial : ∀ n, block standardDirection 6
      (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ (c*C)*majorant L.R d n) :
    ((scalarField G I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (e-1) := by
  have hb : ((scalarField G I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((L.pressureAmplitude (P := P) N*C)*c) (d+1) := by
    apply scalarEmbeddingField_normalized_bound _ _ _ _ D.T_pos.le L.g L.positive
    intro n
    simpa only [mul_assoc,mul_left_comm,mul_comm] using
      L.pressure_bound N G I (c*C) (mul_nonneg hc.le W.data_nonneg) d hforce hinitial n
  have hnonneg := mul_nonneg (L.pressureAmplitude_nonneg (P := P) N) W.data_nonneg
  have hcost : L.pressureAmplitude (P := P) N*C ≤ L.R := by
    linarith [W.pressureGradient]
  exact (hb.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
    L.radius_one hnonneg hcost (by omega)

theorem angular_grade_bound (C : ℝ) (W : GradeGuards (P := P) L N C)
    (G : Forcing P D raw) (I : InitialData P D)
    (c : ℝ) (hc : 0 < c) (d e : ℕ) (hroom : d+3 ≤ e)
    (hforce : ∀ n, block standardDirection 6 (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (c*C)*majorant L.R d n)
    (hinitial : ∀ n, block standardDirection 6
      (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ (c*C)*majorant L.R d n) :
    ((angularField G I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e := by
  have hh := angularGradientField_normalized_bound _ _ _ _ D.T_pos.le
    (c • L.g) (smul_profile_pos L.g L.positive c hc)
    D.m₀ D.m₀_unit.le (zero_le_one.trans L.radius_one) zero_le_one
    (L.scalar_grade_bound_pred N C W G I c hc d e hroom hforce hinitial)
  simpa only [angularField,Field.WordBound,Field.normalized_path,
    show e-1+1=e by omega] using hh

theorem scalar_grade_bound (C : ℝ) (W : GradeGuards (P := P) L N C)
    (G : Forcing P D raw) (I : InitialData P D)
    (c : ℝ) (hc : 0 < c) (d e : ℕ) (hroom : d+3 ≤ e)
    (hforce : ∀ n, block standardDirection 6 (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (c*C)*majorant L.R d n)
    (hinitial : ∀ n, block standardDirection 6
      (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ (c*C)*majorant L.R d n) :
    ((scalarField G I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e :=
  (L.scalar_grade_bound_pred N C W G I c hc d e hroom hforce hinitial).mono_shift
    L.radius_one zero_le_one (Nat.sub_le _ _)

theorem forced_scalar_and_angular_grade_bound
    (W : GradeGuards (P := P) L N 1)
    (G : Forcing P D raw) (F : Field P D.T raw) (c : ℝ) (hc : 0 < c)
    (p : ℕ) (hp : 2 ≤ p)
    (hforce : (F.normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highForceShift p)) :
    ((scalarField G (InitialData.zero P D)).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highShift p) ∧
    ((angularField G (InitialData.zero P D)).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 (highShift p) := by
  have hf : (G.forcingField.normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R (c*1) (highForceShift p) :=
    (hforce.unscale_profile D.T_pos.le L.g L.positive c hc).transfer _
  have hi (n : ℕ) : block standardDirection 6
      (fun a => translate P a ((InitialData.zero P D).value : CylinderL2 P U)) n 0 ≤
        (c*1)*majorant L.R (highForceShift p) n := by
    simpa only [InitialData.zero,Submodule.coe_zero,map_zero,block_zero_function,mul_one] using
      mul_nonneg hc.le (majorant_nonneg L.R (zero_le_one.trans L.radius_one) (highForceShift p) n)
  have hroom : highForceShift p+3 ≤ highShift p := by
    simp only [highForceShift,highShift]
    omega
  exact ⟨L.scalar_grade_bound N 1 W G (InitialData.zero P D) c hc _ _ hroom hf hi,
    L.angular_grade_bound N 1 W G (InitialData.zero P D) c hc _ _ hroom hf hi⟩

theorem primary_scalar_and_angular_grade_bound
    (C : ℝ) (W : GradeGuards (P := P) L N C) (Y : InitialData P D)
    (α : ℝ) (hα : 0 < α)
    (hYb : ∀ n, block standardDirection 6
      (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤ (α*C)*majorant L.R 0 n) :
    ((scalarField (EulerPacketForwardPrimary.forcing D) Y).normalized D.T_pos.le (α • L.g)
      (smul_profile_pos L.g L.positive α hα)).WordBound 6 L.R 1 (highShift 1) ∧
    ((angularField (EulerPacketForwardPrimary.forcing D) Y).normalized D.T_pos.le (α • L.g)
      (smul_profile_pos L.g L.positive α hα)).WordBound 6 L.R 1 (highShift 1) := by
  let G := EulerPacketForwardPrimary.forcing (P := P) D
  have hf (n : ℕ) : block standardDirection 6 (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (α*C)*majorant L.R 0 n := by
    have hh : HistoryData.forcingPath G = 0 := by
      unfold HistoryData.forcingPath
      rw [EulerPacketForwardPrimary.forcing_path_zero,map_zero]
    simpa only [hh,map_zero,block_zero_function] using
      mul_nonneg (mul_nonneg hα.le W.data_nonneg)
        (majorant_nonneg L.R (zero_le_one.trans L.radius_one) 0 n)
  have hroom : 0+3 ≤ highShift 1 := by norm_num [highShift]
  exact ⟨L.scalar_grade_bound N C W G Y α hα 0 _ hroom hf hYb,
    L.angular_grade_bound N C W G Y α hα 0 _ hroom hf hYb⟩

end Budget

end EulerTransversePacketForward
