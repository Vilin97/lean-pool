/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimary
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget

@[expose] public section

/-! The literal compact initial wave supplies the seven-field primary
budget for the direct-forward, zero-history packet construction. -/

noncomputable section

namespace EulerTransversePacketForward.Budget

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerPacketShiftArithmetic EulerContinuousTimeWeight
  EulerParameterWordGevrey EulerGevrey EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerPacketTimeProfile EulerCylinderSobolev

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (L : Budget D (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (C : ℝ) (W : GradeGuards (P := P) L N C) (Y : InitialData P D)
  (α : ℝ) (hα : 0 < α)
  (hYb : ∀ n, block standardDirection 6
    (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤ (α*C)*majorant L.R 0 n)

include W hα hYb

theorem primary_profile_budget (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector P)
    (S : Scales (Icc (0 : ℝ) D.T)) (hgrowth : S.growth = α • L.g) :
    ProfileBudget (EulerPacketForwardPrimary.regularity D Y O hcorrector) S L.R 1 := by
  let G := EulerPacketForwardPrimary.forcing (P := P) D
  have hf (n : ℕ) : block standardDirection 6 (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (α*C)*majorant L.R 0 n := by
    have hh : HistoryData.forcingPath G = 0 := by
      unfold HistoryData.forcingPath
      rw [EulerPacketForwardPrimary.forcing_path_zero,map_zero]
    simpa only [hh,map_zero,block_zero_function] using
      mul_nonneg (mul_nonneg hα.le W.data_nonneg)
        (majorant_nonneg L.R (zero_le_one.trans L.radius_one) 0 n)
  obtain ⟨hv,ht,hc,hct,hp⟩ := L.grade_fields N C W G Y α hα 0 (highShift 1)
    (by norm_num [highShift]) hf hYb
  have he : S.high 1 = α • L.g := by
    apply ContinuousMap.ext
    intro t
    rw [S.high_one,hgrowth]
  have hz := Field.wordBound_normalized_of_zero (Field.zero P D.T)
    (fun _ _ _ => rfl) D.T_pos.le (S.mean 1) (S.mean_pos 1) 6 L.R (meanShift 1)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact Field.normalized_wordBound_congr (G.vectorField Y) D.T_pos.le
      (S.high 1) (α • L.g) (S.high_pos 1)
      (smul_profile_pos L.g L.positive α hα) he 6 (highShift 1) L.R 1 hv
  · exact Field.normalized_wordBound_congr (G.vectorDerivativeField Y) D.T_pos.le
      (S.high 1) (α • L.g) (S.high_pos 1)
      (smul_profile_pos L.g L.positive α hα) he 6 (highShift 1) L.R 1 ht
  · exact hz.mono_amplitude (zero_le_one.trans L.radius_one) zero_le_one
  · exact hz.mono_amplitude (zero_le_one.trans L.radius_one) zero_le_one
  · exact Field.normalized_wordBound_congr (G.curlCorrectorField Y) D.T_pos.le
      (S.high 1) (α • L.g) (S.high_pos 1)
      (smul_profile_pos L.g L.positive α hα) he 6 (highShift 1) L.R 1 hc
  · exact Field.normalized_wordBound_congr (G.correctorDerivativeField Y) D.T_pos.le
      (S.high 1) (α • L.g) (S.high_pos 1)
      (smul_profile_pos L.g L.positive α hα) he 6 (highShift 1) L.R 1 hct
  · exact Field.normalized_wordBound_congr (G.scalarGradientField Y) D.T_pos.le
      (S.high 1) (α • L.g) (S.high_pos 1)
      (smul_profile_pos L.g L.positive α hα) he 6 (highShift 1) L.R 1 hp

end EulerTransversePacketForward.Budget

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerParameterWordGevrey EulerGevrey EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerCylinderSobolev

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (hR : wordRadius (Fin 4) δ ≤ L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := period) L N (wordCost (Fin 4) 6 δ*‖ξ‖))

include hδ1 hR hα W

theorem forwardPrimary_profile_budget (O : Operators) (hcorrector : O.curlCorrector =
  D.curlCorrector period)
    (S : Scales (Icc (0 : ℝ) D.T)) (hgrowth : S.growth = α • L.g) :
    ProfileBudget (forwardPrimaryRegularity D δ hδ (α • ξ) hs O hcorrector) S L.R 1 := by
  apply L.primary_profile_budget N _ W (initialData D δ hδ (α • ξ) hs) α hα _ O hcorrector S hgrowth
  intro n
  have hh := initialData_common_radius D δ hδ (α • ξ) hs standardDirection
    (fun i => by cases i using Fin.cases <;> simp [Prod.norm_def]) 6 hδ1 L.R hR n
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hα,mul_assoc,mul_left_comm,mul_comm] using hh

end EulerPacketTerminalDatum
