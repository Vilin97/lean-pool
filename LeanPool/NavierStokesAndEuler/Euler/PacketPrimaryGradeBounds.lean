/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryFullBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimarySourceRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalInitialData
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketLinearCostAbsorption
import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalEnvelope

/-! The actual primary closes the first packet grade.  Its terminal scalar
amplitude is canceled against the actual time profile, and only fixed source
costs are absorbed into the radius. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketPrimary.Budget

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerPacketShiftArithmetic EulerContinuousTimeWeight
  EulerParameterWordGevrey EulerGevrey EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerPacketTimeProfile EulerCylinderSobolev

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6}
  (H : Budget L) (N : EulerTransversePacketJoin.NormalBudget D 6 L.R) (C : ℝ)

/-- C bounds the unmultiplied terminal datum.  No guard involves the scalar
amplitude α, and the original radius is retained. -/
structure GradeGuards : Prop where
  terminal_nonneg : 0 ≤ C
  common : H.commonCost*C ≤ L.R
  corrector : H.correctorAmplitude (P := P) N*C ≤ L.R
  correctorTime : H.correctorTimeAmplitude (P := P) N*C ≤ L.R
  pressureGradient : 3*H.pressureAmplitude (P := P) N*C ≤ L.R

variable (W : GradeGuards (P := P) H N C) (Y : InitialData P D) (α : ℝ) (hα : 0 < α)
  (hYb : ∀ n, block standardDirection 6 (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤
    (α * C) * majorant L.R 0 n)

include W hYb hα

theorem grade_fields :
    ((vectorField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) ∧
    ((vectorDerivativeField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) ∧
    ((correctorField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) ∧
    ((correctorDerivativeField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) ∧
    ((scalarGradientField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) := by
  have ha := mul_nonneg hα.le W.terminal_nonneg
  have hv : ((vectorField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((H.commonCost*C)*α) 3 := by
    intro n
    simpa only [Field.normalized_path,vectorField,Nat.zero_add,mul_assoc,mul_left_comm,mul_comm]
        using H.velocity_common_bound Y _ ha 0 hYb n
  have ht : ((vectorDerivativeField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((H.commonCost*C)*α) 3 := by
    intro n
    simpa only [Field.normalized_path, vectorDerivativeField, Nat.zero_add, mul_assoc,
        mul_left_comm, mul_comm] using H.derivative_common_bound Y _ ha 0 hYb n
  have hc : ((correctorField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((H.correctorAmplitude (P := P) N*C)*α) 4 := by
    intro n
    simpa only [Field.normalized_path,correctorField,Nat.zero_add,mul_assoc,mul_left_comm,mul_comm]
        using H.corrector_bound N Y _ ha 0 hYb n
  have hct : ((correctorDerivativeField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((H.correctorTimeAmplitude (P := P) N*C)*α) 4 := by
    intro n
    simpa only [Field.normalized_path, correctorDerivativeField, Nat.zero_add, mul_assoc,
        mul_left_comm, mul_comm] using H.corrector_time_bound N Y _ ha 0 hYb n
  have hp : ((scalarGradientField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((3*H.pressureAmplitude (P := P) N*C)*α) 4 := by
    intro n
    simpa only [Field.normalized_path,Nat.zero_add,mul_assoc,mul_left_comm,mul_comm] using
        H.pressure_gradient_bound N Y _ ha 0 hYb n
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (hv.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg H.commonCost_nonneg W.terminal_nonneg) W.common (by
          norm_num [highShift])
  · exact (ht.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg H.commonCost_nonneg W.terminal_nonneg) W.common (by
          norm_num [highShift])
  · exact (hc.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg (H.correctorAmplitude_nonneg N) W.terminal_nonneg)
      W.corrector (by norm_num [highShift])
  · exact (hct.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg (H.correctorTimeAmplitude_nonneg N) W.terminal_nonneg)
      W.correctorTime (by norm_num [highShift])
  · exact (hp.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg (mul_nonneg (by
          norm_num) (H.pressureAmplitude_nonneg N)) W.terminal_nonneg)
      W.pressureGradient (by norm_num [highShift])

theorem profile_budget (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector P)
    (S : Scales (Icc (0 : ℝ) D.T)) (hgrowth : S.growth = α • L.fullProfile) :
    ProfileBudget (profileRegularity τ hτ hτT B Y O hcorrector) S L.R 1 := by
  obtain ⟨hv,ht,hc,hct,hp⟩ := H.grade_fields N C W Y α hα hYb
  have he : S.high 1 = α • L.fullProfile := by
    apply ContinuousMap.ext
    intro t
    rw [S.high_one,hgrowth]
  have hz := Field.wordBound_normalized_of_zero (Field.zero P D.T)
    (fun _ _ _ => rfl) D.T_pos.le (S.mean 1) (S.mean_pos 1) 6 L.R (meanShift 1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Field.normalized_wordBound_congr (vectorField τ hτ hτT B Y) D.T_pos.le
      (S.high 1) (α • L.fullProfile) (S.high_pos 1)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) he 6 (highShift 1) L.R 1 hv
  · exact Field.normalized_wordBound_congr (vectorDerivativeField τ hτ hτT B Y) D.T_pos.le
      (S.high 1) (α • L.fullProfile) (S.high_pos 1)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) he 6 (highShift 1) L.R 1 ht
  · exact hz.mono_amplitude (zero_le_one.trans L.radius_bounds.1) zero_le_one
  · exact hz.mono_amplitude (zero_le_one.trans L.radius_bounds.1) zero_le_one
  · exact Field.normalized_wordBound_congr (correctorField τ hτ hτT B Y) D.T_pos.le
      (S.high 1) (α • L.fullProfile) (S.high_pos 1)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) he 6 (highShift 1) L.R 1 hc
  · exact Field.normalized_wordBound_congr (correctorDerivativeField τ hτ hτT B Y) D.T_pos.le
      (S.high 1) (α • L.fullProfile) (S.high_pos 1)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) he 6 (highShift 1) L.R 1 hct
  · exact Field.normalized_wordBound_congr (scalarGradientField τ hτ hτT B Y) D.T_pos.le
      (S.high 1) (α • L.fullProfile) (S.high_pos 1)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) he 6 (highShift 1) L.R 1 hp

end EulerTransversePacketPrimary.Budget

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerParameterWordGevrey EulerGevrey EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerCylinderSobolev

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6}
  (H : EulerTransversePacketPrimary.Budget L)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (hR : wordRadius (Fin 4) δ ≤ L.R)
  (W : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H N (wordCost (Fin 4) 6 δ *
      ‖ξ‖))

include hδ1 hR hα

theorem scaled_initialData_bound (n : ℕ) :
    block standardDirection 6 (fun a => translate period a
      ((initialData D δ hδ (α • ξ) hs).value : CylinderL2 period U)) n 0 ≤
      (α*(wordCost (Fin 4) 6 δ*‖ξ‖))*majorant L.R 0 n := by
  have hh := initialData_common_radius D δ hδ (α • ξ) hs standardDirection
    (fun i => by cases i using Fin.cases <;> simp [Prod.norm_def]) 6 hδ1 L.R hR n
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hα,mul_assoc,mul_left_comm,mul_comm] using hh

include W in
/-- The literal α χ₁ fδ ξT terminal datum supplies the required primary
profile budget, with every terminal jet estimate discharged. -/
theorem primary_profile_budget (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector
    period)
    (S : Scales (Icc (0 : ℝ) D.T)) (hgrowth : S.growth = α • L.fullProfile) :
    ProfileBudget (EulerTransversePacketPrimary.profileRegularity τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs) O hcorrector) S L.R 1 :=
  H.profile_budget N _ W (initialData D δ hδ (α • ξ) hs) α hα
    (scaled_initialData_bound (L := L) δ hδ hδ1 ξ hs α hα hR) O hcorrector S hgrowth

end EulerPacketTerminalDatum
