/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ExtendedHeatedOutgoing
public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalCone

@[expose] public section

/-!
# A common scheduled profile below caller-supplied parameter bounds

The reset coefficient bound is selected before lambda. The caller's lambda
cap is intersected with the existing reset and energy thresholds before any
profile is constructed. The actual core is then fixed before choosing h.
-/

noncomputable section

namespace NavierStokes.ScheduledProfileChoice

open OutgoingProfile (Profile)
open ExtendedHeatedOutgoing (ScheduleBounds)

/-- The actual core and reset bound precede every subsequent height choice. -/
theorem exists_scheduled_core_below (P m : ℝ) (hP : 0 < P) (hm : 0 < m)
    (cap : ℝ → ℝ) (hcap : ∀ K : ℝ, 0 < K → 0 < cap K) :
    ∃ (K B : ℝ) (core : OutgoingSchedule.Parameters),
      0 < K ∧ 0 < B ∧ core.P = P ∧ core.m = m ∧
      core.wait = 60 * Real.log (1 / core.lam) ∧
      core.lam < cap K ∧ core.lam < 1 / 120 ∧
      ∀ h : ℝ, 0 < h → 2 * h < core.lam →
        ∃ F : Profile, F.data.core = core ∧ F.data.h = h ∧ F.coefficientBound = K ∧
          ScheduleBounds F ∧ OutgoingProfile.Specification F B := by
  obtain ⟨resetLam, K, hresetLam, hK, hreset⟩ := UniformAngularReset.exists_scheduled_reset
  obtain ⟨delta, hdelta, hrate⟩ := PulseAmplitude.exists_rate_threshold
    (CorrectedPulseAmplitude.combinedConstant P m K)
  let lam₀ := min (cap K) (min resetLam (min delta (1 / 120 : ℝ)))
  have hlam₀ : 0 < lam₀ := lt_min (hcap K hK) (lt_min hresetLam (lt_min hdelta (by norm_num)))
  let lam := lam₀ / 2
  have hlam : 0 < lam := half_pos hlam₀
  have hlam₀' : lam < lam₀ := half_lt_self hlam₀
  have hcaller : lam < cap K := hlam₀'.trans_le (min_le_left _ _)
  have hrest : lam < min resetLam (min delta (1 / 120 : ℝ)) :=
    hlam₀'.trans_le (min_le_right _ _)
  have hreset' : lam < resetLam := hrest.trans_le (min_le_left _ _)
  have hdelta' : lam < delta := hrest.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : lam < 1 / 120 := hrest.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let core := OutgoingSchedule.paperParameters P m lam hP hm hlam (by linarith)
  refine ⟨K, 128 * CorrectedPulseAmplitude.combinedConstant P m K, core, hK,
    mul_pos (by norm_num) (CorrectedPulseAmplitude.combinedConstant_pos hP m K hK),
    rfl, rfl, rfl, hcaller, hsmall, ?_⟩
  intro h hh htail
  let d : OutgoingTail.TailData := ⟨core, h, hh, htail⟩
  obtain ⟨r⟩ := hreset d hreset'
  let F : Profile := ⟨d, K, r⟩
  have b : ScheduleBounds F := {
    coefficient_pos := hK
    lambda_small := hsmall.le
    wait_eq := rfl
    scale_small := hrate lam hlam hdelta' }
  exact ⟨F, rfl, rfl, rfl, b, b.specification⟩

/-- A scalar-parameter form of the same construction, with the reset bound
retained as an explicit preceding existential. -/
theorem exists_scheduled_profile_below (P m : ℝ) (hP : 0 < P) (hm : 0 < m)
    (cap : ℝ → ℝ) (hcap : ∀ K : ℝ, 0 < K → 0 < cap K) :
    ∃ K lam B : ℝ,
      0 < K ∧ 0 < lam ∧ lam < cap K ∧ lam < 1 / 120 ∧ 0 < B ∧
      ∀ h : ℝ, 0 < h → 2 * h < lam →
        ∃ F : Profile, F.data.core.P = P ∧ F.data.core.m = m ∧
          F.data.core.lam = lam ∧ F.data.h = h ∧ F.coefficientBound = K ∧
          ScheduleBounds F ∧ OutgoingProfile.Specification F B := by
  obtain ⟨K, B, core, hK, hB, hcP, hcm, _hwait, hcaller, hsmall, hf⟩ :=
    exists_scheduled_core_below P m hP hm cap hcap
  refine ⟨K, core.lam, B, hK, core.lam_pos, hcaller, hsmall, hB, ?_⟩
  intro h hh ht
  obtain ⟨F, hcore, hh', hK', hb, hF⟩ := hf h hh ht
  refine ⟨F, ?_, ?_, ?_, hh', hK', hb, hF⟩
  · rw [hcore, hcP]
  · rw [hcore, hcm]
  · rw [hcore]

/-- This number depends on the already fixed core and an additional caller
height bound. It is chosen before the terminal exponent h. -/
noncomputable def heightCap (core : OutgoingSchedule.Parameters) (extra : ℝ) : ℝ :=
  min (core.lam / 4)
    (min extra (min (1 / 1000) (min (1 / 4) (1 / (1 + TerminalCone.releaseBudget core)))))

theorem heightCap_pos (core : OutgoingSchedule.Parameters) {extra : ℝ} (he : 0 < extra) :
    0 < heightCap core extra := by
  have hb := TerminalCone.releaseBudget_nonneg core
  exact lt_min (div_pos core.lam_pos (by norm_num))
    (lt_min he (lt_min (by norm_num) (lt_min (by norm_num) (by positivity))))

theorem heightCap_bounds (core : OutgoingSchedule.Parameters) (extra : ℝ) :
    2 * heightCap core extra < core.lam ∧ heightCap core extra ≤ extra ∧
      heightCap core extra ≤ 1 / 1000 ∧ heightCap core extra ≤ 1 / 4 ∧
      heightCap core extra ≤ 1 / (1 + TerminalCone.releaseBudget core) := by
  have hl : heightCap core extra ≤ core.lam / 4 := min_le_left _ _
  have hr : heightCap core extra ≤
      min extra (min (1 / 1000) (min (1 / 4) (1 / (1 + TerminalCone.releaseBudget core)))) :=
        min_le_right _ _
  have hrest := hr.trans (min_le_right _ _)
  have hlast := hrest.trans (min_le_right _ _)
  exact ⟨by linarith [core.lam_pos], hr.trans (min_le_left _ _),
    hrest.trans (min_le_left _ _), hlast.trans (min_le_left _ _), hlast.trans (min_le_right _ _)⟩

/-- The common lambda and all height caps are fixed before h and before the
actual reset/Profile. The additional cap may impose the outgoing-cone height
bound; the built-in caps also give the axis and terminal requirements. -/
theorem exists_scheduled_family_below (P m : ℝ) (hP : 0 < P) (hm : 0 < m)
    (cap : ℝ → ℝ) (hcap : ∀ K : ℝ, 0 < K → 0 < cap K)
    (extraHeight : OutgoingSchedule.Parameters → ℝ)
    (hextra : ∀ core : OutgoingSchedule.Parameters, 0 < extraHeight core) :
    ∃ (K B H : ℝ) (core : OutgoingSchedule.Parameters),
      0 < K ∧ 0 < B ∧ 0 < H ∧ core.P = P ∧ core.m = m ∧
      core.wait = 60 * Real.log (1 / core.lam) ∧
      core.lam < cap K ∧ core.lam < 1 / 120 ∧
      2 * H < core.lam ∧ H ≤ extraHeight core ∧ H ≤ 1 / 1000 ∧
      ∀ h : ℝ, 0 < h → h ≤ H →
        ∃ F : Profile, F.data.core = core ∧ F.data.h = h ∧ F.coefficientBound = K ∧
          ScheduleBounds F ∧ OutgoingProfile.Specification F B ∧ TerminalCone.SmallTail F.data := by
  obtain ⟨K, B, core, hK, hB, hcP, hcm, hwait, hcaller, hsmall, hf⟩ :=
    exists_scheduled_core_below P m hP hm cap hcap
  have hb := heightCap_bounds core (extraHeight core)
  refine ⟨K, B, heightCap core (extraHeight core), core, hK, hB,
    heightCap_pos core (hextra core), hcP, hcm, hwait, hcaller, hsmall,
    hb.1, hb.2.1, hb.2.2.1, ?_⟩
  intro h hh hH
  have ht : 2 * h < core.lam := (mul_le_mul_of_nonneg_left hH (by norm_num)).trans_lt hb.1
  obtain ⟨F, hcore, hh', hK', hs, hF⟩ := hf h hh ht
  refine ⟨F, hcore, hh', hK', hs, hF, ?_⟩
  unfold TerminalCone.SmallTail
  rw [hcore, hh']
  exact ⟨hH.trans hb.2.2.2.1, hH.trans hb.2.2.2.2⟩

end NavierStokes.ScheduledProfileChoice
