/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.Certificate

/-!
Existence of a certified Euclidean two-phase local trial with its query bound.
-/

@[expose] public section

namespace V7

open Stage1E03

theorem euclideanTrial : EuclideanTrialStatement := by
  refine ⟨10, by norm_num, ?_⟩
  intro d eps M D heps hM hD x0 cached
  let n := horizon eps M D
  let trial := euclideanLocalTrial eps x0 n
  refine ⟨n, n, trial, ?_, rfl, ?_⟩
  · rfl
  intro inst hcached hG hDG
  have hMD : eps < M * D := by
    have hmul := mul_le_mul_of_nonneg_left hDG hM.le
    have hcancel : M * (lpNorm 2 (inst.oracle.gradient x0) / M) =
        lpNorm 2 (inst.oracle.gradient x0) := by field_simp [hM.ne']
    rw [hcancel] at hmul
    linarith
  have hkappa : 1 < M * D / eps := by
    exact (lt_div_iff₀ heps).2 (by simpa using hMD)
  have hn : 1 ≤ n := by
    simpa [n] using one_le_horizon hkappa.le
  let report := sourcePhaseAReport inst eps M n 0 n
  let phaseA := sourcePhaseAData inst M D n
  let phaseB := sourcePhaseBData inst M n (sourceU inst M n)
  have hshape : FullReportShape inst eps M n report := by
    simpa [report] using sourceFullReport_shape inst eps M n hn
  refine ⟨report, phaseA, phaseB, ?_, ?_, ?_, ?_, ?_⟩
  · change (programTrial fun M _D _cached =>
        ⟨phaseABudget n n,
          phaseAProgram eps M x0 n 0 ⟨x0, 0⟩ none [] n⟩).Executes
        M D cached inst.oracle report
    have hexec := programTrial_executes inst.oracle (fun M _D _cached =>
      ⟨phaseABudget n n,
        phaseAProgram eps M x0 n 0 ⟨x0, 0⟩ none [] n⟩) M D cached
    rw [eval_full_eq_source inst eps M n (by omega)] at hexec
    simpa [report] using hexec
  · exact source_trial_certificate inst eps M D n heps hM hD hn rfl
      hkappa.le hG cached hcached report hshape
  · simpa [phaseA, phaseB] using
      source_operational_contract inst eps M D n hM hn report hshape
  · simpa using fullShape_calls_le hshape
  · have hcallsNat := fullShape_calls_le hshape
    have hcallsReal : (report.calls : ℝ) ≤
        (O3.euclideanTrialCallBudget n n : ℝ) := by
      exact_mod_cast hcallsNat
    have hbudget := O3.euclideanTrialCallBudget_horizon (kappa := M * D / eps)
      hkappa.le
    exact hcallsReal.trans (by
      simpa [n, horizon, O3.euclideanHorizon] using hbudget)

end V7
