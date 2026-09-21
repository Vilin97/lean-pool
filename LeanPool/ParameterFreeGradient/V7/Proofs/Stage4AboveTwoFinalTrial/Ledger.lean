/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Semantics
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Ledger

namespace V7.Stage4AboveTwoFinalTrial

variable {d : ℕ} {eps : ℝ} {oracle : PairOracle d}
  {report : TrialReport d} {cached : CachedPair d}

open V7.Stage3BelowTwoS3F

theorem phaseOneTrace_lastD (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) :
    (phaseOneNewTrace p eps M D x0 oracle m).getLastD
      (phaseOneObs p eps M D x0 oracle 0) = phaseOneObs p eps M D x0 oracle m := by
  cases m with
  | zero => simp [phaseOneNewTrace]
  | succ m => rw [phaseOneTrace_succ]; simp

theorem phaseTwoTrace_lastD (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) :
    (phaseTwoNewTrace p eps M D x0 oracle m).getLastD
      (phaseTwoObs p eps M D x0 oracle 0) = phaseTwoObs p eps M D x0 oracle m := by
  cases m with
  | zero => simp [phaseTwoNewTrace]
  | succ m => rw [phaseTwoTrace_succ]; simp

theorem phaseOne_chain (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) :
    chainChecks (phaseOneObs p eps M D x0 oracle 0)
      (phaseOneNewTrace p eps M D x0 oracle m) =
        phaseOneChecks p eps M D x0 oracle m := by
  induction m with
  | zero => simp [phaseOneNewTrace, phaseOneChecks, chainChecks]
  | succ m ih =>
      rw [phaseOneTrace_succ, chainChecks_append, phaseOneTrace_lastD,
        ih, phaseOneChecks_succ]
      rfl

theorem phaseTwo_chain (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) :
    chainChecks (phaseTwoObs p eps M D x0 oracle 0)
      (phaseTwoNewTrace p eps M D x0 oracle m) =
        phaseTwoChecks p eps M D x0 oracle m := by
  induction m with
  | zero => simp [phaseTwoNewTrace, phaseTwoChecks, chainChecks]
  | succ m ih =>
      rw [phaseTwoTrace_succ, chainChecks_append, phaseTwoTrace_lastD,
        ih, phaseTwoChecks_succ]
      rfl

theorem total_chain (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m₂ : ℕ) :
    chainChecks (phaseOneObs p eps M D x0 oracle 0)
      (phaseOneNewTrace p eps M D x0 oracle (nF p eps M D) ++
        phaseTwoNewTrace p eps M D x0 oracle m₂) =
      allChecks p eps M D x0 oracle (nF p eps M D) m₂ := by
  rw [chainChecks_append, phaseOneTrace_lastD, phaseOne_chain]
  rw [← phaseTwoObs_zero, phaseTwo_chain]
  rfl

theorem fullShape_kinds
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    CheckedGuardsHaveKinds report [.cocoercivity] := by
  intro check hcheck
  cases hshape with
  | primalSuccess m hm0 hmn hsmall hprior =>
      simp only [phaseOneChecks, List.mem_map] at hcheck
      rcases hcheck with ⟨k, hk, rfl⟩
      simp [cocoCheck]
  | primalScale m hm0 hmn hprior hlarge hfail =>
      simp only [phaseOneChecks, List.mem_map] at hcheck
      rcases hcheck with ⟨k, hk, rfl⟩
      simp [cocoCheck]
  | dualSuccess m hm0 hmn hP hQ hsmall =>
      simp only [allChecks, List.mem_append] at hcheck
      rcases hcheck with hcheck | hcheck
      · simp only [phaseOneChecks, List.mem_map] at hcheck
        rcases hcheck with ⟨k, hk, rfl⟩
        simp [cocoCheck]
      · simp only [phaseTwoChecks, List.mem_map] at hcheck
        rcases hcheck with ⟨k, hk, rfl⟩
        simp [cocoCheck]
  | dualScale m hm0 hmn hP hQ hlarge hfail =>
      simp only [allChecks, List.mem_append] at hcheck
      rcases hcheck with hcheck | hcheck
      · simp only [phaseOneChecks, List.mem_map] at hcheck
        rcases hcheck with ⟨k, hk, rfl⟩
        simp [cocoCheck]
      · simp only [phaseTwoChecks, List.mem_map] at hcheck
        rcases hcheck with ⟨k, hk, rfl⟩
        simp [cocoCheck]
  | radius hP hQ hlarge =>
      simp only [allChecks, List.mem_append] at hcheck
      rcases hcheck with hcheck | hcheck
      · simp only [phaseOneChecks, List.mem_map] at hcheck
        rcases hcheck with ⟨k, hk, rfl⟩
        simp [cocoCheck]
      · simp only [phaseTwoChecks, List.mem_map] at hcheck
        rcases hcheck with ⟨k, hk, rfl⟩
        simp [cocoCheck]

theorem fullShape_ledger
    (hcached : cached.observation = oracle.observe x0)
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    ConsecutiveGuardLedger cached report := by
  have hzero : cached.observation = phaseOneObs p eps M D x0 oracle 0 := by
    simpa [phaseOneObs, phaseOneState, O3.PairOracle.observe] using hcached
  cases hshape with
  | primalSuccess m hm0 hmn hsmall hprior =>
      have hm : m₁ - 1 + 1 = m₁ := by omega
      have hgen := chainChecks_ledger_prefix cached
        (phaseOneNewTrace p eps M D x0 oracle (m₁ - 1))
        [phaseOneObs p eps M D x0 oracle m₁]
      rw [hzero, phaseOne_chain] at hgen
      have ht : phaseOneNewTrace p eps M D x0 oracle (m₁ - 1) ++
          [phaseOneObs p eps M D x0 oracle m₁] =
          phaseOneNewTrace p eps M D x0 oracle m₁ := by
        calc
          _ = phaseOneNewTrace p eps M D x0 oracle (m₁ - 1) ++
              [phaseOneObs p eps M D x0 oracle (m₁ - 1 + 1)] := by rw [hm]
          _ = phaseOneNewTrace p eps M D x0 oracle (m₁ - 1 + 1) :=
            (phaseOneTrace_succ p eps M D x0 oracle (m₁ - 1)).symm
          _ = _ := by rw [hm]
      simpa only [ConsecutiveGuardLedger, ht] using hgen
  | primalScale m hm0 hmn hprior hlarge hfail =>
      have hgen := chainChecks_ledger_prefix cached
        (phaseOneNewTrace p eps M D x0 oracle m₁) []
      rw [hzero, phaseOne_chain] at hgen
      simpa only [ConsecutiveGuardLedger, List.append_nil] using hgen
  | dualSuccess m hm0 hmn hP hQ hsmall =>
      have hm : m₂ - 1 + 1 = m₂ := by omega
      let pre := phaseOneNewTrace p eps M D x0 oracle (nF p eps M D) ++
        phaseTwoNewTrace p eps M D x0 oracle (m₂ - 1)
      have hgen := chainChecks_ledger_prefix cached pre
        [phaseTwoObs p eps M D x0 oracle m₂]
      rw [hzero, total_chain p eps M D x0 oracle (m₂ - 1)] at hgen
      dsimp only [pre] at hgen
      have ht : phaseTwoNewTrace p eps M D x0 oracle (m₂ - 1) ++
          [phaseTwoObs p eps M D x0 oracle m₂] =
          phaseTwoNewTrace p eps M D x0 oracle m₂ := by
        calc
          _ = phaseTwoNewTrace p eps M D x0 oracle (m₂ - 1) ++
              [phaseTwoObs p eps M D x0 oracle (m₂ - 1 + 1)] := by rw [hm]
          _ = phaseTwoNewTrace p eps M D x0 oracle (m₂ - 1 + 1) :=
            (phaseTwoTrace_succ p eps M D x0 oracle (m₂ - 1)).symm
          _ = _ := by rw [hm]
      simpa only [ConsecutiveGuardLedger, List.append_assoc, ht] using hgen
  | dualScale m hm0 hmn hP hQ hlarge hfail =>
      let pre := phaseOneNewTrace p eps M D x0 oracle (nF p eps M D) ++
        phaseTwoNewTrace p eps M D x0 oracle m₂
      have hgen := chainChecks_ledger_prefix cached pre []
      rw [hzero, total_chain p eps M D x0 oracle m₂] at hgen
      simpa only [ConsecutiveGuardLedger, pre, List.append_nil] using hgen
  | radius hP hQ hlarge =>
      let pre := phaseOneNewTrace p eps M D x0 oracle (nF p eps M D) ++
        phaseTwoNewTrace p eps M D x0 oracle (nD p eps M D)
      have hgen := chainChecks_ledger_prefix cached pre []
      rw [hzero, total_chain p eps M D x0 oracle (nD p eps M D)] at hgen
      simpa only [ConsecutiveGuardLedger, pre, List.append_nil] using hgen

theorem fullShape_accounting
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    report.consecutiveGuardAccounting := by
  cases hshape <;>
    simp [TrialReport.consecutiveGuardAccounting, TrialReport.calls,
      phaseOneNewTrace, phaseTwoNewTrace, phaseOneChecks, phaseTwoChecks,
      allChecks] <;> omega

theorem fullShape_calls_le
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    report.calls ≤ nF p eps M D + nD p eps M D := by
  cases hshape <;>
    simp [TrialReport.calls, phaseOneNewTrace, phaseTwoNewTrace] <;> omega

end V7.Stage4AboveTwoFinalTrial
