/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Certificate

namespace V7.Stage3BelowTwoS3F

noncomputable def shapeWitness (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m₁ m₂ : ℕ) : BelowTrialWitness p d where
  n := horizon p eps M D
  completedOne := m₁
  completedTwo := m₂
  phaseOne := primalData p (horizon p eps M D) (phaseOneOracle x0 M D oracle) 0 0
  phaseTwo := dualData p (horizon p eps M D)
    (phaseTwoOracle p eps M D x0 oracle)
  phaseTwoCenter := phaseTwoCenter p eps M D x0 oracle

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
      let pre := phaseOneNewTrace p eps M D x0 oracle (horizon p eps M D) ++
        phaseTwoNewTrace p eps M D x0 oracle (m₂ - 1)
      have hgen := chainChecks_ledger_prefix cached pre
        [phaseTwoObs p eps M D x0 oracle m₂]
      rw [hzero, total_chain p eps M D x0 oracle
        (horizon p eps M D) (m₂ - 1) rfl] at hgen
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
      let pre := phaseOneNewTrace p eps M D x0 oracle (horizon p eps M D) ++
        phaseTwoNewTrace p eps M D x0 oracle m₂
      have hgen := chainChecks_ledger_prefix cached pre []
      rw [hzero, total_chain p eps M D x0 oracle
        (horizon p eps M D) m₂ rfl] at hgen
      simpa only [ConsecutiveGuardLedger, pre, List.append_nil] using hgen
  | radius hP hQ hlarge =>
      let pre := phaseOneNewTrace p eps M D x0 oracle (horizon p eps M D) ++
        phaseTwoNewTrace p eps M D x0 oracle (horizon p eps M D)
      have hgen := chainChecks_ledger_prefix cached pre []
      rw [hzero, total_chain p eps M D x0 oracle
        (horizon p eps M D) (horizon p eps M D) rfl] at hgen
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
    report.calls ≤ 2 * horizon p eps M D := by
  cases hshape <;>
    simp [TrialReport.calls, phaseOneNewTrace, phaseTwoNewTrace] <;> omega

theorem fullShape_operational_contract (hp : 1 < p) (heps : 0 < eps)
    (hM : 0 < M) (hD : 0 < D)
    (hcached : cached.observation = oracle.observe x0)
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    BelowTrialOperationalContract p eps M D x0 cached oracle report
      (shapeWitness p eps M D x0 oracle m₁ m₂) := by
  have hn := one_le_horizon hp heps hM hD
  refine ⟨rfl, rfl, primal_dynamics p (horizon p eps M D) hn _ 0 0,
    rfl, rfl, dualQ_zero _ _ _, dual_dynamics p (horizon p eps M D) hn _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, fullShape_kinds hshape,
    fullShape_ledger hcached hshape, fullShape_accounting hshape,
    fullShape_calls_le hshape⟩
  · dsimp [shapeWitness]
    cases hshape <;> omega
  · dsimp [shapeWitness]
    cases hshape <;> omega
  · intro hm₂
    dsimp [shapeWitness] at hm₂ ⊢
    cases hshape <;> simp_all
  · intro k hk
    rfl
  · dsimp [shapeWitness]
    cases hshape <;>
      simp [phaseOneNewTrace, phaseTwoNewTrace, phaseOneObs, phaseOneState,
        phaseTwoObs, phaseTwoCenter, primalData, dualData]
  · intro terminal hout
    cases hshape with
    | primalSuccess m hm0 hmn hsmall hprior =>
        injection hout with heq
        subst terminal
        exact Or.inr ⟨rfl, hm0, rfl⟩
    | primalScale m hm0 hmn hprior hlarge hfail => cases hout
    | dualSuccess m hm0 hmn hP hQ hsmall =>
        injection hout with heq
        subst terminal
        exact Or.inl ⟨hm0, rfl⟩
    | dualScale m hm0 hmn hP hQ hlarge hfail => cases hout
    | radius hP hQ hlarge => cases hout
  · intro terminal hout
    cases hshape with
    | primalSuccess m hm0 hmn hsmall hprior => cases hout
    | primalScale m hm0 hmn hprior hlarge hfail => cases hout
    | dualSuccess m hm0 hmn hP hQ hsmall => cases hout
    | dualScale m hm0 hmn hP hQ hlarge hfail => cases hout
    | radius hP hQ hlarge =>
        injection hout with heq
        subst terminal
        exact ⟨rfl, rfl, rfl⟩

end V7.Stage3BelowTwoS3F
