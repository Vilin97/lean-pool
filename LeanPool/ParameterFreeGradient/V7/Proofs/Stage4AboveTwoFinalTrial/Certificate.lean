/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.AnalyticBridge
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage2.GuardSoundness

namespace V7.Stage4AboveTwoFinalTrial

open V7.Stage3BelowTwoS3F

theorem phaseOneNewTrace_exact (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) :
    TraceExact oracle (phaseOneNewTrace p eps M D x0 oracle m) := by
  intro obs hobs
  simp only [phaseOneNewTrace, List.mem_map] at hobs
  rcases hobs with ⟨k, hk, rfl⟩
  rfl

theorem phaseTwoNewTrace_exact (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) :
    TraceExact oracle (phaseTwoNewTrace p eps M D x0 oracle m) := by
  intro obs hobs
  simp only [phaseTwoNewTrace, List.mem_map] at hobs
  rcases hobs with ⟨k, hk, rfl⟩
  rfl

theorem fullShape_trace_exact
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    TraceExact oracle report.trace := by
  cases hshape with
  | primalSuccess => exact phaseOneNewTrace_exact p eps M D x0 oracle m₁
  | primalScale => exact phaseOneNewTrace_exact p eps M D x0 oracle m₁
  | dualSuccess =>
      intro obs hobs
      simp only [List.mem_append] at hobs
      exact hobs.elim
        (phaseOneNewTrace_exact p eps M D x0 oracle _ obs)
        (phaseTwoNewTrace_exact p eps M D x0 oracle _ obs)
  | dualScale =>
      intro obs hobs
      simp only [List.mem_append] at hobs
      exact hobs.elim
        (phaseOneNewTrace_exact p eps M D x0 oracle _ obs)
        (phaseTwoNewTrace_exact p eps M D x0 oracle _ obs)
  | radius =>
      intro obs hobs
      simp only [List.mem_append] at hobs
      exact hobs.elim
        (phaseOneNewTrace_exact p eps M D x0 oracle _ obs)
        (phaseTwoNewTrace_exact p eps M D x0 oracle _ obs)

theorem fullShape_outcome_exhaustive
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    TrialOutcomeExhaustive report := by
  cases hshape with
  | primalSuccess => exact Or.inl ⟨_, rfl⟩
  | primalScale => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | dualSuccess => exact Or.inl ⟨_, rfl⟩
  | dualScale => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | radius => exact Or.inr (Or.inr ⟨_, rfl⟩)

theorem phaseOneChecks_not_fails (p M eps D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ)
    (hholds : ∀ k < m, cocoPairHolds p M
      (phaseOneObs p eps M D x0 oracle k)
      (phaseOneObs p eps M D x0 oracle (k + 1))) :
    ∀ check ∈ phaseOneChecks p eps M D x0 oracle m,
      ¬ GuardFails p M oracle check.failure := by
  intro check hcheck
  simp only [phaseOneChecks, List.mem_map] at hcheck
  rcases hcheck with ⟨k, hk, rfl⟩
  exact (cocoPairHolds_iff_not_fails p M oracle _ _).1
    (hholds k (by simpa using hk))

theorem phaseTwoChecks_not_fails (p M eps D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ)
    (hholds : ∀ k < m, cocoPairHolds p M
      (phaseTwoObs p eps M D x0 oracle k)
      (phaseTwoObs p eps M D x0 oracle (k + 1))) :
    ∀ check ∈ phaseTwoChecks p eps M D x0 oracle m,
      ¬ GuardFails p M oracle check.failure := by
  intro check hcheck
  simp only [phaseTwoChecks, List.mem_map] at hcheck
  rcases hcheck with ⟨k, hk, rfl⟩
  exact (cocoPairHolds_iff_not_fails p M oracle _ _).1
    (hholds k (by simpa using hk))

theorem fullShape_guard_data (hcached : cached.observation = oracle.observe x0)
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    GuardDataExact cached oracle report := by
  have hcachedExact :
      cached.observation = oracle.observe cached.observation.point := by
    rw [hcached]
    rfl
  have hzero : cached.observation = phaseOneObs p eps M D x0 oracle 0 := by
    simpa [phaseOneObs, phaseOneState, O3.PairOracle.observe] using hcached
  cases hshape with
  | primalSuccess m hm0 hmn hsmall hprior =>
      have hm : m₁ - 1 + 1 = m₁ := by omega
      have hgen := chainChecks_data_exact_prefix cached oracle
        (phaseOneNewTrace p eps M D x0 oracle (m₁ - 1))
        [phaseOneObs p eps M D x0 oracle m₁] hcachedExact
        (phaseOneNewTrace_exact p eps M D x0 oracle (m₁ - 1))
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
      simpa only [GuardDataExact, ObservationAvailable, ht] using hgen
  | primalScale m hm0 hmn hprior hlarge hfail =>
      have hgen := chainChecks_data_exact_prefix cached oracle
        (phaseOneNewTrace p eps M D x0 oracle m₁) [] hcachedExact
        (phaseOneNewTrace_exact p eps M D x0 oracle m₁)
      rw [hzero, phaseOne_chain] at hgen
      simpa only [GuardDataExact, ObservationAvailable, List.append_nil] using hgen
  | dualSuccess m hm0 hmn hP hQ hsmall =>
      have hm : m₂ - 1 + 1 = m₂ := by omega
      let pre := phaseOneNewTrace p eps M D x0 oracle (nF p eps M D) ++
        phaseTwoNewTrace p eps M D x0 oracle (m₂ - 1)
      have hpre : TraceExact oracle pre := by
        intro obs hobs
        simp only [pre, List.mem_append] at hobs
        exact hobs.elim
          (phaseOneNewTrace_exact p eps M D x0 oracle _ obs)
          (phaseTwoNewTrace_exact p eps M D x0 oracle _ obs)
      have hgen := chainChecks_data_exact_prefix cached oracle pre
        [phaseTwoObs p eps M D x0 oracle m₂] hcachedExact hpre
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
      simpa only [GuardDataExact, ObservationAvailable, List.append_assoc, ht]
        using hgen
  | dualScale m hm0 hmn hP hQ hlarge hfail =>
      let pre := phaseOneNewTrace p eps M D x0 oracle (nF p eps M D) ++
        phaseTwoNewTrace p eps M D x0 oracle m₂
      have hpre : TraceExact oracle pre := by
        intro obs hobs
        simp only [pre, List.mem_append] at hobs
        exact hobs.elim
          (phaseOneNewTrace_exact p eps M D x0 oracle _ obs)
          (phaseTwoNewTrace_exact p eps M D x0 oracle _ obs)
      have hgen := chainChecks_data_exact_prefix cached oracle pre []
        hcachedExact hpre
      rw [hzero, total_chain p eps M D x0 oracle m₂] at hgen
      simpa only [GuardDataExact, ObservationAvailable, pre, List.append_nil]
        using hgen
  | radius hP hQ hlarge =>
      let pre := phaseOneNewTrace p eps M D x0 oracle (nF p eps M D) ++
        phaseTwoNewTrace p eps M D x0 oracle (nD p eps M D)
      have hpre : TraceExact oracle pre := by
        intro obs hobs
        simp only [pre, List.mem_append] at hobs
        exact hobs.elim
          (phaseOneNewTrace_exact p eps M D x0 oracle _ obs)
          (phaseTwoNewTrace_exact p eps M D x0 oracle _ obs)
      have hgen := chainChecks_data_exact_prefix cached oracle pre []
        hcachedExact hpre
      rw [hzero, total_chain p eps M D x0 oracle (nD p eps M D)] at hgen
      simpa only [GuardDataExact, ObservationAvailable, pre, List.append_nil]
        using hgen

theorem fullShape_certificate (hp : 2 < p) (heps : 0 < eps)
    (hM : 0 < M) (hD : 0 < D) (inst : PositiveInstance p d x0)
    (hcached : cached.observation = inst.oracle.observe x0)
    (hshape : FullShape p eps M D x0 inst.oracle report m₁ m₂) :
    TrialCertificate eps p M D inst.L inst.R cached inst.oracle report := by
  have hp1 : 1 < p := by linarith
  have htrace := fullShape_trace_exact hshape
  have hdata := fullShape_guard_data hcached hshape
  refine ⟨htrace, hdata, fullShape_outcome_exhaustive hshape, ?_, ?_, ?_⟩
  · intro terminal hout
    cases hshape with
    | primalSuccess m hm0 hmn hsmall hprior =>
        injection hout with heq
        subst terminal
        have hmem : phaseOneObs p eps M D x0 inst.oracle m₁ ∈
            phaseOneNewTrace p eps M D x0 inst.oracle m₁ := by
          have hm : m₁ - 1 + 1 = m₁ := by omega
          have ht := phaseOneTrace_succ p eps M D x0 inst.oracle (m₁ - 1)
          rw [hm] at ht
          rw [ht]
          simp
        exact ⟨hmem, rfl,
          phaseOneChecks_not_fails p M eps D x0 inst.oracle (m₁ - 1) hprior,
          hsmall⟩
    | primalScale => cases hout
    | dualSuccess m hm0 hmn hP hQ hsmall =>
        injection hout with heq
        subst terminal
        have hmem : phaseTwoObs p eps M D x0 inst.oracle m₂ ∈
            phaseOneNewTrace p eps M D x0 inst.oracle (nF p eps M D) ++
              phaseTwoNewTrace p eps M D x0 inst.oracle m₂ := by
          apply List.mem_append_right
          have hm : m₂ - 1 + 1 = m₂ := by omega
          have ht := phaseTwoTrace_succ p eps M D x0 inst.oracle (m₂ - 1)
          rw [hm] at ht
          rw [ht]
          simp
        refine ⟨hmem, rfl, ?_, hsmall⟩
        intro check hcheck
        simp only [allChecks, List.mem_append] at hcheck
        exact hcheck.elim
          (phaseOneChecks_not_fails p M eps D x0 inst.oracle _ hP check)
          (phaseTwoChecks_not_fails p M eps D x0 inst.oracle (m₂ - 1) hQ check)
    | dualScale => cases hout
    | radius => cases hout
  · intro failed hout
    cases hshape with
    | primalSuccess => cases hout
    | primalScale m hm0 hmn hprior hlarge hfail =>
        injection hout with heq
        subst failed
        have hm : m₁ - 1 + 1 = m₁ := by omega
        have hlist : phaseOneChecks p eps M D x0 inst.oracle m₁ =
            phaseOneChecks p eps M D x0 inst.oracle (m₁ - 1) ++
              [cocoCheck (phaseOneObs p eps M D x0 inst.oracle (m₁ - 1))
                (phaseOneObs p eps M D x0 inst.oracle m₁)] := by
          calc
            _ = phaseOneChecks p eps M D x0 inst.oracle (m₁ - 1 + 1) := by rw [hm]
            _ = _ := by rw [phaseOneChecks_succ, hm]
        have hgf : GuardFails p M inst.oracle
            (cocoCheck (phaseOneObs p eps M D x0 inst.oracle (m₁ - 1))
              (phaseOneObs p eps M D x0 inst.oracle m₁)).failure := by
          apply Classical.byContradiction
          intro hnot
          exact hfail ((cocoPairHolds_iff_not_fails p M inst.oracle _ _).2 hnot)
        refine ⟨by rw [hlist]; simp, by rw [hlist]; simp, ?_, hgf,
          V7.Stage2.failed_cocoercivityGuard_lt_trueScale hp1 inst rfl _ _ hfail⟩
        rw [hlist]
        simpa using phaseOneChecks_not_fails p M eps D x0 inst.oracle
          (m₁ - 1) hprior
    | dualSuccess => cases hout
    | dualScale m hm0 hmn hP hQ hlarge hfail =>
        injection hout with heq
        subst failed
        have hm : m₂ - 1 + 1 = m₂ := by omega
        have hqlist : phaseTwoChecks p eps M D x0 inst.oracle m₂ =
            phaseTwoChecks p eps M D x0 inst.oracle (m₂ - 1) ++
              [cocoCheck (phaseTwoObs p eps M D x0 inst.oracle (m₂ - 1))
                (phaseTwoObs p eps M D x0 inst.oracle m₂)] := by
          calc
            _ = phaseTwoChecks p eps M D x0 inst.oracle (m₂ - 1 + 1) := by rw [hm]
            _ = _ := by rw [phaseTwoChecks_succ, hm]
        have hlist : allChecks p eps M D x0 inst.oracle
              (nF p eps M D) m₂ =
            allChecks p eps M D x0 inst.oracle (nF p eps M D) (m₂ - 1) ++
              [cocoCheck (phaseTwoObs p eps M D x0 inst.oracle (m₂ - 1))
                (phaseTwoObs p eps M D x0 inst.oracle m₂)] := by
          simp only [allChecks, hqlist, List.append_assoc]
        have hgf : GuardFails p M inst.oracle
            (cocoCheck (phaseTwoObs p eps M D x0 inst.oracle (m₂ - 1))
              (phaseTwoObs p eps M D x0 inst.oracle m₂)).failure := by
          apply Classical.byContradiction
          intro hnot
          exact hfail ((cocoPairHolds_iff_not_fails p M inst.oracle _ _).2 hnot)
        refine ⟨by rw [hlist]; simp, by rw [hlist]; simp, ?_, hgf,
          V7.Stage2.failed_cocoercivityGuard_lt_trueScale hp1 inst rfl _ _ hfail⟩
        rw [hlist]
        intro check hcheck
        simp only [List.dropLast_concat] at hcheck
        simp only [allChecks, List.mem_append] at hcheck
        exact hcheck.elim
          (phaseOneChecks_not_fails p M eps D x0 inst.oracle _ hP check)
          (phaseTwoChecks_not_fails p M eps D x0 inst.oracle (m₂ - 1) hQ check)
    | radius => cases hout
  · intro terminal hout
    cases hshape with
    | primalSuccess => cases hout
    | primalScale => cases hout
    | dualSuccess => cases hout
    | dualScale => cases hout
    | radius hP hQ hlarge =>
        injection hout with heq
        subst terminal
        have hmem : phaseTwoObs p eps M D x0 inst.oracle (nD p eps M D) ∈
            phaseOneNewTrace p eps M D x0 inst.oracle (nF p eps M D) ++
              phaseTwoNewTrace p eps M D x0 inst.oracle (nD p eps M D) := by
          apply List.mem_append_right
          have hn := one_le_nD hp heps hM hD
          have hnd : nD p eps M D - 1 + 1 = nD p eps M D := by omega
          have ht := phaseTwoTrace_succ p eps M D x0 inst.oracle
            (nD p eps M D - 1)
          rw [hnd] at ht
          rw [ht]
          simp
        refine ⟨hmem, rfl, ?_, hlarge, ?_⟩
        · intro check hcheck
          simp only [allChecks, List.mem_append] at hcheck
          exact hcheck.elim
            (phaseOneChecks_not_fails p M eps D x0 inst.oracle _ hP check)
            (phaseTwoChecks_not_fails p M eps D x0 inst.oracle _ hQ check)
        · by_contra hnot
          have hDR : inst.R ≤ D := le_of_not_gt hnot
          have hgood := terminal_gradient_le p eps M D hp heps hM hD
            inst hDR hP hQ
          linarith

end V7.Stage4AboveTwoFinalTrial
