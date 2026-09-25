/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.Semantics

/-!
The Euclidean source execution connected to the analytic gap and terminal-gradient estimates.
-/

@[expose] public section

namespace V7
namespace Stage1E03

theorem positive_fstar_eq_minimizer (inst : PositiveInstance p d x0)
    {xstar : Point d} (hxstar : xstar ∈ MinimizerSet inst.oracle) :
    inst.fstar = inst.oracle.value xstar := by
  have himage : inst.oracle.value '' MinimizerSet inst.oracle =
      {inst.oracle.value xstar} := by
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Set.mem_singleton_iff.mpr (le_antisymm (hy xstar) (hxstar y))
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      exact ⟨xstar, hxstar, rfl⟩
  rw [PositiveInstance.fstar, himage]
  simp

theorem positive_fstar_eq_sInf_range (inst : PositiveInstance p d x0) :
    inst.fstar = sInf (Set.range inst.oracle.value) := by
  obtain ⟨xstar, hxstar⟩ := inst.minimizerNonempty
  rw [positive_fstar_eq_minimizer inst hxstar]
  apply le_antisymm
  · apply le_csInf
    · exact Set.range_nonempty _
    · rintro y ⟨z, rfl⟩
      exact hxstar z
  · apply csInf_le
    · exact ⟨inst.oracle.value xstar, by
        rintro y ⟨z, rfl⟩
        exact hxstar z⟩
    · exact ⟨xstar, rfl⟩

theorem source_current_analytic_bridge (inst : PositiveInstance 2 d x0)
    (M D : ℝ) (n : ℕ) (hM : 0 < M) (hn : 1 ≤ n)
    (hDR : inst.R ≤ D) (report : TrialReport d)
    (hall : ∀ check ∈ report.checkedGuards, CheckHolds 2 M check)
    (hguards : report.checkedGuards = sourceGuardSchedule inst M n) :
    let phaseA := sourcePhaseAData inst M D n
    let phaseB := sourcePhaseBData inst M n (sourceU inst M n)
    (phaseA.inst.oracle.value (phaseA.x n) - phaseA.inst.fstar ≤
        phaseA.M * phaseA.D ^ (2 : ℕ) / (2 * phaseA.A n) ∧
      phaseA.M * phaseA.D ^ (2 : ℕ) / (2 * phaseA.A n) ≤
        2 * phaseA.M * phaseA.D ^ (2 : ℕ) / ((n : ℝ) + 1) ^ (2 : ℕ)) ∧
    ((lpNorm 2 (phaseB.oracle.gradient (phaseB.u n))) ^ (2 : ℕ) ≤
        2 * phaseB.M * (phaseB.oracle.value phaseB.U - phaseB.fstar) /
          (phaseB.theta 0) ^ (2 : ℕ) ∧
      phaseB.theta 0 ≥ ((n : ℝ) + 1) / Real.sqrt 2) := by
  let phaseA := sourcePhaseAData inst M D n
  let phaseB := sourcePhaseBData inst M n (sourceU inst M n)
  have hAdyn := sourcePhaseA_dynamics inst M D n hM
  have hBdyn := sourcePhaseB_dynamics inst M n (sourceU inst M n) hM hn
  have hupper : ∀ k < n,
      UpperModelGuard 2 M inst.oracle (phaseA.y k) (phaseA.x (k + 1)) := by
    intro k hk
    have hmem := source_phaseA_guard_mem inst M D n k hk
    rw [← hguards] at hmem
    have hc := hall _ hmem
    simpa [phaseA, CheckHolds, exactGuardCheck, UpperModelGuard,
      O3.PairOracle.observe] using hc
  have hinterp : ∀ i ≤ n, ∀ j ≤ n,
      EuclideanInterpolationGuard M inst.oracle (phaseB.u i) (phaseB.u j) := by
    intro i hi j hj
    have hmem := source_interpolation_guard_mem inst M n i j hi hj
    rw [← hguards] at hmem
    have hc := hall _ hmem
    simpa [phaseB, CheckHolds, exactGuardCheck, EuclideanInterpolationGuard,
      O3.PairOracle.observe] using hc
  have hterminal : TerminalDescentGuard M inst.oracle
      (phaseB.u n) (phaseB.v n) := by
    have hmem : sourceTerminalGuard inst M n ∈ report.checkedGuards := by
      rw [hguards]
      simp [sourceGuardSchedule]
    have hc := hall _ hmem
    dsimp only [phaseB, sourcePhaseBData]
    simpa [sourceTerminalGuard, terminalCheck, CheckHolds,
      TerminalDescentGuard, sourceU, O3.ogmgTerminalObservation,
      O3.ogmgObservation, O3.ogmgGradient, O3.PairOracle.observe,
      O3.stage9ExecutionConfig] using hc
  have hAass : EuclideanGapAssumptions phaseA := by
    refine ⟨hAdyn, hDR, rfl, ?_, ?_, sourcePhaseA_trace_exact inst M D n,
      rfl, hupper, ?_⟩
    · simp [phaseA, sourcePhaseAData, sourceEstimateMinimizer,
        O3.Stage8EuclideanMinimizer.euclideanPsiMinimizer]
    · exact hAdyn.2.2.2.2
    · exact O3.euclideanA_pos_of_one_le hn
  obtain ⟨xstar, hxstar⟩ := inst.minimizerNonempty
  have hfstar := positive_fstar_eq_minimizer inst hxstar
  have hBass : OGMGAssumptions phaseB := by
    rcases hBdyn with ⟨hn', hM', hthetaN, hu0, hvm1, hthetaOrd,
      htheta0, hrec, hvn⟩
    refine ⟨⟨hn', hM', hthetaN, hu0, hvm1, hthetaOrd, htheta0, hrec, hvn⟩,
      inst.convex, inst.coordinateGradient, ?_, ⟨xstar, ?_, hxstar⟩,
      hthetaN, hu0, hvm1, hthetaOrd, htheta0, hrec, hvn, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [phaseB, sourcePhaseBData] using positive_fstar_eq_sInf_range inst
    · simpa [phaseB, sourcePhaseBData] using hfstar.symm
    · change TraceExact inst.oracle
        (sourcePhaseBData inst M n (sourceU inst M n)).trace
      exact sourcePhaseB_trace_exact inst M n (sourceU inst M n)
    · rfl
    · change ∀ i ≤ n, ∀ j ≤ n,
        EuclideanInterpolationGuard M inst.oracle
          ((sourcePhaseBData inst M n (sourceU inst M n)).u i)
          ((sourcePhaseBData inst M n (sourceU inst M n)).u j)
      exact hinterp
    · simp only [phaseB, sourcePhaseBData, WasQueried,
        List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false]
      refine ⟨inst.oracle.observe
          (O3.ogmgV (O3.stage9ExecutionConfig n inst.oracle M
            (sourceU inst M n)) n), ?_, rfl⟩
      exact Or.inr rfl
    · change TerminalDescentGuard M inst.oracle
        ((sourcePhaseBData inst M n (sourceU inst M n)).u n)
        ((sourcePhaseBData inst M n (sourceU inst M n)).v n)
      exact hterminal
  have hAresult := V7.euclideanGap d n phaseA hAass
  have hBresult := V7.finiteDataOGMG d n phaseB hBass
  exact ⟨hAresult, hBresult⟩

/-- The scalar consequence needed by the radius branch, derived from the
current frozen E01/E02 carriers rather than from the legacy Stage-10
composition theorem. -/
theorem source_current_gradient_bound (inst : PositiveInstance 2 d x0)
    (M D : ℝ) (n : ℕ) (hM : 0 < M) (hD : 0 < D) (hn : 1 ≤ n)
    (hDR : inst.R ≤ D) (report : TrialReport d)
    (hall : ∀ check ∈ report.checkedGuards, CheckHolds 2 M check)
    (hguards : report.checkedGuards = sourceGuardSchedule inst M n) :
    lpNorm 2 (inst.oracle.gradient
        ((sourcePhaseBData inst M n (sourceU inst M n)).u n)) ≤
      2 * Real.sqrt 2 * M * D / (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
  have hbridge := source_current_analytic_bridge inst M D n hM hn hDR
    report hall hguards
  let phaseA := sourcePhaseAData inst M D n
  let phaseB := sourcePhaseBData inst M n (sourceU inst M n)
  let gnorm := lpNorm 2 (phaseB.oracle.gradient (phaseB.u n))
  let theta := phaseB.theta 0
  let s : ℝ := (n : ℝ) + 1
  have hs : 0 < s := by positivity
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have ht : 0 < theta := by
    dsimp only [theta, phaseB, sourcePhaseBData]
    exact O3.stage9Theta_pos n 0
  have ht2 : 0 < theta ^ 2 := sq_pos_of_pos ht
  have hg : 0 ≤ gnorm := O3.lpNorm_nonneg 2 _
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htheta : s / Real.sqrt 2 ≤ theta := by
    simpa only [s, theta, phaseB] using hbridge.2.2
  have hstheta : s ^ 2 ≤ 2 * theta ^ 2 := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [div_le_iff₀ hsqrt] at htheta
    nlinarith
  have hgap2 : phaseA.inst.oracle.value (phaseA.x n) - phaseA.inst.fstar ≤
      2 * M * D ^ 2 / s ^ 2 := by
    have hgap := hbridge.1.1.trans hbridge.1.2
    simpa only [phaseA, sourcePhaseAData, s, pow_two] using hgap
  have hphaseLink : phaseA.inst.oracle.value (phaseA.x n) - phaseA.inst.fstar =
      phaseB.oracle.value phaseB.U - phaseB.fstar := by
    rfl
  have hgsq : gnorm ^ 2 ≤
      2 * M * (phaseB.oracle.value phaseB.U - phaseB.fstar) / theta ^ 2 := by
    have hraw := hbridge.2.1
    change gnorm ^ 2 ≤
      2 * M * (phaseB.oracle.value phaseB.U - phaseB.fstar) / theta ^ 2 at hraw
    exact hraw
  have hmul : gnorm ^ 2 * theta ^ 2 ≤
      2 * M * (phaseB.oracle.value phaseB.U - phaseB.fstar) := by
    exact (le_div_iff₀ ht2).mp hgsq
  have hgapmul : (phaseB.oracle.value phaseB.U - phaseB.fstar) * s ^ 2 ≤
      2 * M * D ^ 2 := by
    rw [← hphaseLink]
    exact (le_div_iff₀ hs2).mp hgap2
  have hcore : gnorm ^ 2 * theta ^ 2 * s ^ 2 ≤
      4 * M ^ 2 * D ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hmul hs2.le
    have h2 := mul_le_mul_of_nonneg_left hgapmul
      (by positivity : 0 ≤ 2 * M)
    nlinarith
  have hfinalSq : (gnorm * s ^ 2) ^ 2 ≤
      (2 * Real.sqrt 2 * M * D) ^ 2 := by
    have hnon : 0 ≤ gnorm ^ 2 * s ^ 2 := by positivity
    have hscale := mul_le_mul_of_nonneg_left hstheta hnon
    nlinarith
  have hlinear : gnorm * s ^ 2 ≤ 2 * Real.sqrt 2 * M * D := by
    have hleft : 0 ≤ gnorm * s ^ 2 := by positivity
    have hright : 0 ≤ 2 * Real.sqrt 2 * M * D := by positivity
    nlinarith
  rw [show s ^ 2 = s * s by ring] at hlinear
  exact (le_div_iff₀ (mul_pos hs hs)).2 (by
    simpa only [gnorm, phaseB, sourcePhaseBData, s] using hlinear)

end Stage1E03
end V7
