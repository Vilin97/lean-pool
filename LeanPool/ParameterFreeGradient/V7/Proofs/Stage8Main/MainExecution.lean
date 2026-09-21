/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage8Main.Accounting

namespace V7.Stage8Main

private noncomputable def toAdmissible (input : MethodInput d)
    (inst : PositiveInstance input.p d input.x0)
    (hp : 1 < input.p) (heps : 0 < input.eps)
    (hsec : SecantInitialization input inst.oracle) :
    O3.AdmissibleInstance d input.p where
  f := inst.oracle.value
  grad := inst.oracle.gradient
  L := inst.L
  eps := input.eps
  x0 := input.x0
  z0 := input.z0
  M0 := input.M0
  p_gt_one := hp
  L_pos := inst.L_pos
  eps_pos := heps
  gradient_spec := inst.coordinateGradient
  convex := inst.convex
  minimizer_nonempty := inst.minimizerNonempty
  smooth := inst.smooth
  secant := hsec

theorem run_traceExact (method : O3.FirstOrderMethod d)
    (oracle : PairOracle d) {fuel : ℕ} {state : method.State}
    {history : List (Observation d)} (hhistory : TraceExact oracle history)
    {result : O3.RunResult d}
    (hrun : method.runFuel oracle fuel state history = some result) :
    TraceExact oracle result.queries := by
  induction fuel generalizing state history with
  | zero => simp [O3.FirstOrderMethod.runFuel] at hrun
  | succ fuel ih =>
      rw [O3.FirstOrderMethod.runFuel] at hrun
      cases haction : method.action state with
      | done x =>
          simp [haction] at hrun
          subst result
          exact hhistory
      | query x next =>
          simp [haction] at hrun
          apply ih (O3.traceExact_append hhistory ?_) hrun
          intro obs hobs
          simp at hobs
          subst obs
          rfl

theorem method_run_traceExact (method : O3.FirstOrderMethod d)
    (oracle : PairOracle d) (input : O3.MethodInput d) {fuel : ℕ}
    {result : O3.RunResult d}
    (hrun : method.run oracle input fuel = some result) :
    TraceExact oracle result.queries := by
  exact run_traceExact method oracle (O3.traceExact_nil oracle) hrun

private theorem one_le_log_ratio {L M0 : ℝ} (hM0 : 0 < M0)
    (hM0L : M0 ≤ L) :
    1 ≤ Real.log (Real.exp 1 + L / M0) := by
  have hratio : 0 ≤ L / M0 := by
    exact (zero_lt_one.trans_le ((le_div_iff₀ hM0).2 (by simpa using hM0L))).le
  calc
    1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (Real.exp 1 + L / M0) :=
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
        (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hratio) (by linarith)

theorem currentExecution (input : MethodInput d)
    (hp : 1 < input.p) (heps : 0 < input.eps) (hM0 : 0 < input.M0)
    (inst : PositiveInstance input.p d input.x0)
    (hsec : SecantInitialization input inst.oracle)
    (hM0L : input.M0 ≤ inst.L)
    (rateCoefficient : ℝ) (hrate : 1 ≤ rateCoefficient)
    (hanchorCoefficient : 1 + O3.anchorLogConstant ≤ rateCoefficient)
    (hlocal : ∀ data : RuntimeData d, data.input = input →
      runtimeCoefficient data * selectedAmort data.input.p data.hp ≤ rateCoefficient) :
    ∃ run : PairRunResult d,
      Executes (currentMethod d) input inst.oracle run ∧
      TraceExact inst.oracle run.trace ∧
      run.trace ≠ [] ∧
      run.trace.head?.map O3.Observation.point = some input.x0 ∧
      run.returnedWasQueried ∧
      lpNorm (conjugateExponent input.p)
        (inst.oracle.gradient run.returned) ≤ input.eps ∧
      (run.postInitializationCallCount : ℝ) ≤
        rateCoefficient * conditionBar inst input.eps ^ localCostExponent input.p +
        rateCoefficient * Real.log (Real.exp 1 + inst.L / input.M0) := by
  by_cases hsmall : lpNorm (conjugateExponent input.p)
      (inst.oracle.gradient input.x0) ≤ input.eps
  · let oldRun : O3.RunResult d :=
      ⟨input.x0, [inst.oracle.observe input.x0]⟩
    let run : PairRunResult d :=
      ⟨input.x0, [inst.oracle.observe input.x0]⟩
    have hmethod := currentMethod_early_run inst.oracle input hp heps hM0 hsmall
    have hK : 1 ≤ conditionBar inst input.eps := le_max_left _ _
    have ha : 0 < localCostExponent input.p :=
      V7.Stage2.localCostExponent_pos hp
    have hKpow : 1 ≤ conditionBar inst input.eps ^ localCostExponent input.p := by
      exact Real.one_le_rpow hK ha.le
    have hlog := one_le_log_ratio hM0 hM0L
    refine ⟨run, ?_, ?_, by simp [run], by simp [run, O3.PairOracle.observe],
      ?_, ?_, ?_⟩
    · exact ⟨2, oldRun, by simpa using hmethod, rfl, rfl⟩
    · intro obs hobs
      simp [run] at hobs
      subst obs
      rfl
    · simp [run, PairRunResult.returnedWasQueried, WasQueried,
        O3.PairOracle.observe]
    · simpa [run] using hsmall
    · change (([inst.oracle.observe input.x0].length : ℕ) : ℝ) ≤ _
      simp only [List.length_singleton, Nat.cast_one]
      have hfirst : 1 ≤ rateCoefficient *
          conditionBar inst input.eps ^ localCostExponent input.p := by
        nlinarith
      have hsecond : 0 ≤ rateCoefficient *
          Real.log (Real.exp 1 + inst.L / input.M0) :=
        mul_nonneg (hrate.trans' zero_le_one) (zero_le_one.trans hlog)
      linarith
  · have hlarge : input.eps < lpNorm (conjugateExponent input.p)
        (inst.oracle.gradient input.x0) := lt_of_not_ge hsmall
    let P := toAdmissible input inst hp heps hsec
    have hanchorOld := O3.anchor input.p d P (by simpa [P, toAdmissible,
      O3.AdmissibleInstance.anchorConfig] using hlarge)
    obtain ⟨anchorResult, hanchor, hscaleEq, hradiusEq, hpointEq,
      haccept, hscaleBound, hradiusBound, hanchorCount, hanchorTrace⟩ := hanchorOld
    let cached : CachedPair d := ⟨inst.oracle.observe input.x0⟩
    let G := lpNorm (conjugateExponent input.p)
      (inst.oracle.gradient input.x0)
    have hG : 0 < G := heps.trans hlarge
    let data := runtimeDataFromAnchor input hp heps hM0 cached G
      (by simp [cached, G, O3.PairOracle.observe]) hG anchorResult
    have hcached : data.cached.observation = inst.oracle.observe input.x0 := by
      rfl
    have hMaEq : data.Ma = anchorResult.acceptedScale := by
      rw [hscaleEq]
      rfl
    have hDaEq : data.G / data.Ma = anchorResult.acceptedRadius := by
      rw [hradiusEq, hscaleEq]
      rfl
    have hMaBound : data.Ma < 2 * inst.L := by
      simpa [hMaEq, P, toAdmissible] using hscaleBound
    have hDaBound : data.G / data.Ma ≤ 2 * inst.R := by
      rw [hDaEq]
      simpa [P, toAdmissible, O3.AdmissibleInstance.radius,
        PositiveInstance.R, minimizerDistance] using hradiusBound
    obtain ⟨controllerFuel, finish, hcontroller⟩ :=
      controller_terminates data inst hcached hlarge
    have hinv := runController_invariant data inst hcached hlarge
      (initial_readyInvariant data inst) hcontroller
    obtain ⟨tailFuel, htail⟩ := causalController_refines data inst hcached hlarge
      ([inst.oracle.observe input.x0] ++ anchorResult.observations) hcontroller
    have htail' : (currentMethod d).runFuel inst.oracle tailFuel
        (.controllerReady data initialRuntimeControllerState)
        ([inst.oracle.observe input.x0] ++ anchorResult.observations) =
        some (⟨finish.returned,
          ([inst.oracle.observe input.x0] ++ anchorResult.observations) ++
            reportsTrace finish.reports⟩ : O3.RunResult d) := by
      simpa [initialRuntimeControllerState, reportsTrace] using htail
    have hanchor' : O3.runAnchor inst.oracle
        (O3.anchorPrefixConfig input.toO3 (inst.oracle.value input.x0)
          (inst.oracle.gradient input.x0) G)
        (1 + Nat.ceil (Real.logb 2 (inst.L / input.M0))) 0 [] =
        some anchorResult := by
      change O3.runAnchor inst.oracle
        (O3.anchorPrefixConfig input.toO3 (inst.oracle.value input.x0)
          (inst.oracle.gradient input.x0) G)
        (1 + Nat.ceil (Real.logb 2 (inst.L / input.M0))) 0 [] =
          some anchorResult at hanchor
      exact hanchor
    obtain ⟨methodFuel, hmethod⟩ := currentMethod_full_splice inst.oracle input
      hp heps hM0 hlarge hanchor' htail'
    let oldRun : O3.RunResult d :=
      ⟨finish.returned,
        ([inst.oracle.observe input.x0] ++ anchorResult.observations) ++
          reportsTrace finish.reports⟩
    let run : PairRunResult d :=
      ⟨finish.returned,
        ([inst.oracle.observe input.x0] ++ anchorResult.observations) ++
          reportsTrace finish.reports⟩
    have hreportBound := reportCalls_bound data inst hcached hlarge
      hMaBound hDaBound hinv
    have hprefixAnchor : (anchorResult.observations.length : ℝ) ≤
        O3.anchorLogConstant * Real.log (Real.exp 1 + inst.L / input.M0) := by
      have hceil := O3.anchor_ceiling_le_log_overhead hM0 hM0L
      have hanchorCount' : (anchorResult.observations.length : ℝ) ≤
          (1 + Nat.ceil (Real.logb 2 (inst.L / input.M0)) : ℕ) := by
        exact_mod_cast (by simpa [P, toAdmissible] using hanchorCount)
      exact hanchorCount'.trans hceil
    have hlog := one_le_log_ratio hM0 hM0L
    have hprefix : ((1 + anchorResult.observations.length : ℕ) : ℝ) ≤
        (1 + O3.anchorLogConstant) *
          Real.log (Real.exp 1 + inst.L / input.M0) := by
      norm_num
      show (1 : ℝ) + anchorResult.observations.length ≤
        (1 + O3.anchorLogConstant) *
          Real.log (Real.exp 1 + inst.L / input.M0)
      nlinarith [hprefixAnchor]
    have hcount : (run.postInitializationCallCount : ℝ) =
        (1 + anchorResult.observations.length : ℕ) +
          ((finish.reports.map (fun report => report.calls)).sum : ℕ) := by
      simp [run, PairRunResult.postInitializationCallCount, reportsTrace_length]
      ring
    refine ⟨run, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨methodFuel, oldRun, by simpa [oldRun] using hmethod, rfl, rfl⟩
    · exact method_run_traceExact (currentMethod d) inst.oracle input.toO3 hmethod
    · simp [run]
    · simp [run, O3.PairOracle.observe]
    · rcases hinv.terminal with
        ⟨report, terminal, hreportMem, hout, hpoint, hterminalMem, hgradient⟩
      unfold PairRunResult.returnedWasQueried WasQueried
      refine ⟨terminal, ?_, hpoint⟩
      simp only [run, List.mem_append]
      right
      exact List.mem_flatMap.mpr ⟨report, hreportMem, hterminalMem⟩
    · rcases hinv.terminal with
        ⟨report, terminal, hreportMem, hout, hpoint, hterminalMem, hgradient⟩
      simpa [run, data, runtimeDataFromAnchor, ← hpoint] using hgradient
    · rw [hcount]
      have hKpow : 0 ≤ conditionBar inst input.eps ^
          localCostExponent input.p := Real.rpow_nonneg (by
            exact (zero_le_one.trans (le_max_left _ _))) _
      have hreportRate :
          (((finish.reports.map (fun report => report.calls)).sum : ℕ) : ℝ) ≤
            rateCoefficient * conditionBar inst input.eps ^
              localCostExponent input.p :=
        hreportBound.trans (mul_le_mul_of_nonneg_right (hlocal data rfl) hKpow)
      have hprefixRate : ((1 + anchorResult.observations.length : ℕ) : ℝ) ≤
          rateCoefficient * Real.log (Real.exp 1 + inst.L / input.M0) :=
        hprefix.trans (mul_le_mul_of_nonneg_right hanchorCoefficient
          (zero_le_one.trans hlog))
      exact add_le_add hprefixRate hreportRate |>.trans_eq (by ring)

end V7.Stage8Main
