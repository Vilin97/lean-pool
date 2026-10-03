/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForWorkOnes.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# One-prefix work-tape loop combinator — proof internals

This module proves exact body embedding, driver transitions, certified loop
execution, and one-way-output preservation for `TM.forWorkOnesTM`.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Embed a body configuration in the body phase of `forWorkOnesTM`. -/
def forWorkOnesBodyWrap (driverIdx : Fin n) (body : TM n)
    (cfg : Cfg n body.Q) : Cfg n (forWorkOnesTM driverIdx body).Q :=
  { state := .inr cfg.state
    input := cfg.input
    work := cfg.work
    output := cfg.output }

/-- Every nonhalting body step is simulated exactly. -/
theorem forWorkOnesTM_body_step_internal (driverIdx : Fin n) (body : TM n)
    {cfg next : Cfg n body.Q} (hstep : body.step cfg = some next) :
    (forWorkOnesTM driverIdx body).step
      (forWorkOnesBodyWrap driverIdx body cfg) =
        some (forWorkOnesBodyWrap driverIdx body next) := by
  have hne : cfg.state ≠ body.qhalt := state_ne_qhalt_of_step hstep
  rw [TM.step, ite_eq_right (by simp [forWorkOnesBodyWrap, forWorkOnesTM])]
  simp only [forWorkOnesBodyWrap, forWorkOnesTM, hne, ↓reduceIte]
  rw [TM.step, ite_eq_right hne] at hstep
  revert hstep
  generalize body.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
    cfg.output.read = action
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  intro hstep
  cases Option.some.inj hstep
  rfl

/-- Exact body runs lift through the combined machine's body phase. -/
theorem forWorkOnesTM_body_reachesIn_internal (driverIdx : Fin n) (body : TM n)
    {time : ℕ} {cfg next : Cfg n body.Q}
    (hreach : body.reachesIn time cfg next) :
    (forWorkOnesTM driverIdx body).reachesIn time
      (forWorkOnesBodyWrap driverIdx body cfg)
      (forWorkOnesBodyWrap driverIdx body next) :=
  reachesIn_map (forWorkOnesBodyWrap driverIdx body)
    (fun _ _ => forWorkOnesTM_body_step_internal driverIdx body) hreach

/-- On a `1`, the driver advances its selected work head and enters the body. -/
theorem forWorkOnesTM_step_scan_one_internal (driverIdx : Fin n) (body : TM n)
    (cfg : Cfg n (forWorkOnesTM driverIdx body).Q)
    (hstate : cfg.state = .inl .scan)
    (hone : (cfg.work driverIdx).read = Γ.one)
    (hinput : cfg.input.read ≠ Γ.start)
    (hwork : ∀ i, (cfg.work i).read ≠ Γ.start)
    (houtput : cfg.output.read ≠ Γ.start) :
    (forWorkOnesTM driverIdx body).step cfg = some
      { state := .inr body.qstart
        input := cfg.input
        work := fun i =>
          if i = driverIdx then (cfg.work i).move Dir3.right else cfg.work i
        output := cfg.output } := by
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [forWorkOnesTM])]
  simp only [forWorkOnesTM, hstate, hone, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · rw [idleDir, ite_eq_right hinput]
    rfl
  · funext i
    rw [writeAndMove_readBack _ (hwork i)]
    split
    · rfl
    · rw [idleDir, ite_eq_right (hwork i)]
      rfl
  · rw [writeAndMove_readBack _ houtput, idleDir, ite_eq_right houtput]
    rfl

/-- On the zero separator, the driver halts without consuming it. -/
theorem forWorkOnesTM_step_scan_zero_internal (driverIdx : Fin n) (body : TM n)
    (cfg : Cfg n (forWorkOnesTM driverIdx body).Q)
    (hstate : cfg.state = .inl .scan)
    (hzero : (cfg.work driverIdx).read = Γ.zero)
    (hinput : cfg.input.read ≠ Γ.start)
    (hwork : ∀ i, (cfg.work i).read ≠ Γ.start)
    (houtput : cfg.output.read ≠ Γ.start) :
    (forWorkOnesTM driverIdx body).step cfg = some
      { state := .inl .done
        input := cfg.input
        work := cfg.work
        output := cfg.output } := by
  have hstart : (cfg.work driverIdx).read ≠ Γ.start := by rw [hzero]; decide
  have hone : (cfg.work driverIdx).read ≠ Γ.one := by rw [hzero]; decide
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [forWorkOnesTM])]
  simp only [forWorkOnesTM, hstate, hstart, hone, allReadBack, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · rw [idleDir, ite_eq_right hinput]
    rfl
  · funext i
    rw [writeAndMove_readBack _ (hwork i), idleDir, ite_eq_right (hwork i)]
    rfl
  · rw [writeAndMove_readBack _ houtput, idleDir, ite_eq_right houtput]
    rfl

/-- A halted body takes one preserving seam step back to the scanner. -/
theorem forWorkOnesTM_step_body_halt_internal (driverIdx : Fin n) (body : TM n)
    (cfg : Cfg n body.Q) (hhalt : body.halted cfg)
    (hinput : cfg.input.read ≠ Γ.start)
    (hwork : ∀ i, (cfg.work i).read ≠ Γ.start)
    (houtput : cfg.output.read ≠ Γ.start) :
    (forWorkOnesTM driverIdx body).step
      (forWorkOnesBodyWrap driverIdx body cfg) = some
        { state := .inl .scan
          input := cfg.input
          work := cfg.work
          output := cfg.output } := by
  rw [TM.step, ite_eq_right (by simp [forWorkOnesBodyWrap, forWorkOnesTM])]
  simp only [forWorkOnesBodyWrap, forWorkOnesTM, hhalt, allReadBack, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    rw [writeAndMove_readBack _ (hwork i), idleDir, ite_eq_right (hwork i)]
    rfl
  · rw [writeAndMove_readBack _ houtput, idleDir, ite_eq_right houtput]
    rfl

/-- A certified consecutive-one loop has its advertised exact remaining run. -/
theorem ForWorkOnesLoopSpec.reachesIn_internal
    {driverIdx : Fin n} {body : TM n} {bodyTime : ℕ → ℕ} {total : ℕ}
    (spec : ForWorkOnesLoopSpec driverIdx body bodyTime total) :
    ∀ count value, value + count = total →
      (forWorkOnesTM driverIdx body).reachesIn
        (forWorkOnesLoopTime bodyTime value count)
        (spec.scanCfg value) spec.doneCfg := by
  intro count
  induction count with
  | zero =>
      intro value htotal
      have hvalue : value = total := by omega
      subst value
      exact .step spec.stopStep .zero
  | succ count ih =>
      intro value htotal
      have hvalue : value < total := by omega
      have hscan : (forWorkOnesTM driverIdx body).reachesIn 1
          (spec.scanCfg value) (spec.bodyStartCfg value) :=
        .step (spec.scanStep value hvalue) .zero
      have hbody := spec.bodyRun value hvalue
      have hloopback : (forWorkOnesTM driverIdx body).reachesIn 1
          (spec.bodyDoneCfg value) (spec.scanCfg (value + 1)) :=
        .step (spec.loopbackStep value hvalue) .zero
      have htail := ih (value + 1) (by omega)
      have hreach := reachesIn_trans (forWorkOnesTM driverIdx body) hscan
        (reachesIn_trans (forWorkOnesTM driverIdx body) hbody
          (reachesIn_trans (forWorkOnesTM driverIdx body) hloopback htail))
      convert hreach using 1
      simp only [forWorkOnesLoopTime]
      omega

/-- Consecutive-one iteration preserves one-way output when the body does. -/
theorem IsTransducer.forWorkOnesTM_internal {driverIdx : Fin n} {body : TM n}
    (hbody : body.IsTransducer) :
    (forWorkOnesTM driverIdx body).IsTransducer := by
  intro state iHead wHeads oHead
  cases state with
  | inl phase =>
      cases phase with
      | scan =>
          by_cases hstart : wHeads driverIdx = Γ.start
          · cases iHead <;> cases oHead <;>
              simp [forWorkOnesTM, hstart, allReadBack, idleDir]
          · by_cases hone : wHeads driverIdx = Γ.one
            · cases iHead <;> cases oHead <;>
                simp [forWorkOnesTM, hone, allReadBack, idleDir]
            · cases iHead <;> cases oHead <;>
                simp [forWorkOnesTM, hstart, hone, allReadBack, idleDir]
      | done =>
          cases iHead <;> cases oHead <;>
            simp [forWorkOnesTM, allIdle, idleDir]
  | inr state =>
      by_cases hstate : state = body.qhalt
      · cases oHead <;> simp [forWorkOnesTM, hstate, allReadBack, idleDir]
      · simpa [forWorkOnesTM, hstate] using hbody state iHead wHeads oHead

end TM

end Complexity
