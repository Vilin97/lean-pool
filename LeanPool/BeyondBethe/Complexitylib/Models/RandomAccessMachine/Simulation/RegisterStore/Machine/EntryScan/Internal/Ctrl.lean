/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan.Defs

/-!
# Bounded sparse-entry scan — controller internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

/-- Embed an entry-step configuration in the bounded scan controller. -/
def entryScanBodyWrap (tapes : EntryScanTapes n)
    (cfg : Complexity.Cfg n (entryScanStepTM tapes.entry).Q) :
    Complexity.Cfg n (entryScanTM tapes).Q where
  state := .inr (.inl cfg.state)
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Embed a binary-predecessor configuration in the bounded scan controller. -/
def entryScanPredWrap (tapes : EntryScanTapes n)
    (cfg : Complexity.Cfg n (TM.binaryPredTM tapes.count).Q) :
    Complexity.Cfg n (entryScanTM tapes).Q where
  state := .inr (.inr cfg.state)
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Canonical halted controller configuration with the supplied tapes. -/
def entryScanDoneCfg (tapes : EntryScanTapes n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) :
    Complexity.Cfg n (entryScanTM tapes).Q where
  state := .inl .done
  input := inp
  work := work
  output := out

/-- Canonical loop-test controller configuration with the supplied tapes. -/
def entryScanTestCfg (tapes : EntryScanTapes n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) :
    Complexity.Cfg n (entryScanTM tapes).Q where
  state := .inl .test
  input := inp
  work := work
  output := out

private theorem entryScanTM_body_step
    (tapes : EntryScanTapes n)
    {cfg next : Complexity.Cfg n (entryScanStepTM tapes.entry).Q}
    (hstep : (entryScanStepTM tapes.entry).step cfg = some next) :
    (entryScanTM tapes).step (entryScanBodyWrap tapes cfg) =
      some (entryScanBodyWrap tapes next) := by
  have hne : cfg.state ≠ (entryScanStepTM tapes.entry).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, ite_eq_right (by
    simp [entryScanBodyWrap, entryScanTM])]
  simp only [entryScanBodyWrap, entryScanTM, hne, ↓reduceIte]
  rw [TM.step, ite_eq_right hne] at hstep
  revert hstep
  generalize haction : (entryScanStepTM tapes.entry).δ cfg.state cfg.input.read
    (fun i => (cfg.work i).read) cfg.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem entryScanTM_pred_step
    (tapes : EntryScanTapes n)
    {cfg next : Complexity.Cfg n (TM.binaryPredTM tapes.count).Q}
    (hstep : (TM.binaryPredTM tapes.count).step cfg = some next) :
    (entryScanTM tapes).step (entryScanPredWrap tapes cfg) =
      some (entryScanPredWrap tapes next) := by
  have hne : cfg.state ≠ (TM.binaryPredTM tapes.count).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, ite_eq_right (by
    simp [entryScanPredWrap, entryScanTM])]
  simp only [entryScanPredWrap, entryScanTM, hne, ↓reduceIte]
  rw [TM.step, ite_eq_right hne] at hstep
  revert hstep
  generalize haction : (TM.binaryPredTM tapes.count).δ cfg.state cfg.input.read
    (fun i => (cfg.work i).read) cfg.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

theorem entryScanTM_body_reachesIn_internal
    (tapes : EntryScanTapes n) {time : ℕ}
    {cfg next : Complexity.Cfg n (entryScanStepTM tapes.entry).Q}
    (hreach : (entryScanStepTM tapes.entry).reachesIn time cfg next) :
    (entryScanTM tapes).reachesIn time
      (entryScanBodyWrap tapes cfg) (entryScanBodyWrap tapes next) :=
  TM.reachesIn_map (entryScanBodyWrap tapes)
    (fun _ _ => entryScanTM_body_step tapes) hreach

theorem entryScanTM_pred_reachesIn_internal
    (tapes : EntryScanTapes n) {time : ℕ}
    {cfg next : Complexity.Cfg n (TM.binaryPredTM tapes.count).Q}
    (hreach : (TM.binaryPredTM tapes.count).reachesIn time cfg next) :
    (entryScanTM tapes).reachesIn time
      (entryScanPredWrap tapes cfg) (entryScanPredWrap tapes next) :=
  TM.reachesIn_map (entryScanPredWrap tapes)
    (fun _ _ => entryScanTM_pred_step tapes) hreach

theorem entryScanTM_step_test_zero_internal
    (tapes : EntryScanTapes n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcount : (work tapes.count).read = Γ.blank)
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    (entryScanTM tapes).step
      { state := .inl .test, input := inp, work := work, output := out } =
      some { state := .inl .done, input := inp, work := work, output := out } := by
  rw [TM.step, ite_eq_right (by simp [entryScanTM])]
  simp only [entryScanTM, hcount, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryScanTM_step_test_positive_internal
    (tapes : EntryScanTapes n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcount : (work tapes.count).read ≠ Γ.blank)
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    (entryScanTM tapes).step
      { state := .inl .test, input := inp, work := work, output := out } =
      some (entryScanBodyWrap tapes
        { state := (entryScanStepTM tapes.entry).qstart
          input := inp, work := work, output := out }) := by
  rw [TM.step, ite_eq_right (by simp [entryScanTM])]
  simp only [entryScanTM, hcount, ↓reduceIte, entryScanBodyWrap]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryScanTM_step_body_hit_internal
    (tapes : EntryScanTapes n)
    (cfg : Complexity.Cfg n (entryScanStepTM tapes.entry).Q)
    (hhalt : (entryScanStepTM tapes.entry).halted cfg)
    (hresult : (cfg.work tapes.entry.result).read = Γ.one)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryScanTM tapes).step (entryScanBodyWrap tapes cfg) =
      some (entryScanDoneCfg tapes cfg.input cfg.work cfg.output) := by
  rw [TM.step, ite_eq_right (by simp [entryScanBodyWrap, entryScanTM])]
  simp only [entryScanBodyWrap, entryScanDoneCfg, entryScanTM, hhalt,
    hresult, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryScanTM_step_body_miss_internal
    (tapes : EntryScanTapes n)
    (cfg : Complexity.Cfg n (entryScanStepTM tapes.entry).Q)
    (hhalt : (entryScanStepTM tapes.entry).halted cfg)
    (hresult : (cfg.work tapes.entry.result).read ≠ Γ.one)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryScanTM tapes).step (entryScanBodyWrap tapes cfg) =
      some (entryScanPredWrap tapes
        { state := (TM.binaryPredTM tapes.count).qstart
          input := cfg.input, work := cfg.work, output := cfg.output }) := by
  rw [TM.step, ite_eq_right (by simp [entryScanBodyWrap, entryScanTM])]
  simp only [entryScanBodyWrap, entryScanTM, hhalt, hresult, ↓reduceIte,
    entryScanPredWrap]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryScanTM_step_pred_halt_internal
    (tapes : EntryScanTapes n)
    (cfg : Complexity.Cfg n (TM.binaryPredTM tapes.count).Q)
    (hhalt : (TM.binaryPredTM tapes.count).halted cfg)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryScanTM tapes).step (entryScanPredWrap tapes cfg) =
      some (entryScanTestCfg tapes cfg.input cfg.work cfg.output) := by
  rw [TM.step, ite_eq_right (by simp [entryScanPredWrap, entryScanTM])]
  simp only [entryScanPredWrap, entryScanTestCfg, entryScanTM, hhalt,
    ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

end Machine

end RegisterStore

end RAM

end Complexity
