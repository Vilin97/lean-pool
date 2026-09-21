/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Defs

/-!
# Bounded encoded sparse-store update — controller internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

/-- Embed a match configuration in the update controller. -/
def entryUpdateMatchWrap (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryMatchReadTM tapes.entry).Q) :
    Complexity.Cfg n (entryUpdateTM tapes).Q where
  state := .matching cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Embed a miss-copy configuration in the update controller. -/
def entryUpdateMissWrap (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryMissCopyTM tapes.entry).Q) :
    Complexity.Cfg n (entryUpdateTM tapes).Q where
  state := .miss cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Embed a deletion-cleanup configuration in the update controller. -/
def entryUpdateDeleteWrap (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryMissCleanupTM tapes.entry).Q) :
    Complexity.Cfg n (entryUpdateTM tapes).Q where
  state := .delete cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Embed a replacement configuration in the update controller. -/
def entryUpdateReplaceWrap (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryReplaceCleanupTM tapes.replace).Q) :
    Complexity.Cfg n (entryUpdateTM tapes).Q where
  state := .replace cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Embed a final-append configuration in the update controller. -/
def entryUpdateAppendWrap (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryAppendRestoreTM tapes.replace).Q) :
    Complexity.Cfg n (entryUpdateTM tapes).Q where
  state := .append cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Embed the remaining-count predecessor in the update controller. -/
def entryUpdateRemainingWrap (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (TM.binaryPredTM tapes.remaining).Q) :
    Complexity.Cfg n (entryUpdateTM tapes).Q where
  state := .remaining cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Embed the deletion result-count predecessor in the update controller. -/
def entryUpdateDeleteCountWrap (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (TM.binaryPredTM tapes.resultCount).Q) :
    Complexity.Cfg n (entryUpdateTM tapes).Q where
  state := .deleteCount cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Embed the append result-count successor in the update controller. -/
def entryUpdateAppendCountWrap (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (TM.binarySuccTM tapes.resultCount).Q) :
    Complexity.Cfg n (entryUpdateTM tapes).Q where
  state := .appendCount cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Canonical loop-test controller configuration. -/
def entryUpdateTestCfg (tapes : EntryUpdateTapes n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) :
    Complexity.Cfg n (entryUpdateTM tapes).Q where
  state := .test
  input := inp
  work := work
  output := out

/-- Canonical halted update-controller configuration. -/
def entryUpdateDoneCfg (tapes : EntryUpdateTapes n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) :
    Complexity.Cfg n (entryUpdateTM tapes).Q where
  state := .done
  input := inp
  work := work
  output := out

/-- Work family after the hit-dispatch transition records a match. -/
def entryUpdateMarkFoundWork (tapes : EntryUpdateTapes n)
    (work : Fin n → Tape) : Fin n → Tape :=
  Function.update work tapes.found
    ((work tapes.found).writeAndMove Γ.one
      (TM.idleDir (work tapes.found).read))

private theorem entryUpdateTM_match_step
    (tapes : EntryUpdateTapes n)
    {cfg next : Complexity.Cfg n (entryMatchReadTM tapes.entry).Q}
    (hstep : (entryMatchReadTM tapes.entry).step cfg = some next) :
    (entryUpdateTM tapes).step (entryUpdateMatchWrap tapes cfg) =
      some (entryUpdateMatchWrap tapes next) := by
  have hne : cfg.state ≠ (entryMatchReadTM tapes.entry).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by simp [entryUpdateMatchWrap, entryUpdateTM])]
  simp only [entryUpdateMatchWrap, entryUpdateTM, hne, ↓reduceIte]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : (entryMatchReadTM tapes.entry).δ cfg.state
    cfg.input.read (fun i => (cfg.work i).read) cfg.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem entryUpdateTM_miss_step
    (tapes : EntryUpdateTapes n)
    {cfg next : Complexity.Cfg n (entryMissCopyTM tapes.entry).Q}
    (hstep : (entryMissCopyTM tapes.entry).step cfg = some next) :
    (entryUpdateTM tapes).step (entryUpdateMissWrap tapes cfg) =
      some (entryUpdateMissWrap tapes next) := by
  have hne : cfg.state ≠ (entryMissCopyTM tapes.entry).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by simp [entryUpdateMissWrap, entryUpdateTM])]
  simp only [entryUpdateMissWrap, entryUpdateTM, hne, ↓reduceIte]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : (entryMissCopyTM tapes.entry).δ cfg.state
    cfg.input.read (fun i => (cfg.work i).read) cfg.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem entryUpdateTM_delete_step
    (tapes : EntryUpdateTapes n)
    {cfg next : Complexity.Cfg n (entryMissCleanupTM tapes.entry).Q}
    (hstep : (entryMissCleanupTM tapes.entry).step cfg = some next) :
    (entryUpdateTM tapes).step (entryUpdateDeleteWrap tapes cfg) =
      some (entryUpdateDeleteWrap tapes next) := by
  have hne : cfg.state ≠ (entryMissCleanupTM tapes.entry).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by simp [entryUpdateDeleteWrap, entryUpdateTM])]
  simp only [entryUpdateDeleteWrap, entryUpdateTM, hne, ↓reduceIte]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : (entryMissCleanupTM tapes.entry).δ cfg.state
    cfg.input.read (fun i => (cfg.work i).read) cfg.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem entryUpdateTM_replace_step
    (tapes : EntryUpdateTapes n)
    {cfg next : Complexity.Cfg n (entryReplaceCleanupTM tapes.replace).Q}
    (hstep : (entryReplaceCleanupTM tapes.replace).step cfg = some next) :
    (entryUpdateTM tapes).step (entryUpdateReplaceWrap tapes cfg) =
      some (entryUpdateReplaceWrap tapes next) := by
  have hne : cfg.state ≠ (entryReplaceCleanupTM tapes.replace).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by simp [entryUpdateReplaceWrap, entryUpdateTM])]
  simp only [entryUpdateReplaceWrap, entryUpdateTM, hne, ↓reduceIte]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : (entryReplaceCleanupTM tapes.replace).δ cfg.state
    cfg.input.read (fun i => (cfg.work i).read) cfg.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem entryUpdateTM_append_step
    (tapes : EntryUpdateTapes n)
    {cfg next : Complexity.Cfg n (entryAppendRestoreTM tapes.replace).Q}
    (hstep : (entryAppendRestoreTM tapes.replace).step cfg = some next) :
    (entryUpdateTM tapes).step (entryUpdateAppendWrap tapes cfg) =
      some (entryUpdateAppendWrap tapes next) := by
  have hne : cfg.state ≠ (entryAppendRestoreTM tapes.replace).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by simp [entryUpdateAppendWrap, entryUpdateTM])]
  simp only [entryUpdateAppendWrap, entryUpdateTM, hne, ↓reduceIte]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : (entryAppendRestoreTM tapes.replace).δ cfg.state
    cfg.input.read (fun i => (cfg.work i).read) cfg.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem entryUpdateTM_remaining_step
    (tapes : EntryUpdateTapes n)
    {cfg next : Complexity.Cfg n (TM.binaryPredTM tapes.remaining).Q}
    (hstep : (TM.binaryPredTM tapes.remaining).step cfg = some next) :
    (entryUpdateTM tapes).step (entryUpdateRemainingWrap tapes cfg) =
      some (entryUpdateRemainingWrap tapes next) := by
  have hne : cfg.state ≠ (TM.binaryPredTM tapes.remaining).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by simp [entryUpdateRemainingWrap, entryUpdateTM])]
  simp only [entryUpdateRemainingWrap, entryUpdateTM, hne, ↓reduceIte]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : (TM.binaryPredTM tapes.remaining).δ cfg.state
    cfg.input.read (fun i => (cfg.work i).read) cfg.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem entryUpdateTM_deleteCount_step
    (tapes : EntryUpdateTapes n)
    {cfg next : Complexity.Cfg n (TM.binaryPredTM tapes.resultCount).Q}
    (hstep : (TM.binaryPredTM tapes.resultCount).step cfg = some next) :
    (entryUpdateTM tapes).step (entryUpdateDeleteCountWrap tapes cfg) =
      some (entryUpdateDeleteCountWrap tapes next) := by
  have hne : cfg.state ≠ (TM.binaryPredTM tapes.resultCount).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by simp [entryUpdateDeleteCountWrap, entryUpdateTM])]
  simp only [entryUpdateDeleteCountWrap, entryUpdateTM, hne, ↓reduceIte]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : (TM.binaryPredTM tapes.resultCount).δ cfg.state
    cfg.input.read (fun i => (cfg.work i).read) cfg.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem entryUpdateTM_appendCount_step
    (tapes : EntryUpdateTapes n)
    {cfg next : Complexity.Cfg n (TM.binarySuccTM tapes.resultCount).Q}
    (hstep : (TM.binarySuccTM tapes.resultCount).step cfg = some next) :
    (entryUpdateTM tapes).step (entryUpdateAppendCountWrap tapes cfg) =
      some (entryUpdateAppendCountWrap tapes next) := by
  have hne : cfg.state ≠ (TM.binarySuccTM tapes.resultCount).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by simp [entryUpdateAppendCountWrap, entryUpdateTM])]
  simp only [entryUpdateAppendCountWrap, entryUpdateTM, hne, ↓reduceIte]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : (TM.binarySuccTM tapes.resultCount).δ cfg.state
    cfg.input.read (fun i => (cfg.work i).read) cfg.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

theorem entryUpdateTM_match_reachesIn_internal
    (tapes : EntryUpdateTapes n) {time : ℕ}
    {cfg next : Complexity.Cfg n (entryMatchReadTM tapes.entry).Q}
    (hreach : (entryMatchReadTM tapes.entry).reachesIn time cfg next) :
    (entryUpdateTM tapes).reachesIn time
      (entryUpdateMatchWrap tapes cfg) (entryUpdateMatchWrap tapes next) :=
  TM.reachesIn_map (entryUpdateMatchWrap tapes)
    (fun _ _ => entryUpdateTM_match_step tapes) hreach

theorem entryUpdateTM_miss_reachesIn_internal
    (tapes : EntryUpdateTapes n) {time : ℕ}
    {cfg next : Complexity.Cfg n (entryMissCopyTM tapes.entry).Q}
    (hreach : (entryMissCopyTM tapes.entry).reachesIn time cfg next) :
    (entryUpdateTM tapes).reachesIn time
      (entryUpdateMissWrap tapes cfg) (entryUpdateMissWrap tapes next) :=
  TM.reachesIn_map (entryUpdateMissWrap tapes)
    (fun _ _ => entryUpdateTM_miss_step tapes) hreach

theorem entryUpdateTM_delete_reachesIn_internal
    (tapes : EntryUpdateTapes n) {time : ℕ}
    {cfg next : Complexity.Cfg n (entryMissCleanupTM tapes.entry).Q}
    (hreach : (entryMissCleanupTM tapes.entry).reachesIn time cfg next) :
    (entryUpdateTM tapes).reachesIn time
      (entryUpdateDeleteWrap tapes cfg) (entryUpdateDeleteWrap tapes next) :=
  TM.reachesIn_map (entryUpdateDeleteWrap tapes)
    (fun _ _ => entryUpdateTM_delete_step tapes) hreach

theorem entryUpdateTM_replace_reachesIn_internal
    (tapes : EntryUpdateTapes n) {time : ℕ}
    {cfg next : Complexity.Cfg n (entryReplaceCleanupTM tapes.replace).Q}
    (hreach : (entryReplaceCleanupTM tapes.replace).reachesIn time cfg next) :
    (entryUpdateTM tapes).reachesIn time
      (entryUpdateReplaceWrap tapes cfg) (entryUpdateReplaceWrap tapes next) :=
  TM.reachesIn_map (entryUpdateReplaceWrap tapes)
    (fun _ _ => entryUpdateTM_replace_step tapes) hreach

theorem entryUpdateTM_append_reachesIn_internal
    (tapes : EntryUpdateTapes n) {time : ℕ}
    {cfg next : Complexity.Cfg n (entryAppendRestoreTM tapes.replace).Q}
    (hreach : (entryAppendRestoreTM tapes.replace).reachesIn time cfg next) :
    (entryUpdateTM tapes).reachesIn time
      (entryUpdateAppendWrap tapes cfg) (entryUpdateAppendWrap tapes next) :=
  TM.reachesIn_map (entryUpdateAppendWrap tapes)
    (fun _ _ => entryUpdateTM_append_step tapes) hreach

theorem entryUpdateTM_remaining_reachesIn_internal
    (tapes : EntryUpdateTapes n) {time : ℕ}
    {cfg next : Complexity.Cfg n (TM.binaryPredTM tapes.remaining).Q}
    (hreach : (TM.binaryPredTM tapes.remaining).reachesIn time cfg next) :
    (entryUpdateTM tapes).reachesIn time
      (entryUpdateRemainingWrap tapes cfg) (entryUpdateRemainingWrap tapes next) :=
  TM.reachesIn_map (entryUpdateRemainingWrap tapes)
    (fun _ _ => entryUpdateTM_remaining_step tapes) hreach

theorem entryUpdateTM_deleteCount_reachesIn_internal
    (tapes : EntryUpdateTapes n) {time : ℕ}
    {cfg next : Complexity.Cfg n (TM.binaryPredTM tapes.resultCount).Q}
    (hreach : (TM.binaryPredTM tapes.resultCount).reachesIn time cfg next) :
    (entryUpdateTM tapes).reachesIn time
      (entryUpdateDeleteCountWrap tapes cfg)
      (entryUpdateDeleteCountWrap tapes next) :=
  TM.reachesIn_map (entryUpdateDeleteCountWrap tapes)
    (fun _ _ => entryUpdateTM_deleteCount_step tapes) hreach

theorem entryUpdateTM_appendCount_reachesIn_internal
    (tapes : EntryUpdateTapes n) {time : ℕ}
    {cfg next : Complexity.Cfg n (TM.binarySuccTM tapes.resultCount).Q}
    (hreach : (TM.binarySuccTM tapes.resultCount).reachesIn time cfg next) :
    (entryUpdateTM tapes).reachesIn time
      (entryUpdateAppendCountWrap tapes cfg)
      (entryUpdateAppendCountWrap tapes next) :=
  TM.reachesIn_map (entryUpdateAppendCountWrap tapes)
    (fun _ _ => entryUpdateTM_appendCount_step tapes) hreach

theorem entryUpdateTM_step_test_continue_internal
    (tapes : EntryUpdateTapes n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hremaining : (work tapes.remaining).read ≠ Γ.blank)
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    (entryUpdateTM tapes).step (entryUpdateTestCfg tapes inp work out) =
      some (entryUpdateMatchWrap tapes
        { state := (entryMatchReadTM tapes.entry).qstart
          input := inp, work := work, output := out }) := by
  rw [TM.step, if_neg (by simp [entryUpdateTestCfg, entryUpdateTM])]
  simp only [entryUpdateTestCfg, entryUpdateTM, hremaining, ↓reduceIte,
    entryUpdateMatchWrap]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_test_found_internal
    (tapes : EntryUpdateTapes n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hremaining : (work tapes.remaining).read = Γ.blank)
    (hfound : (work tapes.found).read = Γ.one)
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    (entryUpdateTM tapes).step (entryUpdateTestCfg tapes inp work out) =
      some (entryUpdateDoneCfg tapes inp work out) := by
  rw [TM.step, if_neg (by simp [entryUpdateTestCfg, entryUpdateTM])]
  simp only [entryUpdateTestCfg, entryUpdateDoneCfg, entryUpdateTM,
    hremaining, hfound, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_test_zero_internal
    (tapes : EntryUpdateTapes n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hremaining : (work tapes.remaining).read = Γ.blank)
    (hfound : (work tapes.found).read ≠ Γ.one)
    (hreplacement : (work tapes.replacement).read = Γ.blank)
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    (entryUpdateTM tapes).step (entryUpdateTestCfg tapes inp work out) =
      some (entryUpdateDoneCfg tapes inp work out) := by
  rw [TM.step, if_neg (by simp [entryUpdateTestCfg, entryUpdateTM])]
  simp only [entryUpdateTestCfg, entryUpdateDoneCfg, entryUpdateTM,
    hremaining, hfound, hreplacement, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_test_append_internal
    (tapes : EntryUpdateTapes n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hremaining : (work tapes.remaining).read = Γ.blank)
    (hfound : (work tapes.found).read ≠ Γ.one)
    (hreplacement : (work tapes.replacement).read ≠ Γ.blank)
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    (entryUpdateTM tapes).step (entryUpdateTestCfg tapes inp work out) =
      some (entryUpdateAppendWrap tapes
        { state := (entryAppendRestoreTM tapes.replace).qstart
          input := inp, work := work, output := out }) := by
  rw [TM.step, if_neg (by simp [entryUpdateTestCfg, entryUpdateTM])]
  simp only [entryUpdateTestCfg, entryUpdateTM, hremaining, hfound,
    hreplacement, ↓reduceIte, entryUpdateAppendWrap]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

private theorem entryUpdateMarkFoundWork_apply_eq
    (tapes : EntryUpdateTapes n) (work : Fin n → Tape) :
    entryUpdateMarkFoundWork tapes work tapes.found =
      (work tapes.found).writeAndMove Γ.one
        (TM.idleDir (work tapes.found).read) := by
  simp [entryUpdateMarkFoundWork]

private theorem entryUpdateMarkFoundWork_apply_ne
    (tapes : EntryUpdateTapes n) (work : Fin n → Tape)
    (i : Fin n) (hi : i ≠ tapes.found) :
    entryUpdateMarkFoundWork tapes work i = work i := by
  simp [entryUpdateMarkFoundWork, Function.update_of_ne hi]

theorem entryUpdateTM_step_match_delete_internal
    (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryMatchReadTM tapes.entry).Q)
    (hhalt : (entryMatchReadTM tapes.entry).halted cfg)
    (hresult : (cfg.work tapes.entry.result).read = Γ.one)
    (hreplacement : (cfg.work tapes.replacement).read = Γ.blank)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryUpdateTM tapes).step (entryUpdateMatchWrap tapes cfg) =
      some (entryUpdateDeleteWrap tapes
        { state := (entryMissCleanupTM tapes.entry).qstart
          input := cfg.input
          work := entryUpdateMarkFoundWork tapes cfg.work
          output := cfg.output }) := by
  rw [TM.step, if_neg (by simp [entryUpdateMatchWrap, entryUpdateTM])]
  simp only [entryUpdateMatchWrap, entryUpdateDeleteWrap, entryUpdateTM,
    hhalt, hresult, hreplacement, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    change (cfg.work i).writeAndMove
        (if i = tapes.found then Γw.one
          else TM.readBackWrite (cfg.work i).read).toΓ
        (TM.idleDir (cfg.work i).read) =
      entryUpdateMarkFoundWork tapes cfg.work i
    by_cases hi : i = tapes.found
    · subst i
      simp [entryUpdateMarkFoundWork]
    · simp only [hi, if_false,
        entryUpdateMarkFoundWork_apply_ne tapes cfg.work i hi]
      exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_match_replace_internal
    (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryMatchReadTM tapes.entry).Q)
    (hhalt : (entryMatchReadTM tapes.entry).halted cfg)
    (hresult : (cfg.work tapes.entry.result).read = Γ.one)
    (hreplacement : (cfg.work tapes.replacement).read ≠ Γ.blank)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryUpdateTM tapes).step (entryUpdateMatchWrap tapes cfg) =
      some (entryUpdateReplaceWrap tapes
        { state := (entryReplaceCleanupTM tapes.replace).qstart
          input := cfg.input
          work := entryUpdateMarkFoundWork tapes cfg.work
          output := cfg.output }) := by
  rw [TM.step, if_neg (by simp [entryUpdateMatchWrap, entryUpdateTM])]
  simp only [entryUpdateMatchWrap, entryUpdateReplaceWrap, entryUpdateTM,
    hhalt, hresult, hreplacement, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    change (cfg.work i).writeAndMove
        (if i = tapes.found then Γw.one
          else TM.readBackWrite (cfg.work i).read).toΓ
        (TM.idleDir (cfg.work i).read) =
      entryUpdateMarkFoundWork tapes cfg.work i
    by_cases hi : i = tapes.found
    · subst i
      simp [entryUpdateMarkFoundWork]
    · simp only [hi, if_false,
        entryUpdateMarkFoundWork_apply_ne tapes cfg.work i hi]
      exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_match_miss_internal
    (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryMatchReadTM tapes.entry).Q)
    (hhalt : (entryMatchReadTM tapes.entry).halted cfg)
    (hresult : (cfg.work tapes.entry.result).read ≠ Γ.one)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryUpdateTM tapes).step (entryUpdateMatchWrap tapes cfg) =
      some (entryUpdateMissWrap tapes
        { state := (entryMissCopyTM tapes.entry).qstart
          input := cfg.input, work := cfg.work, output := cfg.output }) := by
  rw [TM.step, if_neg (by simp [entryUpdateMatchWrap, entryUpdateTM])]
  simp only [entryUpdateMatchWrap, entryUpdateMissWrap, entryUpdateTM,
    hhalt, hresult, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_miss_halt_internal
    (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryMissCopyTM tapes.entry).Q)
    (hhalt : (entryMissCopyTM tapes.entry).halted cfg)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryUpdateTM tapes).step (entryUpdateMissWrap tapes cfg) =
      some (entryUpdateRemainingWrap tapes
        { state := (TM.binaryPredTM tapes.remaining).qstart
          input := cfg.input, work := cfg.work, output := cfg.output }) := by
  rw [TM.step, if_neg (by simp [entryUpdateMissWrap, entryUpdateTM])]
  simp only [entryUpdateMissWrap, entryUpdateRemainingWrap, entryUpdateTM,
    hhalt, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_delete_halt_internal
    (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryMissCleanupTM tapes.entry).Q)
    (hhalt : (entryMissCleanupTM tapes.entry).halted cfg)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryUpdateTM tapes).step (entryUpdateDeleteWrap tapes cfg) =
      some (entryUpdateDeleteCountWrap tapes
        { state := (TM.binaryPredTM tapes.resultCount).qstart
          input := cfg.input, work := cfg.work, output := cfg.output }) := by
  rw [TM.step, if_neg (by simp [entryUpdateDeleteWrap, entryUpdateTM])]
  simp only [entryUpdateDeleteWrap, entryUpdateDeleteCountWrap,
    entryUpdateTM, hhalt, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_replace_halt_internal
    (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryReplaceCleanupTM tapes.replace).Q)
    (hhalt : (entryReplaceCleanupTM tapes.replace).halted cfg)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryUpdateTM tapes).step (entryUpdateReplaceWrap tapes cfg) =
      some (entryUpdateRemainingWrap tapes
        { state := (TM.binaryPredTM tapes.remaining).qstart
          input := cfg.input, work := cfg.work, output := cfg.output }) := by
  rw [TM.step, if_neg (by simp [entryUpdateReplaceWrap, entryUpdateTM])]
  simp only [entryUpdateReplaceWrap, entryUpdateRemainingWrap, entryUpdateTM,
    hhalt, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_append_halt_internal
    (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (entryAppendRestoreTM tapes.replace).Q)
    (hhalt : (entryAppendRestoreTM tapes.replace).halted cfg)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryUpdateTM tapes).step (entryUpdateAppendWrap tapes cfg) =
      some (entryUpdateAppendCountWrap tapes
        { state := (TM.binarySuccTM tapes.resultCount).qstart
          input := cfg.input, work := cfg.work, output := cfg.output }) := by
  rw [TM.step, if_neg (by simp [entryUpdateAppendWrap, entryUpdateTM])]
  simp only [entryUpdateAppendWrap, entryUpdateAppendCountWrap, entryUpdateTM,
    hhalt, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_remaining_halt_internal
    (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (TM.binaryPredTM tapes.remaining).Q)
    (hhalt : (TM.binaryPredTM tapes.remaining).halted cfg)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryUpdateTM tapes).step (entryUpdateRemainingWrap tapes cfg) =
      some (entryUpdateTestCfg tapes cfg.input cfg.work cfg.output) := by
  rw [TM.step, if_neg (by simp [entryUpdateRemainingWrap, entryUpdateTM])]
  simp only [entryUpdateRemainingWrap, entryUpdateTestCfg, entryUpdateTM,
    hhalt, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_deleteCount_halt_internal
    (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (TM.binaryPredTM tapes.resultCount).Q)
    (hhalt : (TM.binaryPredTM tapes.resultCount).halted cfg)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryUpdateTM tapes).step (entryUpdateDeleteCountWrap tapes cfg) =
      some (entryUpdateRemainingWrap tapes
        { state := (TM.binaryPredTM tapes.remaining).qstart
          input := cfg.input, work := cfg.work, output := cfg.output }) := by
  rw [TM.step, if_neg (by simp [entryUpdateDeleteCountWrap, entryUpdateTM])]
  simp only [entryUpdateDeleteCountWrap, entryUpdateRemainingWrap,
    entryUpdateTM, hhalt, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

theorem entryUpdateTM_step_appendCount_halt_internal
    (tapes : EntryUpdateTapes n)
    (cfg : Complexity.Cfg n (TM.binarySuccTM tapes.resultCount).Q)
    (hhalt : (TM.binarySuccTM tapes.resultCount).halted cfg)
    (hinput : TM.Parked cfg.input) (hwork : ∀ i, TM.Parked (cfg.work i))
    (houtput : TM.Parked cfg.output) :
    (entryUpdateTM tapes).step (entryUpdateAppendCountWrap tapes cfg) =
      some (entryUpdateDoneCfg tapes cfg.input cfg.work cfg.output) := by
  rw [TM.step, if_neg (by simp [entryUpdateAppendCountWrap, entryUpdateTM])]
  simp only [entryUpdateAppendCountWrap, entryUpdateDoneCfg, entryUpdateTM,
    hhalt, ↓reduceIte]
  refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
  · exact hinput.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact houtput.writeAndMove_readBack_idle

end Machine

end RegisterStore

end RAM

end Complexity
