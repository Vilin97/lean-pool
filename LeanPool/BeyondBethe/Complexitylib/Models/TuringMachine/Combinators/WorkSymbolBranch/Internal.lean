/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch.Defs

/-!
# Direct work-symbol branch combinator — proof internals
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Embed an equal-branch configuration in the direct-symbol controller. -/
def workSymbolEqualWrap (idx : Fin n) (symbol : Γ)
    (onEqual onDifferent : TM n) (c : Cfg n onEqual.Q) :
    Cfg n (branchWorkSymbolTM idx symbol onEqual onDifferent).Q where
  state := workBranchBlankState onEqual onDifferent c.state
  input := c.input
  work := c.work
  output := c.output

/-- Embed a different-branch configuration in the direct-symbol controller. -/
def workSymbolDifferentWrap (idx : Fin n) (symbol : Γ)
    (onEqual onDifferent : TM n) (c : Cfg n onDifferent.Q) :
    Cfg n (branchWorkSymbolTM idx symbol onEqual onDifferent).Q where
  state := workBranchNonblankState onEqual onDifferent c.state
  input := c.input
  work := c.work
  output := c.output

private theorem workSymbolEqualWrap_halted_iff
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    (c : Cfg n onEqual.Q) :
    (branchWorkSymbolTM idx symbol onEqual onDifferent).halted
        (workSymbolEqualWrap idx symbol onEqual onDifferent c) ↔
      onEqual.halted c := by
  change (workSymbolEqualWrap idx symbol onEqual onDifferent c).state =
      (branchWorkSymbolTM idx symbol onEqual onDifferent).qhalt ↔
    c.state = onEqual.qhalt
  by_cases hhalt : c.state = onEqual.qhalt <;>
    simp [workSymbolEqualWrap, workBranchBlankState, branchWorkSymbolTM,
      hhalt]

private theorem workSymbolDifferentWrap_halted_iff
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    (c : Cfg n onDifferent.Q) :
    (branchWorkSymbolTM idx symbol onEqual onDifferent).halted
        (workSymbolDifferentWrap idx symbol onEqual onDifferent c) ↔
      onDifferent.halted c := by
  change (workSymbolDifferentWrap idx symbol onEqual onDifferent c).state =
      (branchWorkSymbolTM idx symbol onEqual onDifferent).qhalt ↔
    c.state = onDifferent.qhalt
  by_cases hhalt : c.state = onDifferent.qhalt <;>
    simp [workSymbolDifferentWrap, workBranchNonblankState,
      branchWorkSymbolTM, hhalt]

private theorem branchWorkSymbolTM_equal_step
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    {c c' : Cfg n onEqual.Q} (hstep : onEqual.step c = some c') :
    (branchWorkSymbolTM idx symbol onEqual onDifferent).step
        (workSymbolEqualWrap idx symbol onEqual onDifferent c) =
      some (workSymbolEqualWrap idx symbol onEqual onDifferent c') := by
  have hne : c.state ≠ onEqual.qhalt := state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by
    simp [workSymbolEqualWrap, workBranchBlankState, branchWorkSymbolTM,
      hne])]
  simp only [workSymbolEqualWrap, workBranchBlankState, hne, ↓reduceIte,
    branchWorkSymbolTM]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : onEqual.δ c.state c.input.read
    (fun i => (c.work i).read) c.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem branchWorkSymbolTM_different_step
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    {c c' : Cfg n onDifferent.Q} (hstep : onDifferent.step c = some c') :
    (branchWorkSymbolTM idx symbol onEqual onDifferent).step
        (workSymbolDifferentWrap idx symbol onEqual onDifferent c) =
      some (workSymbolDifferentWrap idx symbol onEqual onDifferent c') := by
  have hne : c.state ≠ onDifferent.qhalt := state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by
    simp [workSymbolDifferentWrap, workBranchNonblankState,
      branchWorkSymbolTM, hne])]
  simp only [workSymbolDifferentWrap, workBranchNonblankState, hne,
    ↓reduceIte, branchWorkSymbolTM]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : onDifferent.δ c.state c.input.read
    (fun i => (c.work i).read) c.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem branchWorkSymbolTM_equal_reachesIn
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    {t : ℕ} {c c' : Cfg n onEqual.Q} (hreach : onEqual.reachesIn t c c') :
    (branchWorkSymbolTM idx symbol onEqual onDifferent).reachesIn t
      (workSymbolEqualWrap idx symbol onEqual onDifferent c)
      (workSymbolEqualWrap idx symbol onEqual onDifferent c') :=
  reachesIn_map (workSymbolEqualWrap idx symbol onEqual onDifferent)
    (fun _ _ => branchWorkSymbolTM_equal_step idx symbol onEqual onDifferent)
    hreach

private theorem branchWorkSymbolTM_different_reachesIn
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    {t : ℕ} {c c' : Cfg n onDifferent.Q}
    (hreach : onDifferent.reachesIn t c c') :
    (branchWorkSymbolTM idx symbol onEqual onDifferent).reachesIn t
      (workSymbolDifferentWrap idx symbol onEqual onDifferent c)
      (workSymbolDifferentWrap idx symbol onEqual onDifferent c') :=
  reachesIn_map (workSymbolDifferentWrap idx symbol onEqual onDifferent)
    (fun _ _ => branchWorkSymbolTM_different_step idx symbol onEqual onDifferent)
    hreach

private theorem branchWorkSymbolTM_dispatch_equal
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hequal : (work idx).read = symbol)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) :
    (branchWorkSymbolTM idx symbol onEqual onDifferent).step
        { state := (branchWorkSymbolTM idx symbol onEqual onDifferent).qstart
          input := inp
          work := work
          output := out } =
      some (workSymbolEqualWrap idx symbol onEqual onDifferent
        { state := onEqual.qstart, input := inp, work := work, output := out }) := by
  rw [TM.step, if_neg (by simp [branchWorkSymbolTM])]
  simp only [branchWorkSymbolTM, hequal, allReadBack, ↓reduceIte,
    workSymbolEqualWrap]
  refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  · exact transitionInput_eq_self hinp
  · funext i
    exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self hout

private theorem branchWorkSymbolTM_dispatch_different
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hdifferent : (work idx).read ≠ symbol)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) :
    (branchWorkSymbolTM idx symbol onEqual onDifferent).step
        { state := (branchWorkSymbolTM idx symbol onEqual onDifferent).qstart
          input := inp
          work := work
          output := out } =
      some (workSymbolDifferentWrap idx symbol onEqual onDifferent
        { state := onDifferent.qstart, input := inp, work := work,
          output := out }) := by
  rw [TM.step, if_neg (by simp [branchWorkSymbolTM])]
  simp only [branchWorkSymbolTM, hdifferent, allReadBack, ↓reduceIte,
    workSymbolDifferentWrap]
  refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  · exact transitionInput_eq_self hinp
  · funext i
    exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self hout

theorem branchWorkSymbolTM_reachesIn_equal_frame_internal
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {t : ℕ} {c' : Cfg n onEqual.Q}
    (hequal : (work idx).read = symbol)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start)
    (hreach : onEqual.reachesIn t
      { state := onEqual.qstart, input := inp, work := work, output := out } c')
    (hhalt : onEqual.halted c') :
    ∃ C,
      (branchWorkSymbolTM idx symbol onEqual onDifferent).reachesIn (t + 1)
        { state := (branchWorkSymbolTM idx symbol onEqual onDifferent).qstart
          input := inp
          work := work
          output := out } C ∧
      (branchWorkSymbolTM idx symbol onEqual onDifferent).halted C ∧
      C.input = c'.input ∧ C.work = c'.work ∧ C.output = c'.output := by
  let C := workSymbolEqualWrap idx symbol onEqual onDifferent c'
  refine ⟨C, .step
    (branchWorkSymbolTM_dispatch_equal idx symbol onEqual onDifferent
      inp work out hequal hinp hwork hout)
    (branchWorkSymbolTM_equal_reachesIn idx symbol onEqual onDifferent hreach),
    ?_, rfl, rfl, rfl⟩
  exact (workSymbolEqualWrap_halted_iff idx symbol onEqual onDifferent c').2
    hhalt

theorem branchWorkSymbolTM_reachesIn_different_frame_internal
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {t : ℕ} {c' : Cfg n onDifferent.Q}
    (hdifferent : (work idx).read ≠ symbol)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start)
    (hreach : onDifferent.reachesIn t
      { state := onDifferent.qstart, input := inp, work := work, output := out }
      c')
    (hhalt : onDifferent.halted c') :
    ∃ C,
      (branchWorkSymbolTM idx symbol onEqual onDifferent).reachesIn (t + 1)
        { state := (branchWorkSymbolTM idx symbol onEqual onDifferent).qstart
          input := inp
          work := work
          output := out } C ∧
      (branchWorkSymbolTM idx symbol onEqual onDifferent).halted C ∧
      C.input = c'.input ∧ C.work = c'.work ∧ C.output = c'.output := by
  let C := workSymbolDifferentWrap idx symbol onEqual onDifferent c'
  refine ⟨C, .step
    (branchWorkSymbolTM_dispatch_different idx symbol onEqual onDifferent
      inp work out hdifferent hinp hwork hout)
    (branchWorkSymbolTM_different_reachesIn idx symbol onEqual onDifferent
      hreach), ?_, rfl, rfl, rfl⟩
  exact (workSymbolDifferentWrap_halted_iff idx symbol onEqual onDifferent
    c').2 hhalt

theorem IsTransducer.branchWorkSymbolTM_internal
    {idx : Fin n} {symbol : Γ} {onEqual onDifferent : TM n}
    (hequal : onEqual.IsTransducer) (hdifferent : onDifferent.IsTransducer) :
    (branchWorkSymbolTM idx symbol onEqual onDifferent).IsTransducer := by
  intro state iHead wHeads oHead
  cases state with
  | inl phase =>
      cases phase with
      | dispatch =>
          simp only [branchWorkSymbolTM]
          split <;> cases oHead <;> simp [allReadBack, idleDir]
      | done => cases oHead <;> simp [branchWorkSymbolTM, allIdle, idleDir]
  | inr branchState =>
      cases branchState with
      | inl q =>
          simp only [branchWorkSymbolTM]
          split
          · cases oHead <;> simp [allReadBack, idleDir]
          · exact hequal q iHead wHeads oHead
      | inr q =>
          simp only [branchWorkSymbolTM]
          split
          · cases oHead <;> simp [allReadBack, idleDir]
          · exact hdifferent q iHead wHeads oHead

end TM

end Complexity
