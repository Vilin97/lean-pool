/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Space

/-!
# Direct work-symbol branch combinator

This module exposes exact framed execution for a one-step branch on an
arbitrary work-tape symbol. It is the direct controller primitive used to
branch on the readable sparse-entry equality flag.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Exact framed execution through the symbol-equal branch. -/
theorem branchWorkSymbolTM_reachesIn_equal_frame
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
      C.input = c'.input ∧ C.work = c'.work ∧ C.output = c'.output :=
  branchWorkSymbolTM_reachesIn_equal_frame_internal idx symbol onEqual
    onDifferent inp work out hequal hinp hwork hout hreach hhalt

/-- Exact framed execution through the symbol-different branch. -/
theorem branchWorkSymbolTM_reachesIn_different_frame
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
      C.input = c'.input ∧ C.work = c'.work ∧ C.output = c'.output :=
  branchWorkSymbolTM_reachesIn_different_frame_internal idx symbol onEqual
    onDifferent inp work out hdifferent hinp hwork hout hreach hhalt

/-- A direct work-symbol branch is a transducer when both selected branches
are transducers. -/
theorem IsTransducer.branchWorkSymbolTM
    {idx : Fin n} {symbol : Γ} {onEqual onDifferent : TM n}
    (hequal : onEqual.IsTransducer) (hdifferent : onDifferent.IsTransducer) :
    (branchWorkSymbolTM idx symbol onEqual onDifferent).IsTransducer :=
  hequal.branchWorkSymbolTM_internal hdifferent

/-- Coarse all-prefix auxiliary-space envelope for a direct work-symbol
branch. -/
theorem branchWorkSymbolTM_prefix_withinAuxSpace
    (idx : Fin n) (symbol : Γ) (onEqual onDifferent : TM n)
    (branchTime inputLength initialSpace time : ℕ)
    (start current : Cfg n
      (branchWorkSymbolTM idx symbol onEqual onDifferent).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (branchWorkSymbolTM idx symbol onEqual onDifferent).reachesIn
      time start current)
    (htime : time ≤ branchTime + 1) :
    current.WithinAuxSpace inputLength (initialSpace + branchTime + 1) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end TM

end Complexity
