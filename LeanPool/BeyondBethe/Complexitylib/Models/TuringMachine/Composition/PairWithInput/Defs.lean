/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairEmit.Defs

/-!
# Pair a computed value with the original input

This file defines a generic deterministic pipeline for the fanout operation
`x ↦ pair (f x) x`. It redirects the computed value to a work tape, rewinds
that tape and the immutable original input, then emits both components
directly to the real output. Only the first raw-output delimiter is semantic;
later cells may contain arbitrary non-`▷` junk.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Work-tape count of `pairWithInputTM`. One extra tape beyond the redirected
output is kept as a stable phase-composition frame. -/
abbrev pairWithInputTapeCount (nf : ℕ) := compositionTapeCount nf 0

/-- Physical work tape holding the raw output of the function computation. -/
def pairWithInputRawOutputIdx (nf : ℕ) : Fin (pairWithInputTapeCount nf) :=
  compositionRawOutputIdx nf 0

/-- First phase of `pairWithInputTM`: compute with the output redirected to
the raw-output work tape. -/
def pairWithInputFirstTM (tmF : TM nf) : TM (pairWithInputTapeCount nf) :=
  compositionFirstTM tmF 0

/-- Normalize the two read heads, then emit the computed value paired with
the unchanged original input. -/
def pairWithInputTailTM (nf : ℕ) : TM (pairWithInputTapeCount nf) :=
  seqTM (rewindWorkTM (pairWithInputRawOutputIdx nf))
    (seqTM rewindInputTM (pairInputWorkTM (pairWithInputRawOutputIdx nf)))

/-- Executable deterministic fanout combinator computing
`x ↦ pair (f x) x` whenever `tmF` computes `f`. -/
def pairWithInputTM (tmF : TM nf) : TM (pairWithInputTapeCount nf) :=
  seqTM (pairWithInputFirstTM tmF) (pairWithInputTailTM nf)

/-- Coarse time budget for `pairWithInputTM`. It covers the source run, both
rewinds, pair emission, and the three phase transitions. -/
def pairWithInputTime (sourceTime : ℕ → ℕ) (inputLength : ℕ) : ℕ :=
  5 * sourceTime inputLength + inputLength + 12

end TM

end Complexity
