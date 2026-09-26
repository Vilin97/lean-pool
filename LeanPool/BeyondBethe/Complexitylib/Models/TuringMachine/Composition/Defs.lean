/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.RetargetCompute.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Lift
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Placement.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines

/-!
# Sequential composition after function computation

This file fixes the tape layout and executable phase pipeline used to feed one
deterministic function computation into a second machine. Proofs of correctness
and time bounds live in the internal and public theorem layers.

For a function-computing `tmF : TM nf` and a second machine `tmG : TM ng`, the
composite has
`nf + 1 + (ng + 1)` work tapes:

- `0 .. nf - 1`: work tapes of `tmF`
- `nf`: raw redirected output of `tmF`
- `nf + 1 .. nf + ng`: work tapes of `tmG`
- `nf + ng + 1`: canonical virtual input of `tmG`

The raw output is rewound and copied to the fresh virtual-input tape before
`tmG` resumes after its compulsory first transition off the left-end markers.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {nf ng : ℕ}

/-- Work-tape count of the sequential composition machine. -/
abbrev compositionTapeCount (nf ng : ℕ) := 0 + (nf + 1) + (ng + 1)

/-- Physical work tape holding the raw redirected output of the first machine. -/
def compositionRawOutputIdx (nf ng : ℕ) : Fin (compositionTapeCount nf ng) :=
  ⟨nf, by simp [compositionTapeCount]; omega⟩

@[simp] theorem compositionRawOutputIdx_val (nf ng : ℕ) :
    (compositionRawOutputIdx nf ng).val = nf := rfl

/-- Physical work tape holding the canonical virtual input of the second machine. -/
def compositionVirtualInputIdx (nf ng : ℕ) : Fin (compositionTapeCount nf ng) :=
  ⟨nf + 1 + ng, by simp [compositionTapeCount]⟩

@[simp] theorem compositionVirtualInputIdx_val (nf ng : ℕ) :
    (compositionVirtualInputIdx nf ng).val = nf + 1 + ng := rfl

/-- The two pipeline tapes occupy distinct physical coordinates. -/
theorem compositionRawOutputIdx_ne_virtualInputIdx (nf ng : ℕ) :
    compositionRawOutputIdx nf ng ≠ compositionVirtualInputIdx nf ng := by
  intro h
  have := congrArg Fin.val h
  simp only [compositionRawOutputIdx_val, compositionVirtualInputIdx_val] at this
  omega

/-- The raw-output coordinate is the placed last work tape of
`tmF.retargetOutput`. -/
theorem compositionRawOutputIdx_eq_firstPlacedLast (nf ng : ℕ) :
    compositionRawOutputIdx nf ng =
      placeWorkIdx 0 (ng + 1) (Fin.last nf) := by
  apply Fin.ext
  simp [compositionRawOutputIdx, placeWorkIdx]

/-- The virtual-input coordinate is the placed last work tape of
`retargetInputStarted tmG`. -/
theorem compositionVirtualInputIdx_eq_secondPlacedLast (nf ng : ℕ) :
    compositionVirtualInputIdx nf ng =
      placeWorkIdx (0 + (nf + 1)) 0 (Fin.last ng) := by
  apply Fin.ext
  simp [compositionVirtualInputIdx, placeWorkIdx]

/-- Physical coordinate of work tape `i` of the first computation. -/
def compositionPrefixIdx (nf ng : ℕ) (i : Fin nf) :
    Fin (compositionTapeCount nf ng) :=
  ⟨i.val, by simp [compositionTapeCount]; omega⟩

@[simp] theorem compositionPrefixIdx_val (nf ng : ℕ) (i : Fin nf) :
    (compositionPrefixIdx nf ng i).val = i.val := rfl

/-- Physical coordinate of source work tape `j` of the second computation. -/
def compositionSecondWorkIdx (nf ng : ℕ) (j : Fin ng) :
    Fin (compositionTapeCount nf ng) :=
  placeWorkIdx (0 + (nf + 1)) 0 (Fin.castSucc j)

@[simp] theorem compositionSecondWorkIdx_val (nf ng : ℕ) (j : Fin ng) :
    (compositionSecondWorkIdx nf ng j).val = nf + 1 + j.val := by
  simp [compositionSecondWorkIdx, placeWorkIdx]

/-- The first phase redirects `tmF`'s output into the raw-output tape and parks
the work-tape suffix reserved for the second computation. -/
def compositionFirstTM (tmF : TM nf) (ng : ℕ) : TM (compositionTapeCount nf ng) :=
  placeWorkTM 0 (ng + 1) tmF.retargetOutput

/-- The last phase places the already-started virtual-input wrapper for `tmG`
after the first computation's work and raw-output tapes. -/
def compositionSecondTM (nf : ℕ) (tmG : TM ng) : TM (compositionTapeCount nf ng) :=
  placeWorkTM (0 + (nf + 1)) 0 (retargetInputStarted tmG)

/-- Pipeline after the first computation: rewind its raw output, copy it onto
a clean virtual-input tape, rewind that tape, and run the second computation. -/
def compositionTailTM (nf ng : ℕ) (tmG : TM ng) : TM (compositionTapeCount nf ng) :=
  seqTM (rewindWorkTM (compositionRawOutputIdx nf ng))
    (seqTM
      (copyWorkToWorkTM (compositionRawOutputIdx nf ng)
        (compositionVirtualInputIdx nf ng))
      (seqTM (rewindWorkTM (compositionVirtualInputIdx nf ng))
        (compositionSecondTM nf tmG)))

/-- Executable sequential composition of a function computation with a second
deterministic machine. -/
def compositionTM (tmF : TM nf) (tmG : TM ng) : TM (compositionTapeCount nf ng) :=
  seqTM (compositionFirstTM tmF ng) (compositionTailTM nf ng tmG)

end TM

end Complexity
