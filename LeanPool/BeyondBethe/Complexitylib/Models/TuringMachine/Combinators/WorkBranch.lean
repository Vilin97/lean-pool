/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch.Internal

/-!
# Direct work-symbol branch combinator

`TM.branchWorkBlankTM idx onBlank onNonblank` reads one work-tape symbol and
runs `onBlank` exactly on blank, or `onNonblank` on any other symbol. The
dispatcher performs one framed, tape-preserving step. It never writes a test
result to the output tape, and branch simulation adds no trailing seam step.

The preservation results require every head to be off the left marker. This
is the necessary boundary condition imposed by the one-sided tape model:
heads reading `▷` must move right.

## Main results

- `TM.branchWorkBlankTM_reachesIn_blank_frame` and its nonblank counterpart
  give exact selected-branch execution and literal tape frames.
- `TM.branchWorkBlankTM_hoareTime` composes two branch contracts with one
  dispatch step.
- `TM.branchWorkBlankTM_hoareTimeSpace` preserves the maximum branch budget.
- `Tape.HasBinaryNat.read_eq_blank_iff` specializes blank dispatch to
  canonical binary zero.
- `TM.IsTransducer.branchWorkBlankTM` preserves one-way output behavior.
-/


@[expose] public section

namespace Complexity

namespace Tape

/-- A canonical little-endian natural reads blank exactly when its value is
zero. Consequently the direct blank/nonblank work branch is a canonical
zero/nonzero branch on `HasBinaryNat` tapes. -/
theorem HasBinaryNat.read_eq_blank_iff {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) :
    t.read = Γ.blank ↔ value = 0 :=
  h.read_eq_blank_iff_internal

end Tape

namespace TM

variable {n : ℕ}

/-- Blank dispatch takes one step, selects the blank branch, and preserves
all tapes exactly. -/
theorem branchWorkBlankTM_dispatch_blank
    (idx : Fin n) (onBlank onNonblank : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hblank : (work idx).read = Γ.blank)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) :
    (branchWorkBlankTM idx onBlank onNonblank).step
        { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
          input := inp
          work := work
          output := out } =
      some
        { state := workBranchBlankState onBlank onNonblank onBlank.qstart
          input := inp
          work := work
          output := out } := by
  simpa [workBranchBlankWrap] using
    branchWorkBlankTM_dispatch_blank_internal idx onBlank onNonblank
      inp work out hblank hinp hwork hout

/-- Nonblank dispatch takes one step, selects the nonblank branch, and
preserves all tapes exactly. -/
theorem branchWorkBlankTM_dispatch_nonblank
    (idx : Fin n) (onBlank onNonblank : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hnonblank : (work idx).read ≠ Γ.blank)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) :
    (branchWorkBlankTM idx onBlank onNonblank).step
        { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
          input := inp
          work := work
          output := out } =
      some
        { state := workBranchNonblankState onBlank onNonblank
            onNonblank.qstart
          input := inp
          work := work
          output := out } := by
  simpa [workBranchNonblankWrap] using
    branchWorkBlankTM_dispatch_nonblank_internal idx onBlank onNonblank
      inp work out hnonblank hinp hwork hout

/-- Exact framed execution through the blank branch. The combined controller
uses one dispatch transition followed by the branch's exact `t` transitions. -/
theorem branchWorkBlankTM_reachesIn_blank_frame
    (idx : Fin n) (onBlank onNonblank : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {t : ℕ} {c' : Cfg n onBlank.Q}
    (hblank : (work idx).read = Γ.blank)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start)
    (hreach : onBlank.reachesIn t
      { state := onBlank.qstart, input := inp, work := work, output := out } c')
    (hhalt : onBlank.halted c') :
    ∃ C,
      (branchWorkBlankTM idx onBlank onNonblank).reachesIn (t + 1)
        { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
          input := inp
          work := work
          output := out } C ∧
      (branchWorkBlankTM idx onBlank onNonblank).halted C ∧
      C.input = c'.input ∧ C.work = c'.work ∧ C.output = c'.output :=
  branchWorkBlankTM_reachesIn_blank_frame_internal idx onBlank onNonblank
    inp work out hblank hinp hwork hout hreach hhalt

/-- Exact framed execution through the nonblank branch. -/
theorem branchWorkBlankTM_reachesIn_nonblank_frame
    (idx : Fin n) (onBlank onNonblank : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {t : ℕ} {c' : Cfg n onNonblank.Q}
    (hnonblank : (work idx).read ≠ Γ.blank)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start)
    (hreach : onNonblank.reachesIn t
      { state := onNonblank.qstart, input := inp, work := work, output := out } c')
    (hhalt : onNonblank.halted c') :
    ∃ C,
      (branchWorkBlankTM idx onBlank onNonblank).reachesIn (t + 1)
        { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
          input := inp
          work := work
          output := out } C ∧
      (branchWorkBlankTM idx onBlank onNonblank).halted C ∧
      C.input = c'.input ∧ C.work = c'.work ∧ C.output = c'.output :=
  branchWorkBlankTM_reachesIn_nonblank_frame_internal idx onBlank onNonblank
    inp work out hnonblank hinp hwork hout hreach hhalt

/-- Compose two time-bounded branch contracts. The precondition supplies the
off-marker frame and translates the initial read into the selected branch's
precondition. The postcondition records which branch contract completed. -/
theorem branchWorkBlankTM_hoareTime
    (idx : Fin n) (onBlank onNonblank : TM n)
    {pre blankPre nonblankPre blankPost nonblankPost : TapePred n}
    {blankTime nonblankTime : ℕ}
    (hframe : ∀ inp work out, pre inp work out →
      inp.read ≠ Γ.start ∧ (∀ i, (work i).read ≠ Γ.start) ∧
        out.read ≠ Γ.start)
    (hblankPre : ∀ inp work out, pre inp work out →
      (work idx).read = Γ.blank → blankPre inp work out)
    (hnonblankPre : ∀ inp work out, pre inp work out →
      (work idx).read ≠ Γ.blank → nonblankPre inp work out)
    (hblank : onBlank.HoareTime blankPre blankPost blankTime)
    (hnonblank : onNonblank.HoareTime nonblankPre nonblankPost nonblankTime) :
    (branchWorkBlankTM idx onBlank onNonblank).HoareTime pre
      (fun inp work out =>
        blankPost inp work out ∨ nonblankPost inp work out)
      (branchWorkBlankTime blankTime nonblankTime) :=
  branchWorkBlankTM_hoareTime_internal idx onBlank onNonblank hframe
    hblankPre hnonblankPre hblank hnonblank

/-- Compose two time-and-space branch contracts. Dispatch preserves the
starting tapes, so the all-reachable space bound is exactly the maximum of the
two branch budgets rather than an additional seam allowance. -/
theorem branchWorkBlankTM_hoareTimeSpace
    (idx : Fin n) (onBlank onNonblank : TM n)
    {pre blankPre nonblankPre blankPost nonblankPost : TapePred n}
    {blankTime nonblankTime inputLength blankSpace nonblankSpace : ℕ}
    (hframe : ∀ inp work out, pre inp work out →
      inp.read ≠ Γ.start ∧ (∀ i, (work i).read ≠ Γ.start) ∧
        out.read ≠ Γ.start)
    (hblankPre : ∀ inp work out, pre inp work out →
      (work idx).read = Γ.blank → blankPre inp work out)
    (hnonblankPre : ∀ inp work out, pre inp work out →
      (work idx).read ≠ Γ.blank → nonblankPre inp work out)
    (hblank : onBlank.HoareTimeSpace blankPre blankPost blankTime
      inputLength blankSpace)
    (hnonblank : onNonblank.HoareTimeSpace nonblankPre nonblankPost
      nonblankTime inputLength nonblankSpace) :
    (branchWorkBlankTM idx onBlank onNonblank).HoareTimeSpace pre
      (fun inp work out =>
        blankPost inp work out ∨ nonblankPost inp work out)
      (branchWorkBlankTime blankTime nonblankTime) inputLength
      (max blankSpace nonblankSpace) :=
  branchWorkBlankTM_hoareTimeSpace_internal idx onBlank onNonblank hframe
    hblankPre hnonblankPre hblank hnonblank

/-- Direct work branching preserves one-way output when both selected
branches do. The dispatch step itself never moves the output head left. -/
theorem IsTransducer.branchWorkBlankTM
    {idx : Fin n} {onBlank onNonblank : TM n}
    (hblank : onBlank.IsTransducer)
    (hnonblank : onNonblank.IsTransducer) :
    (branchWorkBlankTM idx onBlank onNonblank).IsTransducer :=
  hblank.branchWorkBlankTM_internal hnonblank

end TM

end Complexity
