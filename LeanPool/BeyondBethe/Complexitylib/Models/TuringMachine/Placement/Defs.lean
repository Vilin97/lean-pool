/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# Work-tape placement

This file defines a layout combinator that places the work tapes of a machine
inside a larger, contiguous middle block. The surrounding physical tapes are
idled, so later phases can reserve disjoint tape regions without changing the
source machine.

## Main definitions

- `TM.placeWorkIdx` — physical index of a source work tape
- `TM.placeWorkCoord` — source coordinate of a physical middle-block tape
- `TM.placeWorkTM` — place a machine between `pre` prefix and `post` suffix tapes
- `TM.placeWorkCfg` — embed a configuration with an arbitrary extra-tape frame
- `TM.placeWorkFrameStep` — one idle action on every physical frame tape
- `TM.placeWorkParkedCfg` — the canonical embedding with parked blank extras
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n pre post : ℕ}

/-- Physical work-tape index occupied by source work tape `i` after placement. -/
def placeWorkIdx (pre post : ℕ) (i : Fin n) : Fin (pre + n + post) :=
  ⟨pre + i.val, by omega⟩

/-- A physical work tape lies in the block occupied by the source machine. -/
def placeWorkInMiddle (pre n : ℕ) {post : ℕ} (i : Fin (pre + n + post)) : Prop :=
  pre ≤ i.val ∧ i.val < pre + n

instance instDecidablePlaceWorkInMiddle (pre n : ℕ) {post : ℕ}
    (i : Fin (pre + n + post)) : Decidable (placeWorkInMiddle pre n i) := by
  unfold placeWorkInMiddle
  infer_instance

/-- Source coordinate corresponding to a physical tape in the middle block. -/
def placeWorkCoord (pre n : ℕ) {post : ℕ} (i : Fin (pre + n + post))
    (h : placeWorkInMiddle pre n i) : Fin n :=
  ⟨i.val - pre, by
    unfold placeWorkInMiddle at h
    omega⟩

@[simp] theorem placeWorkIdx_val (pre post : ℕ) (i : Fin n) :
    (placeWorkIdx pre post i).val = pre + i.val := rfl

@[simp] theorem placeWorkInMiddle_placeWorkIdx (pre post : ℕ) (i : Fin n) :
    placeWorkInMiddle pre n (placeWorkIdx pre post i) := by
  unfold placeWorkInMiddle
  simp only [placeWorkIdx_val]
  exact ⟨by omega, by omega⟩

@[simp] theorem placeWorkCoord_placeWorkIdx (pre post : ℕ) (i : Fin n) :
    placeWorkCoord pre n (placeWorkIdx pre post i)
      (placeWorkInMiddle_placeWorkIdx pre post i) = i := by
  apply Fin.ext
  simp [placeWorkCoord]

theorem placeWorkIdx_placeWorkCoord (i : Fin (pre + n + post))
    (h : placeWorkInMiddle pre n i) :
    placeWorkIdx pre post (placeWorkCoord pre n i h) = i := by
  apply Fin.ext
  unfold placeWorkInMiddle at h
  simp [placeWorkIdx, placeWorkCoord]
  omega

theorem placeWorkIdx_injective (pre post : ℕ) :
    Function.Injective (placeWorkIdx (n := n) pre post) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [placeWorkIdx_val] at this
  omega

/-- Place `tm` after `pre` reserved work tapes and before `post` reserved work
tapes. Physical tapes in the middle block simulate `tm`; every other work tape
writes back the symbol it reads and idles. Input and output actions are unchanged. -/
def placeWorkTM (pre post : ℕ) (tm : TM n) : TM (pre + n + post) where
  Q := tm.Q
  qstart := tm.qstart
  qhalt := tm.qhalt
  δ := fun q iHead wHeads oHead =>
    let r := tm.δ q iHead (fun i => wHeads (placeWorkIdx pre post i)) oHead
    (r.1,
      fun i =>
        if h : placeWorkInMiddle pre n i then r.2.1 (placeWorkCoord pre n i h)
        else readBackWrite (wHeads i),
      r.2.2.1,
      r.2.2.2.1,
      fun i =>
        if h : placeWorkInMiddle pre n i then r.2.2.2.2.1 (placeWorkCoord pre n i h)
        else idleDir (wHeads i),
      r.2.2.2.2.2)
  δ_right_of_start := by
    intro q iHead wHeads oHead
    obtain ⟨hin, hwork, hout⟩ :=
      tm.δ_right_of_start q iHead (fun i => wHeads (placeWorkIdx pre post i)) oHead
    refine ⟨hin, fun i hi => ?_, hout⟩
    dsimp only
    split
    · rename_i hmid
      apply hwork (placeWorkCoord pre n i hmid)
      rw [placeWorkIdx_placeWorkCoord i hmid]
      exact hi
    · exact idleDir_right_of_start hi

/-- Embed `c` into the placed layout. The supplied physical `extras` frame is
used outside the middle block and ignored inside it. -/
def placeWorkCfg (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) :
    Cfg (pre + n + post) (placeWorkTM pre post tm).Q where
  state := c.state
  input := c.input
  work := fun i =>
    if h : placeWorkInMiddle pre n i then c.work (placeWorkCoord pre n i h)
    else extras i
  output := c.output

/-- Apply the placement machine's idle work-tape action to an extra-tape frame.
Only values outside the middle block are observable through `placeWorkCfg`. -/
def placeWorkFrameStep {pre n post : ℕ}
    (extras : Fin (pre + n + post) → Tape) : Fin (pre + n + post) → Tape :=
  fun i => (extras i).writeAndMove (readBackWrite (extras i).read)
    (idleDir (extras i).read)

/-- Canonical embedding whose prefix and suffix tapes are parked and blank. -/
def placeWorkParkedCfg (tm : TM n) (pre post : ℕ) (c : Cfg n tm.Q) :
    Cfg (pre + n + post) (placeWorkTM pre post tm).Q :=
  placeWorkCfg tm pre post (fun _ => (Tape.init []).move Dir3.right) c

@[simp] theorem placeWorkCfg_state (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) :
    (placeWorkCfg tm pre post extras c).state = c.state := rfl

@[simp] theorem placeWorkCfg_input (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) :
    (placeWorkCfg tm pre post extras c).input = c.input := rfl

@[simp] theorem placeWorkCfg_output (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) :
    (placeWorkCfg tm pre post extras c).output = c.output := rfl

@[simp] theorem placeWorkCfg_work_middle (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) (i : Fin n) :
    (placeWorkCfg tm pre post extras c).work (placeWorkIdx pre post i) = c.work i := by
  simp only [placeWorkCfg, placeWorkInMiddle_placeWorkIdx, dite_true]
  rw [placeWorkCoord_placeWorkIdx]

theorem placeWorkCfg_work_extra (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q)
    (i : Fin (pre + n + post)) (h : ¬placeWorkInMiddle pre n i) :
    (placeWorkCfg tm pre post extras c).work i = extras i := by
  simp [placeWorkCfg, h]

theorem placeWorkCfg_work_prefix (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) (i : Fin pre) :
    (placeWorkCfg tm pre post extras c).work ⟨i.val, by omega⟩ =
      extras ⟨i.val, by omega⟩ := by
  apply placeWorkCfg_work_extra
  simp [placeWorkInMiddle]

theorem placeWorkCfg_work_suffix (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) (i : Fin post) :
    (placeWorkCfg tm pre post extras c).work ⟨pre + n + i.val, by omega⟩ =
      extras ⟨pre + n + i.val, by omega⟩ := by
  apply placeWorkCfg_work_extra
  simp [placeWorkInMiddle]

end TM

end Complexity
