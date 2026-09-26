/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.RetargetCompute.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.RetargetCompute.Internal

/-!
# Retargeted-input computation seams

`TM.retargetInputStarted` runs a source machine on a virtual input held by its
last work tape when every participating head is already parked at cell `1`.
It absorbs the source machine's compulsory first transition from `▷`, making
the wrapper suitable as a later phase of `TM.seqTM`.

The degenerate `qstart = qhalt` case is included: such a source computes only
the empty string, and the wrapper halts immediately without requiring a
positive advertised time bound.

## Main results

- `TM.retargetInputStarted_computesVirtual_exact` — exact saved-start time
- `TM.retargetInputStarted_computesVirtual` — same-time virtual computation
- `TM.retargetInputStarted_decidesVirtual` — same-time virtual decision
- `TM.retargetInputStarted_hoareTime` — Hoare form for phase composition
- `TM.placeWorkTM_retargetInputStarted_computesVirtual` — placed stable-frame seam
- `TM.placeWorkTM_retargetInputStarted_decidesVirtual` — placed decision seam
-/


@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-- The started wrapper and ordinary retargeted-input machine have identical
step functions. -/
theorem retargetInputStarted_step_eq (M : TM k) (c : Cfg (k + 1) M.Q) :
    (retargetInputStarted M).step c = (retargetInput M).step c :=
  retargetInputStarted_step_eq_internal M c

/-- A run of `retargetInput M` is also a run of its started wrapper. -/
theorem retargetInputStarted_reachesIn_of_retargetInput (M : TM k)
    {t : ℕ} {c c' : Cfg (k + 1) M.Q}
    (hreach : (retargetInput M).reachesIn t c c') :
    (retargetInputStarted M).reachesIn t c c' :=
  retargetInputStarted_reachesIn_of_retargetInput_internal M hreach

/-- For a non-halted source start state, the wrapper entry configuration is
exactly the retargeted embedding of the source's post-sentinel configuration. -/
theorem retargetInputStartedCfg_eq_retargetWrap (M : TM k)
    (y : List Bool) (realInput : Tape) (hne : M.qstart ≠ M.qhalt) :
    retargetInputStartedCfg M y realInput =
      retargetWrap M realInput (startedCfg M y hne) :=
  retargetInputStartedCfg_eq_retargetWrap_internal M y realInput hne

/-- Exact virtual-input computation seam. A nondegenerate source run saves its
first transition; an initially halted source uses zero transitions. -/
theorem retargetInputStarted_computesVirtual_exact (M : TM k)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) (realInput : Tape) :
    ∃ (c' : Cfg (k + 1) M.Q) (t : ℕ),
      t + (if M.qstart = M.qhalt then 0 else 1) ≤ T y.length ∧
      (retargetInputStarted M).reachesIn t
        (retargetInputStartedCfg M y realInput) c' ∧
      (retargetInputStarted M).halted c' ∧
      c'.output.HasOutput (f y) :=
  retargetInputStarted_computesVirtual_exact_internal M hcomp y realInput

/-- The started virtual-input wrapper computes within the source's advertised
time bound. -/
theorem retargetInputStarted_computesVirtual (M : TM k)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) (realInput : Tape) :
    ∃ (c' : Cfg (k + 1) M.Q) (t : ℕ),
      t ≤ T y.length ∧
      (retargetInputStarted M).reachesIn t
        (retargetInputStartedCfg M y realInput) c' ∧
      (retargetInputStarted M).halted c' ∧
      c'.output.HasOutput (f y) :=
  retargetInputStarted_computesVirtual_internal M hcomp y realInput

/-- The started virtual-input wrapper retains a source decider's two verdict
implications within the source's advertised time bound. -/
theorem retargetInputStarted_decidesVirtual (M : TM k)
    {L : Language} {T : ℕ → ℕ}
    (hdec : M.DecidesInTime L T) (y : List Bool) (realInput : Tape) :
    ∃ (c' : Cfg (k + 1) M.Q) (t : ℕ),
      t ≤ T y.length ∧
      (retargetInputStarted M).reachesIn t
        (retargetInputStartedCfg M y realInput) c' ∧
      (retargetInputStarted M).halted c' ∧
      (y ∈ L → c'.output.cells 1 = Γ.one) ∧
      (y ∉ L → c'.output.cells 1 = Γ.zero) :=
  retargetInputStarted_decidesVirtual_internal M hdec y realInput

/-- Hoare form of the same-time virtual-input seam. The real input is ignored;
the work and output tapes have the canonical already-started shapes. -/
theorem retargetInputStarted_hoareTime (M : TM k)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) :
    (retargetInputStarted M).HoareTime
      (fun inp work out =>
        work = (retargetInputStartedCfg M y inp).work ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp _work out => out.HasOutput (f y))
      (T y.length) :=
  retargetInputStarted_hoareTime_internal M hcomp y

/-- Placed virtual-input computation with an exact preserved prefix/suffix
frame. The middle block contains the source scratch tapes and virtual input.
Every extra tape satisfying the standard start invariant at a positive head
position is unchanged in the final `placeWorkCfg` endpoint. -/
theorem placeWorkTM_retargetInputStarted_computesVirtual (M : TM k)
    (pre post : ℕ) (extras : Fin (pre + (k + 1) + post) → Tape)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) (realInput : Tape)
    (hinv : ∀ i, ¬placeWorkInMiddle pre (k + 1) i →
      Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬placeWorkInMiddle pre (k + 1) i →
      1 ≤ (extras i).head) :
    ∃ (c' : Cfg (k + 1) M.Q)
      (C' : Cfg (pre + (k + 1) + post)
        (placeWorkTM pre post (retargetInputStarted M)).Q) (t : ℕ),
      t ≤ T y.length ∧
      (placeWorkTM pre post (retargetInputStarted M)).reachesIn t
        (placeWorkCfg (retargetInputStarted M) pre post extras
          (retargetInputStartedCfg M y realInput)) C' ∧
      C' = placeWorkCfg (retargetInputStarted M) pre post extras c' ∧
      (placeWorkTM pre post (retargetInputStarted M)).halted C' ∧
      C'.output.HasOutput (f y) :=
  placeWorkTM_retargetInputStarted_computesVirtual_internal M pre post extras
    hcomp y realInput hinv hhead

/-- Placed virtual-input decision with an exact preserved prefix/suffix frame. -/
theorem placeWorkTM_retargetInputStarted_decidesVirtual (M : TM k)
    (pre post : ℕ) (extras : Fin (pre + (k + 1) + post) → Tape)
    {L : Language} {T : ℕ → ℕ}
    (hdec : M.DecidesInTime L T) (y : List Bool) (realInput : Tape)
    (hinv : ∀ i, ¬placeWorkInMiddle pre (k + 1) i →
      Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬placeWorkInMiddle pre (k + 1) i →
      1 ≤ (extras i).head) :
    ∃ (c' : Cfg (k + 1) M.Q)
      (C' : Cfg (pre + (k + 1) + post)
        (placeWorkTM pre post (retargetInputStarted M)).Q) (t : ℕ),
      t ≤ T y.length ∧
      (placeWorkTM pre post (retargetInputStarted M)).reachesIn t
        (placeWorkCfg (retargetInputStarted M) pre post extras
          (retargetInputStartedCfg M y realInput)) C' ∧
      C' = placeWorkCfg (retargetInputStarted M) pre post extras c' ∧
      (placeWorkTM pre post (retargetInputStarted M)).halted C' ∧
      (y ∈ L → C'.output.cells 1 = Γ.one) ∧
      (y ∉ L → C'.output.cells 1 = Γ.zero) :=
  placeWorkTM_retargetInputStarted_decidesVirtual_internal M pre post extras
    hdec y realInput hinv hhead

end TM

end Complexity
