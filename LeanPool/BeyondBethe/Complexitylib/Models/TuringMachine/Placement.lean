/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Placement.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Placement.Internal

/-!
# Work-tape placement

This public surface exposes exact simulation theorems for `TM.placeWorkTM`.
The source machine occupies a contiguous middle block of physical work tapes;
prefix and suffix tapes form an arbitrary preserved frame whenever their heads
are parked away from the left-end marker.

## Main results

- `TM.placeWorkTM_step_placeWorkCfg` — exact step with an evolving frame
- `TM.placeWorkTM_reachesIn_placeWorkCfg_stable` — exact stable-frame simulation
- `TM.placeWorkTM_reachesIn_placeWorkParkedCfg` — canonical parked simulation
- `TM.placeWorkTM_computesInTime` — same-time preservation of computation
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- A placed step simulates one source step while applying the prescribed idle
action to the arbitrary physical extra-tape frame. -/
theorem placeWorkTM_step_placeWorkCfg (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) :
    (placeWorkTM pre post tm).step (placeWorkCfg tm pre post extras c) =
      (tm.step c).map
        (placeWorkCfg tm pre post (placeWorkFrameStep extras)) :=
  placeWorkTM_step_placeWorkCfg_internal tm pre post extras c

/-- If every extra tape reads a non-left-end symbol, its idle action is a
no-op and a placed step commutes through the unchanged frame. -/
theorem placeWorkTM_step_placeWorkCfg_stable (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q)
    (hextra : ∀ i, ¬placeWorkInMiddle pre n i → (extras i).read ≠ Γ.start) :
    (placeWorkTM pre post tm).step (placeWorkCfg tm pre post extras c) =
      (tm.step c).map (placeWorkCfg tm pre post extras) :=
  placeWorkTM_step_placeWorkCfg_stable_internal tm pre post extras c hextra

/-- Start-invariant extra tapes whose heads are at positive positions form a
stable frame for one placed step. -/
theorem placeWorkTM_step_placeWorkCfg_of_startInvariant (tm : TM n)
    (pre post : ℕ) (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q)
    (hinv : ∀ i, ¬placeWorkInMiddle pre n i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬placeWorkInMiddle pre n i → 1 ≤ (extras i).head) :
    (placeWorkTM pre post tm).step (placeWorkCfg tm pre post extras c) =
      (tm.step c).map (placeWorkCfg tm pre post extras) := by
  apply placeWorkTM_step_placeWorkCfg_stable tm pre post extras c
  intro i hi
  show (extras i).cells (extras i).head ≠ Γ.start
  exact (hinv i hi).2 (extras i).head (hhead i hi)

/-- A stable arbitrary frame is preserved exactly throughout a bounded source
run, with no time overhead. -/
theorem placeWorkTM_reachesIn_placeWorkCfg_stable (tm : TM n)
    (pre post : ℕ) (extras : Fin (pre + n + post) → Tape)
    {t : ℕ} {c c' : Cfg n tm.Q} (hreach : tm.reachesIn t c c')
    (hextra : ∀ i, ¬placeWorkInMiddle pre n i → (extras i).read ≠ Γ.start) :
    (placeWorkTM pre post tm).reachesIn t
      (placeWorkCfg tm pre post extras c)
      (placeWorkCfg tm pre post extras c') :=
  placeWorkTM_reachesIn_placeWorkCfg_stable_internal tm pre post extras hreach hextra

/-- Start-invariant positive-head extras remain an exact frame throughout a
bounded source run. -/
theorem placeWorkTM_reachesIn_placeWorkCfg_of_startInvariant (tm : TM n)
    (pre post : ℕ) (extras : Fin (pre + n + post) → Tape)
    {t : ℕ} {c c' : Cfg n tm.Q} (hreach : tm.reachesIn t c c')
    (hinv : ∀ i, ¬placeWorkInMiddle pre n i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬placeWorkInMiddle pre n i → 1 ≤ (extras i).head) :
    (placeWorkTM pre post tm).reachesIn t
      (placeWorkCfg tm pre post extras c)
      (placeWorkCfg tm pre post extras c') := by
  apply placeWorkTM_reachesIn_placeWorkCfg_stable tm pre post extras hreach
  intro i hi
  show (extras i).cells (extras i).head ≠ Γ.start
  exact (hinv i hi).2 (extras i).head (hhead i hi)

/-- The canonical parked embedding commutes with one source step. -/
theorem placeWorkTM_step_placeWorkParkedCfg (tm : TM n) (pre post : ℕ)
    (c : Cfg n tm.Q) :
    (placeWorkTM pre post tm).step (placeWorkParkedCfg tm pre post c) =
      (tm.step c).map (placeWorkParkedCfg tm pre post) :=
  placeWorkTM_step_placeWorkParkedCfg_internal tm pre post c

/-- The canonical parked embedding simulates a bounded source run exactly. -/
theorem placeWorkTM_reachesIn_placeWorkParkedCfg (tm : TM n)
    (pre post : ℕ) {t : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c') :
    (placeWorkTM pre post tm).reachesIn t
      (placeWorkParkedCfg tm pre post c)
      (placeWorkParkedCfg tm pre post c') :=
  placeWorkTM_reachesIn_placeWorkParkedCfg_internal tm pre post hreach

/-- A placed embedded configuration is halted exactly when its source
configuration is halted. -/
@[simp] theorem placeWorkCfg_halted_iff (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) :
    (placeWorkTM pre post tm).halted (placeWorkCfg tm pre post extras c) ↔
      tm.halted c := by
  rfl

/-- A bounded run from the source's ordinary initial configuration lifts with
the same duration. A positive run ends in the canonical parked embedding; at
time zero the placed machine remains at its own ordinary initial configuration. -/
theorem placeWorkTM_reachesIn_init (tm : TM n) (pre post : ℕ)
    (x : List Bool) {t : ℕ} {c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t (tm.initCfg x) c') :
    ∃ C' : Cfg (pre + n + post) (placeWorkTM pre post tm).Q,
      (placeWorkTM pre post tm).reachesIn t ((placeWorkTM pre post tm).initCfg x) C' ∧
      C'.state = c'.state ∧ C'.input = c'.input ∧ C'.output = c'.output ∧
      (t = 0 ∨ C' = placeWorkParkedCfg tm pre post c') :=
  placeWorkTM_reachesIn_init_internal tm pre post x hreach

/-- Work-tape placement preserves deterministic function computation with
exactly the same time bound. The surrounding blank tapes bounce off `▷`
during the source machine's own first step and then remain parked. -/
theorem placeWorkTM_computesInTime (tm : TM n) (pre post : ℕ)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : tm.ComputesInTime f T) :
    (placeWorkTM pre post tm).ComputesInTime f T :=
  placeWorkTM_computesInTime_internal tm pre post hcomp

end TM

end Complexity
