/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Internal

/-!
# Clearing a binary work tape

This module exposes a literal-frame contract for erasing a canonical Boolean
work tape and returning its head to cell one. It also records the one-way-output
discipline of the clearing, rewinding, and composite machines.

## Main results

- `clearWorkTM_hoareTime_frame` — clear and rewind with a full external frame.
- `clearWorkTM_hoareTimeSpace_frame` — the corresponding all-prefix space contract.
- `clearWorkTM_isTransducer` — clearing never moves the output head left.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Clearing a canonical Boolean work tape preserves the input, output, and
every unrelated work tape literally, and resets the target to the standard
parked blank tape within `2 * bits.length + 5` steps. -/
theorem clearWorkTM_hoareTime_frame
    (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : work₀ idx =
      (Tape.init (bits.map Γ.ofBool)).move Dir3.right)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀) :
    (clearWorkTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx
          ((Tape.init []).move Dir3.right) ∧
        out = out₀)
      (clearWorkTimeBound bits.length) :=
  clearWorkTM_hoareTime_frame_internal idx bits inp₀ work₀ out₀
    htarget hinp hother hout

/-- Time-and-space form of `clearWorkTM_hoareTime_frame`. Starting from an
`initialSpace` budget, one extra cell per possible transition yields an honest
all-reachable bound. -/
theorem clearWorkTM_hoareTimeSpace_frame
    (idx : Fin n) (bits : List Bool) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : work₀ idx =
      (Tape.init (bits.map Γ.ofBool)).move Dir3.right)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀)
    (hinitial :
      ({ state := (clearWorkTM idx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (clearWorkTM idx).Q).WithinAuxSpace inputLength initialSpace) :
    (clearWorkTM idx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx
          ((Tape.init []).move Dir3.right) ∧
        out = out₀)
      (clearWorkTimeBound bits.length) inputLength
      (initialSpace + clearWorkTimeBound bits.length) :=
  clearWorkTM_hoareTimeSpace_frame_internal idx bits inputLength initialSpace
    inp₀ work₀ out₀ htarget hinp hother hout hinitial

/-- Blanking a work tape never moves the output head left. -/
theorem blankWorkTM_isTransducer (idx : Fin n) :
    (blankWorkTM idx).IsTransducer :=
  blankWorkTM_isTransducer_internal idx

/-- Rewinding a work tape never moves the output head left. -/
theorem rewindWorkTM_isTransducer (idx : Fin n) :
    (rewindWorkTM idx).IsTransducer :=
  rewindWorkTM_isTransducer_internal idx

/-- Clearing and rewinding a work tape never moves the output head left. -/
theorem clearWorkTM_isTransducer (idx : Fin n) :
    (clearWorkTM idx).IsTransducer :=
  clearWorkTM_isTransducer_internal idx

end TM

end Complexity
