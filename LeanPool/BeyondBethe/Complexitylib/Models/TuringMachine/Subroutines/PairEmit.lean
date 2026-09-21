/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairEmit.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairEmit.Internal

/-!
# Pair emission from the input and a work tape

The emitter reads a delimited first component from a designated work tape,
doubles its bits, writes the pair separator, and copies the real input as the
second component.

## Main results

- `TM.pairInputWorkTM_reachesIn` — exact execution from a concrete tape boundary
- `TM.pairInputWorkTM_hoareTime` — compositional time-bounded contract
-/


public section

namespace Complexity

namespace TM

/-- Exact pair emission preserves the source cells and every unrelated work
tape, consumes both sources through their delimiters, and leaves the output as
an appendable prefix containing the canonical pair. -/
theorem pairInputWorkTM_reachesIn {n : ℕ}
    (firstIdx : Fin n) (first second : List Bool)
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : inp = (Tape.init (second.map Γ.ofBool)).move Dir3.right)
    (hsourceHead : (work firstIdx).head = 1)
    (hsourceOutput : (work firstIdx).HasOutput first)
    (hwork : ∀ i, (work i).StartInvariant ∧ 1 ≤ (work i).head)
    (houtput : out = (Tape.init []).move Dir3.right) :
    ∃ c',
      (pairInputWorkTM firstIdx).reachesIn (pairInputWorkTime first second)
        { state := (pairInputWorkTM firstIdx).qstart,
          input := inp, work := work, output := out } c' ∧
      (pairInputWorkTM firstIdx).halted c' ∧
      c'.input.HasBinarySuffix [] ∧
      c'.input.cells = inp.cells ∧
      (c'.work firstIdx).HasBinarySuffix [] ∧
      (c'.work firstIdx).cells = (work firstIdx).cells ∧
      (c'.work firstIdx).HasOutput first ∧
      (∀ i, i ≠ firstIdx → c'.work i = work i) ∧
      c'.output.HasBinaryPrefix (pair first second) :=
  pairInputWorkTM_reachesIn_internal firstIdx first second hinput
    hsourceHead hsourceOutput hwork houtput

/-- Emit `pair first second` within
`2 * first.length + second.length + 3` steps. -/
theorem pairInputWorkTM_hoareTime {n : ℕ}
    (firstIdx : Fin n) (first second : List Bool) :
    (pairInputWorkTM firstIdx).HoareTime
      (fun inp work out =>
        inp = (Tape.init (second.map Γ.ofBool)).move Dir3.right ∧
        (work firstIdx).head = 1 ∧
        (work firstIdx).HasOutput first ∧
        (∀ i, (work i).StartInvariant ∧ 1 ≤ (work i).head) ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp _work out => out.HasOutput (pair first second))
      (pairInputWorkTime first second) :=
  pairInputWorkTM_hoareTime_internal firstIdx first second

end TM

end Complexity
