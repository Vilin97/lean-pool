/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Internal.CopyWorkOutput

/-!
# Copy a raw work-tape output

These theorems let `TM.copyWorkToWorkTM` consume a source satisfying
`Tape.HasOutput`, even when cells after the terminating blank contain arbitrary
junk. The fresh destination receives a canonical `Tape.HasBinaryPrefix`.

## Main results

- `TM.copyWorkToWorkTM_reachesIn_of_hasOutput` — exact concrete copy run
- `TM.copyWorkToWorkTM_hoareTime_of_hasOutput` — exact raw-output copy
- `TM.copyWorkToWorkTM_hoareTime_frame_of_hasOutput` — copy with frame preservation
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Starting at cell one, copy exactly the source's advertised output in
`|x| + 1` steps, preserving all source cells and the destination's cell zero. -/
theorem copyWorkToWorkTM_reachesIn_of_hasOutput {n : ℕ}
    (src dst : Fin n) (hne : src ≠ dst) (x : List Bool)
    {inp out : Tape} {work : Fin n → Tape}
    (hsrcHead : (work src).head = 1)
    (hsrcOutput : (work src).HasOutput x)
    (hdst : (work dst).HasBinaryPrefix []) :
    ∃ c',
      (copyWorkToWorkTM src dst).reachesIn (x.length + 1)
        { state := (copyWorkToWorkTM src dst).qstart,
          input := inp, work := work, output := out } c' ∧
      (copyWorkToWorkTM src dst).halted c' ∧
      (c'.work src).cells = (work src).cells ∧
      (c'.work src).head = x.length + 1 ∧
      (c'.work src).HasOutput x ∧
      (c'.work dst).HasBinaryPrefix x ∧
      (c'.work dst).cells 0 = (work dst).cells 0 := by
  exact copyWorkToWorkTM_reachesIn_of_hasOutput_internal
    src dst hne x hsrcHead hsrcOutput hdst

/-- Copy a raw `HasOutput` source to a fresh destination in exactly the usual
linear bound. Source cells are preserved, including arbitrary trailing junk. -/
theorem copyWorkToWorkTM_hoareTime_of_hasOutput {n : ℕ}
    (src dst : Fin n) (hne : src ≠ dst) (x : List Bool) (source : Tape) :
    (copyWorkToWorkTM src dst).HoareTime
      (fun _inp work _out =>
        work src = source ∧ source.head = 1 ∧ source.HasOutput x ∧
          (work dst).HasBinaryPrefix [])
      (fun _inp work _out =>
        (work src).cells = source.cells ∧
        (work src).head = x.length + 1 ∧
        (work src).HasOutput x ∧
        (work dst).HasBinaryPrefix x)
      (x.length + 1) := by
  exact copyWorkToWorkTM_hoareTime_of_hasOutput_internal src dst hne x source

/-- Frame-rich raw-output copy. The input, output, and unrelated work tapes
are preserved exactly while the source is copied to the fresh destination. -/
theorem copyWorkToWorkTM_hoareTime_frame_of_hasOutput {n : ℕ}
    (src dst : Fin n) (hne : src ≠ dst) (x : List Bool) (source : Tape)
    {P : Tape → (Fin n → Tape) → Tape → Prop}
    (hP : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      (work' src).cells = source.cells →
      (work' src).head = x.length + 1 →
      (work' src).HasOutput x →
      (work' dst).HasBinaryPrefix x →
      (work' dst).cells 0 = Γ.start →
      inp' = inp → out' = out →
      (∀ i, i ≠ src → i ≠ dst → work' i = work i) →
      P inp' work' out') :
    (copyWorkToWorkTM src dst).HoareTime
      (fun inp work out =>
        work src = source ∧ source.head = 1 ∧ source.HasOutput x ∧
        work dst = (Tape.init []).move Dir3.right ∧
        inp.read ≠ Γ.start ∧ out.read ≠ Γ.start ∧ 1 ≤ out.head ∧
        (∀ i, i ≠ src → i ≠ dst →
          (work i).read ≠ Γ.start ∧ 1 ≤ (work i).head) ∧
        P inp work out)
      (fun inp work out =>
        (work src).cells = source.cells ∧
        (work src).head = x.length + 1 ∧
        (work src).HasOutput x ∧
        (work dst).HasBinaryPrefix x ∧
        (work dst).cells 0 = Γ.start ∧
        P inp work out)
      (x.length + 1) := by
  exact copyWorkToWorkTM_hoareTime_frame_of_hasOutput_internal
    src dst hne x source hP

end TM

end Complexity
