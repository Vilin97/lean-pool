/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.RegisterOps
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.MoveLeftStep

/-!
# Parking every tape at once

Rewinding tapes one at a time needs every tape *not* being rewound to be
`Parked` already — a tape still reading `▷` would bounce to cell `1` as a side
effect. One `TM.skipTM` step with no target achieves that uniformly: from
`Tape.StartInvariant` alone, cell-`0` tapes bounce to cell `1` and parked tapes
stay put.

## Main results

- `TM.parkAll_hoareTime` — one step parks every tape
-/


public section

namespace Complexity

namespace TM

/-- One idle step on a `StartInvariant` tape is exactly a bounce off `▷` if it
was there, and otherwise a no-op: the resulting head is `max t.head 1`. -/
theorem move_idleDir_eq_of_startInvariant {t : Tape} (h : Tape.StartInvariant t) :
    t.move (idleDir t.read) = ⟨max t.head 1, t.cells⟩ := by
  by_cases hh : t.read = Γ.start
  · have hh0 : t.head = 0 := by
      by_contra hc
      exact (h.2 t.head (by omega)) hh
    rw [idleDir, ite_eq_left hh]
    refine Tape.ext ?_ (Tape.move_cells t Dir3.right)
    show t.head + 1 = max t.head 1
    omega
  · have hh0 : t.head ≠ 0 := fun hc => hh (by rw [Tape.read, hc]; exact h.1)
    rw [idleDir, ite_eq_right hh]
    show t = ⟨max t.head 1, t.cells⟩
    have : max t.head 1 = t.head := by omega
    rw [this]

/-- One idle step parks a `StartInvariant` tape: bounces it off `▷` if it was
there, and otherwise leaves it exactly as it was. -/
theorem parked_move_idleDir_of_startInvariant {t : Tape} (h : Tape.StartInvariant t) :
    Parked (t.move (idleDir t.read)) ∧ (t.move (idleDir t.read)).cells = t.cells := by
  rw [move_idleDir_eq_of_startInvariant h]
  exact ⟨⟨le_max_right _ _, fun j hj => h.2 j hj⟩, rfl⟩

/-- **Parking every tape at once.** From tapes satisfying only
`StartInvariant`, one `skipTM` step brings every one of them to `Parked`,
preserving all cell contents exactly. -/
theorem parkAll_hoareTime {n : ℕ} (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Tape.StartInvariant inp₀) (hwork : ∀ i, Tape.StartInvariant (work₀ i))
    (hout : Tape.StartInvariant out₀) :
    (skipTM (n := n)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = (⟨max inp₀.head 1, inp₀.cells⟩ : Tape) ∧
        (∀ i, work i = (⟨max (work₀ i).head 1, (work₀ i).cells⟩ : Tape)) ∧
        out = (⟨max out₀.head 1, out₀.cells⟩ : Tape))
      1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨⟨(skipTM (n := n)).qhalt,
      inp.move (idleDir inp.read),
      fun i => (work i).move (idleDir (work i).read),
      out.move (idleDir out.read)⟩,
    1, le_refl 1, ?_, rfl, ?_, ?_, ?_⟩
  · refine TM.reachesIn.step ?_ .zero
    simp only [TM.step, skipTM,
      ite_eq_right (show BumpPhase.go ≠ BumpPhase.done by decide),
      writeAndMove_readBack_of_startInvariant out hout]
    congr 2
    funext i
    exact writeAndMove_readBack_of_startInvariant (work i) (hwork i) _
  · exact move_idleDir_eq_of_startInvariant hinp
  · exact fun i => move_idleDir_eq_of_startInvariant (hwork i)
  · exact move_idleDir_eq_of_startInvariant hout

end TM

end Complexity
