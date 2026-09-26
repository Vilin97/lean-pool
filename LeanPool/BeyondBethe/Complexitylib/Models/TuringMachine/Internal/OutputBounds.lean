/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Internal

/-!
# Output-length bounds — proof internals

This module proves that a deterministic machine cannot produce more output
bits than the number of transitions it has taken. The key support lemma says
that an output cell beyond the initial head position plus the elapsed time is
unchanged.

Public statements are in `Complexitylib.Models.TuringMachine.OutputBounds`.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- One output-tape action leaves every cell other than the current head
unchanged. -/
private theorem output_cells_ne_of_step {tm : TM n} {c c' : Cfg n tm.Q}
    (hstep : tm.step c = some c') {j : ℕ} (hj : j ≠ c.output.head) :
    c'.output.cells j = c.output.cells j := by
  simp only [TM.step] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    rw [← hstep]
    simp only [Tape.move_cells, Tape.write]
    split
    · rfl
    · change Function.update c.output.cells c.output.head _ j = c.output.cells j
      rw [Function.update_of_ne hj]

/-- Cells beyond the output head's maximum reach are never changed. -/
theorem reachesIn_output_cells_far_internal {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      ∀ j, c.output.head + t < j → c'.output.cells j = c.output.cells j := by
  intro t
  induction t with
  | zero =>
      intro c c' hreach j _hj
      cases hreach
      rfl
  | succ t ih =>
      intro c c' hreach j hj
      cases hreach with
      | step hstep hrest =>
          next c'' =>
            have hhead : c''.output.head ≤ c.output.head + 1 := by
              have hbound := tm.output_head_reachesIn_bound
                (TM.reachesIn.step hstep TM.reachesIn.zero)
              simpa using hbound
            have hcell : c''.output.cells j = c.output.cells j :=
              output_cells_ne_of_step hstep (by omega)
            rw [ih hrest j (by omega), hcell]

/-- A run from an initial configuration needs at least one transition for
each bit present in its final output string. -/
theorem output_length_le_of_reachesIn_internal {tm : TM n} {x y : List Bool}
    {c' : Cfg n tm.Q} {t : ℕ}
    (hreach : tm.reachesIn t (tm.initCfg x) c')
    (hout : c'.output.HasOutput y) : y.length ≤ t := by
  by_contra hnle
  have ht : t < y.length := Nat.lt_of_not_ge hnle
  have hy : 0 < y.length := lt_of_le_of_lt (Nat.zero_le t) ht
  let i := y.length - 1
  have hi : i < y.length := by
    dsimp only [i]
    omega
  have hidx : i + 1 = y.length := by omega
  have hbit := hout.1 i hi
  have hfar := reachesIn_output_cells_far_internal hreach y.length (by simp; omega)
  have hblank : c'.output.cells y.length = Γ.blank := by
    rw [hfar]
    simp [Tape.init, hy.ne']
  rw [hidx, hblank] at hbit
  exact Γ.ofBool_ne_blank _ hbit.symm

/-- A time-bounded function computation has output length bounded by its
advertised running time. -/
theorem computesInTime_output_length_le_internal {tm : TM n}
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (h : tm.ComputesInTime f T) (x : List Bool) :
    (f x).length ≤ T x.length := by
  obtain ⟨c', t, ht, hreach, _hhalt, hout⟩ := h x
  exact (output_length_le_of_reachesIn_internal hreach hout).trans ht

end TM

end Complexity
