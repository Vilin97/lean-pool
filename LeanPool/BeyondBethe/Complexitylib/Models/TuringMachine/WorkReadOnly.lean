/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# Read-only work-tape certificates

`TM.WorkReadOnly tm idx` records the local syntactic fact that every transition
of `tm` writes the symbol already read on work tape `idx`. The head may move,
but valid tape contents are preserved through every finite run.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Every transition writes back the symbol read on the selected work tape. -/
def WorkReadOnly (tm : TM n) (idx : Fin n) : Prop :=
  ∀ state inputHead workHeads outputHead,
    state ≠ tm.qhalt →
    (tm.δ state inputHead workHeads outputHead).2.1 idx =
      readBackWrite (workHeads idx)

/-- A read-only transition preserves all cells of a valid selected tape. -/
theorem WorkReadOnly.cells_eq_of_step {tm : TM n} {idx : Fin n}
    (hreadonly : tm.WorkReadOnly idx) {c c' : Cfg n tm.Q}
    (hstep : tm.step c = some c')
    (hnostart : ∀ j, 1 ≤ j → (c.work idx).cells j ≠ Γ.start) :
    (c'.work idx).cells = (c.work idx).cells := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst c'
  change
    ((c.work idx).writeAndMove
      ((tm.δ c.state c.input.read (fun i => (c.work i).read)
        c.output.read).2.1 idx).toΓ
      ((tm.δ c.state c.input.read (fun i => (c.work i).read)
        c.output.read).2.2.2.2.1 idx)).cells = (c.work idx).cells
  rw [hreadonly _ _ _ _ hne]
  apply tape_readBackWrite_preserves
  by_cases hhead : (c.work idx).head = 0
  · exact Or.inl hhead
  · exact Or.inr (by
      apply hnostart
      omega)

/-- A read-only work tape retains its complete cell function through an exact
finite run. -/
theorem WorkReadOnly.cells_eq_of_reachesIn {tm : TM n} {idx : Fin n}
    (hreadonly : tm.WorkReadOnly idx) {time : ℕ} {start final : Cfg n tm.Q}
    (hreach : tm.reachesIn time start final)
    (hnostart : ∀ j, 1 ≤ j → (start.work idx).cells j ≠ Γ.start) :
    (final.work idx).cells = (start.work idx).cells := by
  induction hreach with
  | zero => rfl
  | step hstep _ ih =>
      have hcells := hreadonly.cells_eq_of_step hstep hnostart
      apply Eq.trans (ih ?_) hcells
      intro j hj
      rw [hcells]
      exact hnostart j hj

/-- Sequential composition preserves a shared read-only work tape. -/
theorem WorkReadOnly.seqTM {first second : TM n} {idx : Fin n}
    (hfirst : first.WorkReadOnly idx)
    (hsecond : second.WorkReadOnly idx) :
    (seqTM first second).WorkReadOnly idx := by
  intro state inputHead workHeads outputHead hstate
  cases state with
  | inl state =>
      unfold Complexity.TM.seqTM
      dsimp only
      split
      · rfl
      · next hne => exact hfirst state inputHead workHeads outputHead hne
  | inr state =>
      unfold Complexity.TM.seqTM
      dsimp only
      split
      · next heq =>
          subst state
          exact (hstate rfl).elim
      · next hne => exact hsecond state inputHead workHeads outputHead hne

end TM

end Complexity
