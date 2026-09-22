/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.ForReg
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.WipeStep

/-!
# The wipe loop

`TM.forRegTM` drives a body an exact number of times off a dedicated unary fuel
register. Running `TM.wipeStepTM` through it, fueled by a register holding `v`
marks unrelated to any targeted tape's content, blanks the leading `v` cells of
every target whatever was there.

## Main results

- `TM.wipedTape` — the closed form of `v` wipe steps applied to a tape
- `TM.wipeLoop_hoareTime` — the loop's contract
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Wipe-step applied `i` times to `t`, in closed form. -/
def wipedTape (t : Tape) (i : ℕ) : Tape :=
  (fun s : Tape => s.writeAndMove Γw.blank.toΓ Dir3.right)^[i] t

@[simp] theorem wipedTape_zero (t : Tape) : wipedTape t 0 = t := rfl

theorem wipedTape_succ (t : Tape) (i : ℕ) :
    wipedTape t (i + 1) = (wipedTape t i).writeAndMove Γw.blank.toΓ Dir3.right :=
  Function.iterate_succ_apply' _ i t

/-- Wiping advances the head one cell per step. -/
theorem wipedTape_head (t : Tape) (i : ℕ) : (wipedTape t i).head = t.head + i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [wipedTape_succ]
      show (((wipedTape t i).write Γw.blank.toΓ).move Dir3.right).head = t.head + (i + 1)
      rw [show (((wipedTape t i).write Γw.blank.toΓ).move Dir3.right).head
            = ((wipedTape t i).write Γw.blank.toΓ).head + 1 from rfl,
        Tape.write_head, ih]
      omega

/-- **What wiping does.** From a head parked at cell `1`, wiping `H` times
blanks exactly cells `1 … H` and leaves every other cell alone. -/
theorem wipedTape_cells_of_head_one {t : Tape} (hh : t.head = 1) (H j : ℕ) :
    (wipedTape t H).cells j = if 1 ≤ j ∧ j ≤ H then Γ.blank else t.cells j := by
  induction H with
  | zero => rw [wipedTape_zero, ite_eq_right (by omega : ¬(1 ≤ j ∧ j ≤ 0))]
  | succ H ih =>
      have hheadH : (wipedTape t H).head = H + 1 := by rw [wipedTape_head, hh]; omega
      rw [wipedTape_succ]
      show (((wipedTape t H).write Γw.blank.toΓ).move Dir3.right).cells j = _
      rw [Tape.move_cells, Tape.write, ite_eq_right (by rw [hheadH]; omega)]
      show Function.update (wipedTape t H).cells (wipedTape t H).head Γw.blank.toΓ j = _
      rw [hheadH]
      by_cases hj : j = H + 1
      · rw [hj, Function.update_self, ite_eq_left ⟨by omega, by omega⟩]
        rfl
      · rw [Function.update_of_ne hj, ih]
        by_cases hc : 1 ≤ j ∧ j ≤ H
        · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, by omega⟩]
        · have hc' : ¬(1 ≤ j ∧ j ≤ H + 1) := by
            rintro ⟨h1, h2⟩
            exact hc ⟨h1, by omega⟩
          rw [ite_eq_right hc, ite_eq_right hc']

/-- The canonical blank tape's cells, spelled out. -/
theorem initNil_cells (j : ℕ) :
    (Tape.init ([] : List Γ)).cells j = if j = 0 then Γ.start else Γ.blank := by
  cases j with
  | zero => exact Tape.init_cells_zero []
  | succ i => rw [Tape.init_cells_ge [] i (by simp), ite_eq_right (Nat.succ_ne_zero i)]

/-- **Wiping really blanks the tape.** A tape parked at cell `1` whose content
is confined to cells `1 … H` becomes literally the blank tape (head at `H + 1`)
after `H` wipe steps — this is where the content-agnostic wipe pays off: no
assumption is made about *where* inside `1 … H` the nonblank cells sit. -/
theorem wipedTape_eq_blank {t : Tape} (H : ℕ) (hh : t.head = 1)
    (h0 : t.cells 0 = Γ.start) (hfar : ∀ j, H < j → t.cells j = Γ.blank) :
    wipedTape t H = (⟨H + 1, (Tape.init ([] : List Γ)).cells⟩ : Tape) := by
  refine Tape.ext (by rw [wipedTape_head, hh]; show 1 + H = H + 1; omega) (funext fun j => ?_)
  rw [wipedTape_cells_of_head_one hh, initNil_cells]
  by_cases hj0 : j = 0
  · rw [hj0, ite_eq_right (by omega : ¬(1 ≤ 0 ∧ 0 ≤ H)), ite_eq_left rfl, h0]
  · rw [ite_eq_right hj0]
    by_cases hc : 1 ≤ j ∧ j ≤ H
    · rw [ite_eq_left hc]
    · rw [ite_eq_right hc, hfar j (by omega)]

/-- Wiping preserves `Parked`-ness: the head only advances, and every
written or untouched cell beyond the marker stays off `▷`. -/
theorem wipedTape_parked {t : Tape} (h : Parked t) (i : ℕ) : Parked (wipedTape t i) := by
  induction i with
  | zero => exact h
  | succ i ih =>
      rw [wipedTape_succ]
      have hheq : (wipedTape t i).writeAndMove Γw.blank.toΓ Dir3.right =
          ((wipedTape t i).write Γw.blank.toΓ).move Dir3.right := rfl
      have hhead_ne : (wipedTape t i).head ≠ 0 := by
        have := ih.1; omega
      refine ⟨?_, fun j hj => ?_⟩
      · rw [hheq]
        show 1 ≤ ((wipedTape t i).write Γw.blank.toΓ).head + 1
        omega
      · rw [hheq, Tape.move_cells]
        simp only [Tape.write, ite_eq_right hhead_ne]
        show Function.update (wipedTape t i).cells (wipedTape t i).head Γw.blank.toΓ j ≠ Γ.start
        by_cases hje : j = (wipedTape t i).head
        · rw [hje, Function.update_self]; decide
        · rw [Function.update_of_ne hje]; exact ih.2 j hj

/-- A fresh output tape (`(Tape.init []).move Dir3.right`) is `Parked`. -/
theorem parked_parkedBlank : Parked ((Tape.init []).move Dir3.right) := by
  refine ⟨le_refl 1, fun j hj => ?_⟩
  rw [Tape.move_cells, show j = (j - 1) + 1 from by omega,
    Tape.init_cells_ge [] (j - 1) (by simp)]
  decide

/-- A fresh output tape satisfies the empty output accumulator. -/
theorem outAcc_nil_of_parkedBlank :
    OutAcc [] ((Tape.init []).move Dir3.right) := by
  refine ⟨rfl, ?_, nofun, fun j hj => ?_⟩
  · rw [Tape.move_cells]; exact Tape.init_cells_zero []
  · rw [Tape.move_cells, show j = (j - 1) + 1 from by omega,
      Tape.init_cells_ge [] (j - 1) (by simp)]

/-- The only tape satisfying the empty output accumulator is the fresh
parked blank tape. -/
theorem eq_parkedBlank_of_outAcc_nil {t : Tape} (h : OutAcc [] t) :
    t = (Tape.init []).move Dir3.right := by
  obtain ⟨hhead, hcell0, -, htail⟩ := h
  refine Tape.ext ?_ ?_
  · rw [hhead]; rfl
  · rw [Tape.move_cells]
    funext j
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0; rw [hcell0, Tape.init_cells_zero]
    · rw [htail j (by simpa using! hj1), show j = (j - 1) + 1 from by omega,
        Tape.init_cells_ge [] (j - 1) (by simp)]

/-- The register-shaped tape at iteration `i` is `Parked`. -/
theorem regIterCells_parked (v i : ℕ) : Parked (⟨i + 2, regCells v⟩ : Tape) := by
  refine ⟨show 1 ≤ i + 2 by omega, fun j _ => ?_⟩
  show regCells v j ≠ Γ.start
  simp only [regCells]
  split
  · omega
  · split <;> decide

/-- **The wipe loop.** Fueled by a register at `r` holding `v` marks (`r`
disjoint from `targets`), `forRegTM (wipeStepTM targets) r` blanks the leading
`v` cells of every tape in `targets`, leaving every other tape — including the
fuel register itself — exactly as it was. -/
theorem wipeLoop_hoareTime {n : ℕ} (targets : List (Fin n)) (r : Fin n)
    (hr : r ∉ targets) (v : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (hinp₀ : Parked inp₀)
    (hother : ∀ j, j ≠ r → Parked (work₀ j)) :
    (forRegTM (wipeStepTM targets) r).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update work₀ r (regTape v) ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update
          (fun j => if j ∈ targets then wipedTape (work₀ j) v else work₀ j) r (regTape v) ∧
        out = (Tape.init []).move Dir3.right)
      (v * 3 + (v + 2)) := by
  set w : ℕ → Fin n → Tape := fun i j =>
    if j = r then regTape v else if j ∈ targets then wipedTape (work₀ j) i else work₀ j
    with hw
  have hw0 : w 0 = Function.update work₀ r (regTape v) := by
    funext j
    by_cases hjr : j = r
    · subst hjr; simp [hw, Function.update_self]
    · rw [Function.update_of_ne hjr]
      simp only [hw, ite_eq_right hjr]
      split
      · rfl
      · rfl
  have hwv : w v = Function.update
      (fun j => if j ∈ targets then wipedTape (work₀ j) v else work₀ j) r (regTape v) := by
    funext j
    by_cases hjr : j = r
    · subst hjr; simp [hw, Function.update_self]
    · rw [Function.update_of_ne hjr]; simp [hw, ite_eq_right hjr]
  have hwork_parked : ∀ i j, j ≠ r → Parked (w i j) := by
    intro i j hjr
    by_cases hjt : j ∈ targets
    · simp only [hw, ite_eq_right hjr, ite_eq_left hjt]
      exact wipedTape_parked (hother j hjr) i
    · simp only [hw, ite_eq_right hjr, ite_eq_right hjt]
      exact hother j hjr
  have hbody : ∀ i, i < v → (wipeStepTM targets).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (w i) r (⟨i + 2, regCells v⟩ : Tape) ∧ OutAcc [] out)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (w (i + 1)) r (⟨i + 2, regCells v⟩ : Tape) ∧ OutAcc [] out)
      1 := by
    intro i _
    set W : Fin n → Tape := Function.update (w i) r (⟨i + 2, regCells v⟩ : Tape) with hW
    have hcopy := wipeStepTM_hoareTime targets inp₀ W ((Tape.init []).move Dir3.right)
      hinp₀ parked_parkedBlank
      (fun k _ => by
        by_cases hkr : k = r
        · subst hkr; rw [hW, Function.update_self]; exact regIterCells_parked v i
        · rw [hW, Function.update_of_ne hkr]; exact hwork_parked i k hkr)
    refine (hcopy.weaken_pre ?_).strengthen_post ?_
    · rintro inp work out ⟨rfl, rfl, hout⟩
      exact ⟨rfl, rfl, eq_parkedBlank_of_outAcc_nil hout⟩
    · rintro inp work out ⟨rfl, hout, hwork⟩
      refine ⟨rfl, ?_, hout ▸ outAcc_nil_of_parkedBlank⟩
      funext j
      rw [hwork j]
      by_cases hjr : j = r
      · subst hjr
        rw [ite_eq_right hr, hW, Function.update_self, Function.update_self]
      · by_cases hjt : j ∈ targets
        · rw [ite_eq_left hjt]
          have hWj : W j = wipedTape (work₀ j) i := by
            rw [hW, Function.update_of_ne hjr, hw]; simp [ite_eq_right hjr, ite_eq_left hjt]
          have hRj : Function.update (w (i + 1)) r (⟨i + 2, regCells v⟩ : Tape) j =
              wipedTape (work₀ j) (i + 1) := by
            rw [Function.update_of_ne hjr, hw]; simp [ite_eq_right hjr, ite_eq_left hjt]
          rw [hWj, hRj, wipedTape_succ]
        · rw [ite_eq_right hjt]
          have hWj : W j = work₀ j := by
            rw [hW, Function.update_of_ne hjr, hw]; simp [ite_eq_right hjr, ite_eq_right hjt]
          have hRj : Function.update (w (i + 1)) r (⟨i + 2, regCells v⟩ : Tape) j = work₀ j := by
            rw [Function.update_of_ne hjr, hw]; simp [ite_eq_right hjr, ite_eq_right hjt]
          rw [hWj, hRj]
  have key := forRegTM_hoareTime (wipeStepTM targets) r v inp₀ w (fun _ => []) 1 hinp₀
    (fun i => by simp [hw]) hwork_parked hbody
  refine key.consequence
    (fun inp work out ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, hw0], h3 ▸ outAcc_nil_of_parkedBlank⟩)
    (fun inp work out ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, hwv], (eq_parkedBlank_of_outAcc_nil h3)⟩)
    (by omega)

end TM

end Complexity
