/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.RewindList
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.WipeLoop

/-!
# Resetting a list of tapes to blank, content-agnostically

The full reset an opaque machine's scratch needs between calls: park everything
(`TM.parkAll_hoareTime`), rewind every targeted tape to cell `1`
(`TM.rewindList_hoareTime`), then wipe `H` cells forward from there
(`TM.wipeLoop_hoareTime`). A fuel register disjoint from the targets drives the
wipe and is left exactly as it started.

## Main results

- `TM.resetTapesTM` — the composite reset machine
- `TM.resetTapesTM_hoareTime` / `TM.resetTapesTM_hoareTime_of_bounds` — its contract
-/


public section

namespace Complexity

namespace TM

/-- **Resetting a list of tapes.** Regardless of their current content or head
position (bounded by `H`), every tape in `targets` ends up blanked from cell
`1` through cell `H`, with its tail beyond cell `H` untouched; the fuel
register `r` (disjoint from `targets`) and every other tape are exactly as
they were. -/
theorem resetTapes_hoareTime {n : ℕ} (targets : List (Fin n)) (hnodup : targets.Nodup)
    (r : Fin n) (hr : r ∉ targets) (H : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinpSI : Tape.StartInvariant inp₀) (hinpP : Parked inp₀)
    (hout0 : out₀ = (Tape.init []).move Dir3.right)
    (hworkSI : ∀ j, j ≠ r → Tape.StartInvariant (work₀ j))
    (htargetHead : ∀ j, j ∈ targets → (work₀ j).head ≤ H)
    (hworkR : work₀ r = regTape H)
    (hother : ∀ j, j ≠ r → j ∉ targets → Parked (work₀ j)) :
    (seqTM (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM)))
        (forRegTM (wipeStepTM targets) r)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = wipedTape (⟨1, (work₀ j).cells⟩ : Tape) H) ∧
        work r = regTape H ∧
        (∀ j, j ≠ r → j ∉ targets → work j = work₀ j))
      (targets.length * (H + 4) + H * 4 + 8) := by
  have hregParked : Parked (regTape H) :=
    ⟨le_refl 1, fun i hi => by
      show regCells H i ≠ Γ.start
      simp only [regCells]; split
      · omega
      · split <;> decide⟩
  have houtSI : Tape.StartInvariant out₀ := by
    rw [hout0]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [Tape.move_cells]; exact Tape.init_cells_zero []
    · rw [Tape.move_cells, show j = (j - 1) + 1 from by omega,
        Tape.init_cells_ge [] (j - 1) (by simp)]
      decide
  have houtP : Parked out₀ := by rw [hout0]; exact parked_parkedBlank
  have hworkSI' : ∀ j, Tape.StartInvariant (work₀ j) := by
    intro j
    by_cases hjr : j = r
    · subst hjr; rw [hworkR]; exact ⟨rfl, hregParked.2⟩
    · exact hworkSI j hjr
  set workA : Fin n → Tape := fun j => (⟨max (work₀ j).head 1, (work₀ j).cells⟩ : Tape)
    with hworkA
  have hAP : ∀ j, Parked (workA j) := fun j => ⟨le_max_right _ _, fun i hi => (hworkSI' j).2 i hi⟩
  have hAtarget : ∀ j, j ∈ targets → (workA j).cells 0 = Γ.start ∧ (workA j).head ≤ H + 1 := by
    intro j hj
    refine ⟨(hworkSI' j).1, ?_⟩
    show max (work₀ j).head 1 ≤ H + 1
    have := htargetHead j hj
    omega
  have hA := parkAll_hoareTime inp₀ work₀ out₀ hinpSI hworkSI' houtSI
  have hinpAeq : (⟨max inp₀.head 1, inp₀.cells⟩ : Tape) = inp₀ :=
    Tape.ext (by show max inp₀.head 1 = inp₀.head; have := hinpP.1; omega) rfl
  have houtAeq : (⟨max out₀.head 1, out₀.cells⟩ : Tape) = out₀ :=
    Tape.ext (by show max out₀.head 1 = out₀.head; have := houtP.1; omega) rfl
  have hApost_imp : ∀ inp work out,
      (inp = (⟨max inp₀.head 1, inp₀.cells⟩ : Tape) ∧
        (∀ i, work i = workA i) ∧ out = (⟨max out₀.head 1, out₀.cells⟩ : Tape)) →
      (inp = inp₀ ∧ work = workA ∧ out = out₀) := by
    rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi.trans hinpAeq, funext hw, ho.trans houtAeq⟩
  have hA' := hA.strengthen_post hApost_imp
  have hB0 := rewindList_hoareTime targets hnodup (H + 1) inp₀ workA out₀ hinpP houtP hAP hAtarget
  have hB : (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM))).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = (⟨1, (work₀ j).cells⟩ : Tape)) ∧
        (∀ j, j ∉ targets → work j = workA j))
      (1 + 1 + targets.length * ((H + 1) + 3) + 1) := by
    refine seqTM_hoareTime skipTM (bigSeqTM (targets.map rewindWorkTM)) hA' ?_ hB0
    rintro inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨transitionInput_eq_self hinpP.read_ne_start, ?_,
      transitionTape_eq_self houtP.read_ne_start⟩
    funext i
    exact transitionTape_eq_self (hAP i).read_ne_start
  set workC : Fin n → Tape := fun j => if j ∈ targets then (⟨1, (work₀ j).cells⟩ : Tape)
    else work₀ j with hworkC
  have hCother : ∀ j, j ≠ r → Parked (workC j) := by
    intro j hjr
    rw [hworkC]
    dsimp only
    split
    · next hjt => exact ⟨le_refl 1, (hworkSI' j).2⟩
    · next hjt => exact hother j hjr hjt
  have hC0 := wipeLoop_hoareTime targets r hr H inp₀ workC hinpP hCother
  have hworkeq : ∀ (work : Fin n → Tape),
      (∀ j, j ∈ targets → work j = (⟨1, (work₀ j).cells⟩ : Tape)) →
      (∀ j, j ∉ targets → work j = workA j) →
      work = Function.update workC r (regTape H) := by
    intro work hts hnts
    funext j
    by_cases hjr : j = r
    · rw [hjr, Function.update_self]
      rw [hnts r hr]
      show (⟨max (work₀ r).head 1, (work₀ r).cells⟩ : Tape) = regTape H
      rw [hworkR]
      exact Tape.ext (by show max 1 1 = 1; omega) (by rw [regT_cells])
    · rw [Function.update_of_ne hjr]
      by_cases hjt : j ∈ targets
      · rw [hts j hjt, hworkC]; simp [hjt]
      · rw [hnts j hjt, hworkC]
        simp only [hjt, if_false]
        exact Tape.ext (by
          show max (work₀ j).head 1 = (work₀ j).head
          have := (hother j hjr hjt).1
          omega) rfl
  have hread : ∀ (work : Fin n → Tape),
      (∀ j, j ∈ targets → work j = (⟨1, (work₀ j).cells⟩ : Tape)) →
      (∀ j, j ∉ targets → work j = workA j) →
      ∀ j, (work j).read ≠ Γ.start := by
    intro work hts hnts j
    by_cases hjt : j ∈ targets
    · rw [hts j hjt]
      exact (hworkSI' j).2 1 le_rfl
    · rw [hnts j hjt]
      exact (hAP j).read_ne_start
  have htrans : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape),
      (inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = (⟨1, (work₀ j).cells⟩ : Tape)) ∧
        (∀ j, j ∉ targets → work j = workA j)) →
      transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = Function.update workC r (regTape H) ∧
        transitionTape out = (Tape.init []).move Dir3.right := by
    rintro inp work out ⟨hi, ho, hts, hnts⟩
    refine ⟨by rw [hi]; exact transitionInput_eq_self hinpP.read_ne_start,
      ?_, by rw [ho, transitionTape_eq_self houtP.read_ne_start]; exact hout0⟩
    rw [← hworkeq work hts hnts]
    funext j
    exact transitionTape_eq_self (hread work hts hnts j)
  have hFull := seqTM_hoareTime (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM)))
    (forRegTM (wipeStepTM targets) r) hB htrans hC0
  have hpost_imp : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape),
      (inp = inp₀ ∧
        work = Function.update (fun j => if j ∈ targets then wipedTape (workC j) H else workC j)
          r (regTape H) ∧
        out = (Tape.init []).move Dir3.right) →
      (inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = wipedTape (⟨1, (work₀ j).cells⟩ : Tape) H) ∧
        work r = regTape H ∧
        (∀ j, j ≠ r → j ∉ targets → work j = work₀ j)) := by
    rintro inp work out ⟨hi, hw, ho⟩
    refine ⟨hi, ho.trans hout0.symm, fun j hjt => ?_, ?_, fun j hjr hjt => ?_⟩
    · rw [hw, Function.update_of_ne (fun h => hr (by rw [h] at hjt; exact hjt)),
        if_pos hjt, hworkC]
      simp [hjt]
    · rw [hw, Function.update_self]
    · rw [hw, Function.update_of_ne hjr, hworkC]
      simp [hjt]
  refine (hFull.strengthen_post hpost_imp).mono_bound ?_
  ring_nf
  omega

/-- The composite reset machine: park everything, rewind the targets, wipe
`H` cells forward, then rewind the targets again. -/
def resetTapesTM {n : ℕ} (targets : List (Fin n)) (r : Fin n) : TM n :=
  seqTM (seqTM (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM)))
      (forRegTM (wipeStepTM targets) r))
    (bigSeqTM (targets.map rewindWorkTM))

/-- **The full reset.** Every tape in `targets` whose content is confined to
cells `1 … H` — no matter *where* in that range, and no matter where its head
currently sits — ends up literally blank and parked at cell `1`. The fuel
register `r` and all other tapes are returned exactly as they were. -/
theorem resetTapesTM_hoareTime {n : ℕ} (targets : List (Fin n)) (hnodup : targets.Nodup)
    (r : Fin n) (hr : r ∉ targets) (H : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinpSI : Tape.StartInvariant inp₀) (hinpP : Parked inp₀)
    (hout0 : out₀ = (Tape.init []).move Dir3.right)
    (hworkSI : ∀ j, j ≠ r → Tape.StartInvariant (work₀ j))
    (htargetHead : ∀ j, j ∈ targets → (work₀ j).head ≤ H)
    (htargetFar : ∀ j, j ∈ targets → ∀ i, H < i → (work₀ j).cells i = Γ.blank)
    (hworkR : work₀ r = regTape H)
    (hother : ∀ j, j ≠ r → j ∉ targets → Parked (work₀ j)) :
    (resetTapesTM targets r).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = (Tape.init []).move Dir3.right) ∧
        work r = regTape H ∧
        (∀ j, j ≠ r → j ∉ targets → work j = work₀ j))
      (targets.length * (H + 4) + H * 4 + 8 + 1 + (targets.length * (H + 4) + 1)) := by
  have houtP : Parked out₀ := by rw [hout0]; exact parked_parkedBlank
  have hregParked : Parked (regTape H) :=
    ⟨le_refl 1, fun i hi => by
      show regCells H i ≠ Γ.start
      simp only [regCells]; split
      · omega
      · split <;> decide⟩
  -- the wipe's exact effect on a targeted tape, spelled out
  have hwiped : ∀ j, j ∈ targets →
      wipedTape (⟨1, (work₀ j).cells⟩ : Tape) H = (⟨H + 1, (Tape.init []).cells⟩ : Tape) := by
    intro j hj
    refine wipedTape_eq_blank H rfl ?_ (fun i hi => htargetFar j hj i hi)
    exact (hworkSI j (fun h => hr (h ▸ hj))).1
  -- the tape family after the wipe phase
  set workD : Fin n → Tape := fun j =>
    if j ∈ targets then (⟨H + 1, (Tape.init []).cells⟩ : Tape)
    else if j = r then regTape H else work₀ j with hworkD
  have hDP : ∀ j, Parked (workD j) := by
    intro j
    rw [hworkD]
    dsimp only
    split
    · exact ⟨show 1 ≤ H + 1 by omega,
        fun i hi => by rw [initNil_cells, if_neg (by omega)]; decide⟩
    · split
      · exact hregParked
      · next hjt hjr => exact hother j hjr hjt
  have hDtarget : ∀ j, j ∈ targets →
      (workD j).cells 0 = Γ.start ∧ (workD j).head ≤ H + 1 := by
    intro j hj
    rw [hworkD]
    simp only [if_pos hj]
    exact ⟨by rw [initNil_cells, if_pos rfl], le_refl _⟩
  have hfirst := resetTapes_hoareTime targets hnodup r hr H inp₀ work₀ out₀ hinpSI hinpP
    hout0 hworkSI htargetHead hworkR hother
  have hsecond := rewindList_hoareTime targets hnodup (H + 1) inp₀ workD out₀ hinpP houtP
    hDP hDtarget
  refine seqTM_hoareTime _ _ hfirst ?_ hsecond |>.strengthen_post ?_
  · -- the boundary: everything is parked, so the seam is the identity
    rintro inp work out ⟨hi, ho, hts, hR, hrest⟩
    have hworkD_eq : work = workD := by
      funext j
      by_cases hjt : j ∈ targets
      · rw [hts j hjt, hwiped j hjt, hworkD]; simp [hjt]
      · by_cases hjr : j = r
        · rw [hjr, hR, hworkD]; simp [hr]
        · rw [hrest j hjr hjt, hworkD]; simp [hjt, hjr]
    subst hworkD_eq
    refine ⟨by rw [hi]; exact transitionInput_eq_self hinpP.read_ne_start, ?_,
      by rw [ho]; exact transitionTape_eq_self houtP.read_ne_start⟩
    funext j
    exact transitionTape_eq_self (hDP j).read_ne_start
  · rintro inp work out ⟨hi, ho, hts, hnts⟩
    refine ⟨hi, ho, fun j hj => ?_, ?_, fun j hjr hjt => ?_⟩
    · rw [hts j hj, hworkD]
      simp only [if_pos hj]
      rfl
    · rw [hnts r hr, hworkD]
      simp [hr]
    · rw [hnts j hjt, hworkD]
      simp [hjt, hjr]

/-- **The reset, keyed on bounds rather than on a named tape family.** The
tapes an opaque machine leaves behind are only known through bounds, never as
a closed form, so this is the shape the loop body actually needs: the exact
starting family is instantiated inside the proof. -/
theorem resetTapesTM_hoareTime_of_bounds {n : ℕ} (targets : List (Fin n))
    (hnodup : targets.Nodup) (r : Fin n) (hr : r ∉ targets) (H : ℕ)
    (inp₀ : Tape) (extras : Fin n → Tape) (out₀ : Tape)
    (hinpSI : Tape.StartInvariant inp₀) (hinpP : Parked inp₀)
    (hout0 : out₀ = (Tape.init []).move Dir3.right)
    (hextraP : ∀ j, j ≠ r → j ∉ targets → Parked (extras j)) :
    (resetTapesTM targets r).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ≠ r → Tape.StartInvariant (work j)) ∧
        (∀ j, j ∈ targets → (work j).head ≤ H ∧ ∀ i, H < i → (work j).cells i = Γ.blank) ∧
        work r = regTape H ∧
        (∀ j, j ≠ r → j ∉ targets → work j = extras j))
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = (Tape.init []).move Dir3.right) ∧
        work r = regTape H ∧
        (∀ j, j ≠ r → j ∉ targets → work j = extras j))
      (targets.length * (H + 4) + H * 4 + 8 + 1 + (targets.length * (H + 4) + 1)) := by
  intro inp work out hpre
  obtain ⟨hi, ho, hSI, hbnd, hR, hext⟩ := hpre
  rw [hi, ho]
  obtain ⟨c', t, ht, hreach, hhalt, hi', ho', hts, hR', hrest⟩ :=
    resetTapesTM_hoareTime targets hnodup r hr H inp₀ work out₀ hinpSI hinpP hout0 hSI
      (fun j hj => (hbnd j hj).1) (fun j hj i hii => (hbnd j hj).2 i hii) hR
      (fun j hjr hjt => by rw [hext j hjr hjt]; exact hextraP j hjr hjt)
      inp₀ work out₀ ⟨rfl, rfl, rfl⟩
  exact ⟨c', t, ht, hreach, hhalt, hi', ho', hts, hR',
    fun j hjr hjt => (hrest j hjr hjt).trans (hext j hjr hjt)⟩

end TM

end Complexity
