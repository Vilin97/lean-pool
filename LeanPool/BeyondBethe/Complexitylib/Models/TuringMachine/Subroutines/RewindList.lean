/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Mathlib.Tactic.Ring
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.EmitSeq
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ParkAll

/-!
# Rewinding a list of tapes, one at a time

Rewinding cannot be done in one uniform pass the way wiping can:
`TM.rewindWorkTM` bounces at `▷` rather than saturating there, so moving
everyone left the same number of times oscillates. Doing it one tape at a time
via `TM.bigSeqTM` works once every tape has been parked once
(`TM.parkAll_hoareTime`).

## Main results

- `TM.rewindList_hoareTime` — rewind every targeted tape to cell `1`
-/


@[expose] public section

namespace Complexity

namespace TM

/-- **Rewinding a list of tapes, one at a time.** Given a uniform head bound
`B` and that *every* tape (not just the targets) is already `Parked` — the
state after `parkAll_hoareTime` — sequentially rewinding each named tape
lands it at cell `1` with its cells unchanged, leaving every other tape
(targeted-but-not-yet-reached, or never targeted) exactly as it was. -/
theorem rewindList_hoareTime {n : ℕ} :
    ∀ (targets : List (Fin n)), targets.Nodup →
    ∀ (B : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape),
    Parked inp₀ → Parked out₀ → (∀ j, Parked (work₀ j)) →
    (∀ j, j ∈ targets → (work₀ j).cells 0 = Γ.start ∧ (work₀ j).head ≤ B) →
    (bigSeqTM (targets.map rewindWorkTM)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = ⟨1, (work₀ j).cells⟩) ∧
        (∀ j, j ∉ targets → work j = work₀ j))
      (targets.length * (B + 3) + 1) := by
  intro targets
  induction targets with
  | nil =>
    intro _ B inp₀ work₀ out₀ hinp hout hwork _
    simp only [List.map_nil, List.length_nil, Nat.zero_mul, Nat.zero_add]
    refine (skipTM_hoareTime_frame inp₀ work₀ out₀ hinp hwork hout).strengthen_post ?_
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, nofun, fun j _ => rfl⟩
  | cons t ts ih =>
    intro hnodup B inp₀ work₀ out₀ hinp hout hwork htarget
    have htnts : t ∉ ts := (List.nodup_cons.mp hnodup).1
    have htsnodup : ts.Nodup := (List.nodup_cons.mp hnodup).2
    have hP : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
        (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
        ((work t).cells = (work₀ t).cells ∧
          inp = inp₀ ∧ out = out₀ ∧ ∀ j, j ≠ t → work j = work₀ j) →
        (work' t).cells = (work t).cells → (work' t).head = 1 →
        (∀ j, j ≠ t → work' j = work j) →
        inp' = inp → out'.cells = out.cells → out'.head = out.head →
        ((work' t).cells = (work₀ t).cells ∧
          inp' = inp₀ ∧ out' = out₀ ∧ ∀ j, j ≠ t → work' j = work₀ j) := by
      rintro inp work out inp' work' out' ⟨hcellsP, rfl, rfl, hrest⟩ hcells' _ hkeep rfl
        hout'c hout'h
      exact ⟨hcells'.trans hcellsP, rfl, Tape.ext hout'h hout'c,
        fun j hjt => (hkeep j hjt).trans (hrest j hjt)⟩
    have h1 := rewindWorkTM_hoareTime_frame t B hP
    have h1' := h1.weaken_pre
      (show (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀) ≤ _ by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        exact ⟨(htarget t (by simp)).1, fun j hj => (hwork t).2 j hj, (htarget t (by simp)).2,
          hinp.read_ne_start, hout.read_ne_start, hout.1,
          fun i _ => ⟨(hwork i).read_ne_start, (hwork i).1⟩, rfl, rfl, rfl, fun _ _ => rfl⟩)
    set work₁ : Fin n → Tape := Function.update work₀ t (⟨1, (work₀ t).cells⟩ : Tape) with hwork₁
    have hwork₁P : ∀ j, Parked (work₁ j) := by
      intro j
      by_cases hjt : j = t
      · rw [hjt, hwork₁, Function.update_self]
        exact ⟨le_refl 1, fun i hi => (hwork t).2 i hi⟩
      · rw [hwork₁, Function.update_of_ne hjt]; exact hwork j
    have hwork₁target : ∀ j, j ∈ ts → (work₁ j).cells 0 = Γ.start ∧ (work₁ j).head ≤ B := by
      intro j hj
      have hjt : j ≠ t := by rintro rfl; exact htnts hj
      rw [hwork₁, Function.update_of_ne hjt]
      exact htarget j (by simp [hj])
    have ih' := ih htsnodup B inp₀ work₁ out₀ hinp hout hwork₁P hwork₁target
    have hread_t : ∀ (work : Fin n → Tape), (work t).cells = (work₀ t).cells →
        (work t).head = 1 → (work t).read ≠ Γ.start := by
      intro work hcells hhead
      show (work t).cells (work t).head ≠ Γ.start
      rw [hhead, hcells]
      exact (hwork t).2 1 le_rfl
    have h2 : (bigSeqTM ((t :: ts).map rewindWorkTM)).HoareTime
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
          (∀ j, j ∈ ts → work j = ⟨1, (work₁ j).cells⟩) ∧
          (∀ j, j ∉ ts → work j = work₁ j))
        ((B + 2) + 1 + (ts.length * (B + 3) + 1)) := by
      simp only [List.map_cons, bigSeqTM]
      refine seqTM_hoareTime (rewindWorkTM t) (bigSeqTM (ts.map rewindWorkTM)) h1' ?_ ih'
      rintro inp work out ⟨hhead1, hcellsP, hpinp, hpout, hprest⟩
      have hreadt : (work t).read ≠ Γ.start := hread_t work hcellsP hhead1
      have ht1 : transitionInput inp = inp₀ := by
        rw [hpinp]; exact transitionInput_eq_self hinp.read_ne_start
      have ht3 : transitionTape out = out₀ := by
        rw [hpout]; exact transitionTape_eq_self hout.read_ne_start
      have ht2 : (fun i => transitionTape (work i)) = work₁ := by
        funext j
        by_cases hjt : j = t
        · rw [hjt, transitionTape_eq_self hreadt, hwork₁, Function.update_self]
          exact Tape.ext hhead1 hcellsP
        · rw [hprest j hjt, transitionTape_eq_self (hwork j).read_ne_start,
            hwork₁, Function.update_of_ne hjt]
      rw [ht1, ht2, ht3]
      exact ⟨rfl, rfl, rfl⟩
    refine h2.consequence (fun _ _ _ h => h)
      (fun inp work out ⟨hinpeq, houteq, hts, hnts⟩ => ?_)
      (by rw [List.length_cons]; ring_nf; omega)
    refine ⟨hinpeq, houteq, fun j hj => ?_, fun j hj => ?_⟩
    · rw [List.mem_cons] at hj
      rcases hj with hjeqt | hjts
      · rw [hnts j (hjeqt ▸ htnts), hjeqt, hwork₁, Function.update_self]
      · rw [hts j hjts]
        congr 1
        have hjt : j ≠ t := fun h => htnts (h ▸ hjts)
        rw [hwork₁, Function.update_of_ne hjt]
    · have hjt : j ≠ t := fun h => hj (List.mem_cons.mpr (Or.inl h))
      have hjts : j ∉ ts := fun h => hj (List.mem_cons.mpr (Or.inr h))
      rw [hnts j hjts, hwork₁, Function.update_of_ne hjt]

end TM

end Complexity
