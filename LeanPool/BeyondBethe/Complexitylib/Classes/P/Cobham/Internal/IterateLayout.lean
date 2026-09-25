/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Apply
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.CopyToVirtualInput

/-!
# The bounded-iteration machine's tape layout — proof internals

The tape layout and phase contracts that
`Complexitylib.Classes.P.Cobham.Internal.Iterate` assembles into the
bounded-iteration machine: two unary fuel registers (one consumed by the outer
loop, one reused by every reset), one junk tape for the register arithmetic, and
then `TM.applyTM`'s own tapes placed after them. The running value needs no tape
of its own — it lives on `applyTM`'s virtual-input tape, which is exactly where
the next call wants it.

## Main results

- `Complexity.rfIdx`, `wfIdx`, `junkIdx`, `appIdx`, `vinIdx`, `resIdx` — the layout
- `Complexity.placedApply_hoareTime` — one embedded application of the iterated function
- `Complexity.iterPark_hoareTime`, `iterResetScratch_hoareTime`,
  `iterFinish_hoareTime` — the phase contracts around it
-/


@[expose] public section

namespace Complexity

open Complexity.TM

variable {k : ℕ}

/-- The outer loop's fuel register. -/
def rfIdx : Fin (3 + (k + 2) + 0) := ⟨0, by omega⟩

/-- The reset's fuel register, restored by every reset. -/
def wfIdx : Fin (3 + (k + 2) + 0) := ⟨1, by omega⟩

/-- Holds the input's padding block; never read again. -/
def junkIdx : Fin (3 + (k + 2) + 0) := ⟨2, by omega⟩

/-- Where `TM.applyTM`'s tape `j` sits in the composite layout. -/
def appIdx (j : Fin (k + 2)) : Fin (3 + (k + 2) + 0) := placeWorkIdx 3 0 j

/-- The running value's tape — `applyTM`'s virtual input. -/
def vinIdx : Fin (3 + (k + 2) + 0) := appIdx (Fin.castSucc (Fin.last k))

/-- Where one application of the iterated function leaves its result. -/
def resIdx : Fin (3 + (k + 2) + 0) := appIdx (Fin.last (k + 1))

@[simp] theorem rfIdx_val : (rfIdx (k := k)).val = 0 := rfl
@[simp] theorem wfIdx_val : (wfIdx (k := k)).val = 1 := rfl
@[simp] theorem junkIdx_val : (junkIdx (k := k)).val = 2 := rfl
@[simp] theorem appIdx_val (j : Fin (k + 2)) : (appIdx j).val = 3 + j.val := rfl

/-- The three bookkeeping tapes are exactly the ones outside `applyTM`'s
block. -/
theorem not_middle_iff (i : Fin (3 + (k + 2) + 0)) :
    ¬ placeWorkInMiddle 3 (k + 2) i ↔ i.val < 3 := by
  have hlt := i.isLt
  unfold placeWorkInMiddle
  constructor <;> intro h <;> omega

theorem appIdx_middle (j : Fin (k + 2)) : placeWorkInMiddle 3 (k + 2) (appIdx j) :=
  placeWorkInMiddle_placeWorkIdx 3 0 j

theorem appIdx_injective : Function.Injective (appIdx (k := k)) :=
  placeWorkIdx_injective 3 0

theorem rfIdx_not_middle : ¬ placeWorkInMiddle 3 (k + 2) (rfIdx (k := k)) :=
  (not_middle_iff _).mpr (by rw [rfIdx_val]; omega)

theorem wfIdx_not_middle : ¬ placeWorkInMiddle 3 (k + 2) (wfIdx (k := k)) :=
  (not_middle_iff _).mpr (by rw [wfIdx_val]; omega)

theorem junkIdx_not_middle : ¬ placeWorkInMiddle 3 (k + 2) (junkIdx (k := k)) :=
  (not_middle_iff _).mpr (by rw [junkIdx_val]; omega)

theorem wfIdx_ne_appIdx (j : Fin (k + 2)) : wfIdx ≠ appIdx j := by
  intro h
  exact wfIdx_not_middle (h ▸ appIdx_middle j)

theorem rfIdx_ne_appIdx (j : Fin (k + 2)) : rfIdx ≠ appIdx j := by
  intro h
  exact rfIdx_not_middle (h ▸ appIdx_middle j)

theorem junkIdx_ne_appIdx (j : Fin (k + 2)) : junkIdx ≠ appIdx j := by
  intro h
  exact junkIdx_not_middle (h ▸ appIdx_middle j)

/-- **The layout is exhaustive.** Every tape of the composite machine is one of
the three bookkeeping tapes or one of `TM.applyTM`'s own, so a predicate that
names all four kinds pins down the whole tape family. -/
theorem layout_cases (i : Fin (3 + (k + 2) + 0)) :
    i = rfIdx ∨ i = wfIdx ∨ i = junkIdx ∨ ∃ j : Fin (k + 2), i = appIdx j := by
  by_cases hmid : placeWorkInMiddle 3 (k + 2) i
  · exact Or.inr (Or.inr (Or.inr
      ⟨placeWorkCoord 3 (k + 2) i hmid, (placeWorkIdx_placeWorkCoord i hmid).symm⟩))
  · rw [not_middle_iff] at hmid
    have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases h with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))

/-- **One application of the iterated function, in the composite layout.**
The bookkeeping tapes are held fixed; `applyTM`'s block goes from its entry
shape for `y` to a state where the result tape holds `G y` and every tape of
the block is still confined to cells `1 … H` — the two facts
`Complexity.resetTapesTM` needs to clean up afterwards. -/
theorem placedApply_hoareTime (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (y : List Bool)
    (inp₀ : Tape) (hinp : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (H : ℕ) (hHy : y.length ≤ H) (hHT : 1 + T y.length ≤ H)
    (extras : Fin (3 + (k + 2) + 0) → Tape)
    (hextraSI : ∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → Tape.StartInvariant (extras i))
    (hextraH : ∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → 1 ≤ (extras i).head) :
    (placeWorkTM 3 0 (applyTM M)).HoareTime
      (fun inp work out => inp = inp₀ ∧
        (∀ j, work (appIdx j) = applyPre M y inp₀ j) ∧
        (∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → work i = extras i) ∧
        out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work resIdx).HasOutput (G y) ∧
        (∀ j, Tape.StartInvariant (work (appIdx j)) ∧ (work (appIdx j)).head ≤ H ∧
          ∀ c, H < c → (work (appIdx j)).cells c = Γ.blank) ∧
        (∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → work i = extras i))
      (T y.length) := by
  have hbase := placeWorkTM_hoareTime_frame (pre := 3) (post := 0) (applyTM M)
    (applyTM_hoareTime_frame M hcomp y inp₀ hinp hinpSI H hHy hHT) extras hextraSI hextraH
  refine (hbase.weaken_pre ?_).strengthen_post ?_
  · rintro inp work out ⟨hi, hmid, hext, ho⟩
    exact ⟨⟨hi, funext hmid, ho⟩, hext⟩
  · rintro inp work out ⟨⟨hi, ho, hres, hall⟩, hext⟩
    exact ⟨hi, ho, hres, hall, hext⟩

/-- The tapes cleaned between two applications of the iterated function: the
witness machine's own scratch together with the virtual-input tape. The result
tape is deliberately excluded — it still carries the value being moved. -/
def resetTargets (k : ℕ) : List (Fin (3 + (k + 2) + 0)) :=
  (List.finRange (k + 1)).map (fun j => appIdx (Fin.castSucc j))

theorem resetTargets_nodup : (resetTargets k).Nodup := by
  refine (List.nodup_finRange (k + 1)).map ?_
  intro a b hab
  exact Fin.castSucc_injective (k + 1) (appIdx_injective hab)

@[simp] theorem resetTargets_length : (resetTargets k).length = k + 1 := by
  simp [resetTargets]

theorem mem_resetTargets_iff (i : Fin (3 + (k + 2) + 0)) :
    i ∈ resetTargets k ↔ ∃ j : Fin (k + 1), appIdx (Fin.castSucc j) = i := by
  simp [resetTargets, eq_comm]

theorem wfIdx_notMem_resetTargets : wfIdx ∉ resetTargets (k := k) := by
  rw [mem_resetTargets_iff]
  rintro ⟨j, hj⟩
  exact wfIdx_ne_appIdx _ hj.symm

theorem resIdx_notMem_resetTargets : resIdx ∉ resetTargets (k := k) := by
  rw [mem_resetTargets_iff]
  rintro ⟨j, hj⟩
  have := appIdx_injective hj
  exact absurd (congrArg Fin.val this) (by simp; omega)

theorem vinIdx_mem_resetTargets : vinIdx ∈ resetTargets (k := k) := by
  rw [mem_resetTargets_iff]
  exact ⟨Fin.last k, rfl⟩

/-- The tape cleaned after the result has been moved back. -/
def resetResult (k : ℕ) : List (Fin (3 + (k + 2) + 0)) := [resIdx]

theorem resetResult_nodup : (resetResult k).Nodup := List.nodup_singleton _

theorem wfIdx_notMem_resetResult : wfIdx ∉ resetResult (k := k) := by
  simp only [resetResult, List.mem_singleton]
  exact wfIdx_ne_appIdx _

/-- **Phases 2–3 of the body.** `δ_right_of_start` only constrains a head that
*reads* `▷`, so an arbitrary witness machine may halt with a head parked on
cell `0`. One idle step lifts every head to at least cell `1`, and one rewind
then brings the result tape's head back to exactly cell `1` — the shape both
`Complexity.resetTapesTM` (which preserves non-target tapes only when they are
parked) and `TM.copyWorkToWorkTM` (which wants its source at cell `1`)
require. -/
theorem iterPark_hoareTime (H : ℕ) (inp₀ : Tape) (hinpP : Parked inp₀)
    (hinpSI : Tape.StartInvariant inp₀)
    (W : Fin (3 + (k + 2) + 0) → Tape)
    (hSI : ∀ i, Tape.StartInvariant (W i))
    (hB : (W resIdx).head ≤ H) :
    (seqTM skipTM (rewindWorkTM resIdx)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W ∧ out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work resIdx).head = 1 ∧
        (work resIdx).cells = (W resIdx).cells ∧
        (∀ i, i ≠ resIdx → work i = (⟨max (W i).head 1, (W i).cells⟩ : Tape)))
      (1 + 1 + (H + 1 + 2)) := by
  set WA : Fin (3 + (k + 2) + 0) → Tape :=
    fun i => (⟨max (W i).head 1, (W i).cells⟩ : Tape) with hWA
  have hWAP : ∀ i, Parked (WA i) := fun i => ⟨le_max_right _ _, fun j hj => (hSI i).2 j hj⟩
  have houtP : Parked parkedBlank := parked_parkedBlank
  have houtSI : Tape.StartInvariant parkedBlank := startInvariant_initNil.move Dir3.right
  have hinpEq : (⟨max inp₀.head 1, inp₀.cells⟩ : Tape) = inp₀ :=
    Tape.ext (by show max inp₀.head 1 = inp₀.head; have := hinpP.1; omega) rfl
  have houtEq : (⟨max parkedBlank.head 1, parkedBlank.cells⟩ : Tape) = parkedBlank :=
    Tape.ext (by show max parkedBlank.head 1 = parkedBlank.head; have := houtP.1; omega) rfl
  have hA' : (skipTM (n := 3 + (k + 2) + 0)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W ∧ out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ work = WA ∧ out = parkedBlank) 1 :=
    (parkAll_hoareTime inp₀ W parkedBlank hinpSI hSI houtSI).strengthen_post (by
      rintro inp work out ⟨hi, hw, ho⟩
      exact ⟨hi.trans hinpEq, funext hw, ho.trans houtEq⟩)
  have hP : ∀ (inp : Tape) (work : Fin (3 + (k + 2) + 0) → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin (3 + (k + 2) + 0) → Tape) (out' : Tape),
      ((work resIdx).cells = (W resIdx).cells ∧ inp = inp₀ ∧ out = parkedBlank ∧
        ∀ i, i ≠ resIdx → work i = WA i) →
      (work' resIdx).cells = (work resIdx).cells →
      (work' resIdx).head = 1 →
      (∀ i, i ≠ resIdx → work' i = work i) →
      inp' = inp → out'.cells = out.cells → out'.head = out.head →
      ((work' resIdx).cells = (W resIdx).cells ∧ inp' = inp₀ ∧ out' = parkedBlank ∧
        ∀ i, i ≠ resIdx → work' i = WA i) := by
    rintro inp work out inp' work' out' ⟨hc, rfl, rfl, hrest⟩ hc' _ hkeep rfl hoc hoh
    exact ⟨hc'.trans hc, rfl, Tape.ext hoh hoc,
      fun i hi => (hkeep i hi).trans (hrest i hi)⟩
  have hC := rewindWorkTM_hoareTime_frame (n := 3 + (k + 2) + 0) resIdx (H + 1)
    (P := fun inp work out => (work resIdx).cells = (W resIdx).cells ∧
      inp = inp₀ ∧ out = parkedBlank ∧ ∀ i, i ≠ resIdx → work i = WA i) hP
  have hpreC : ∀ (inp : Tape) (work : Fin (3 + (k + 2) + 0) → Tape) (out : Tape),
      (inp = inp₀ ∧ work = WA ∧ out = parkedBlank) →
      ((work resIdx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work resIdx).cells j ≠ Γ.start) ∧
        (work resIdx).head ≤ H + 1 ∧
        inp.read ≠ Γ.start ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, i ≠ resIdx → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
        ((work resIdx).cells = (W resIdx).cells ∧ inp = inp₀ ∧ out = parkedBlank ∧
          ∀ i, i ≠ resIdx → work i = WA i)) := by
    rintro inp work out ⟨hi, hw, ho⟩
    subst hw
    refine ⟨(hSI resIdx).1, fun j hj => (hSI resIdx).2 j hj, ?_,
      by rw [hi]; exact hinpP.read_ne_start, by rw [ho]; exact houtP.read_ne_start,
      by rw [ho]; exact houtP.1,
      fun i _ => ⟨(hWAP i).read_ne_start, (hWAP i).1⟩, rfl, hi, ho, fun i _ => rfl⟩
    show max (W resIdx).head 1 ≤ H + 1
    omega
  have hC' := hC.weaken_pre hpreC
  refine (seqTM_hoareTime _ _ hA' ?_ hC').strengthen_post ?_
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨transitionInput_eq_self hinpP.read_ne_start,
      funext fun i => transitionTape_eq_self (hWAP i).read_ne_start,
      transitionTape_eq_self houtP.read_ne_start⟩
  · rintro inp work out ⟨hh, hc, hi, ho, hrest⟩
    exact ⟨hi, ho, hh, hc, hrest⟩

theorem rfIdx_ne_wfIdx : rfIdx (k := k) ≠ wfIdx := by
  intro h; exact absurd (congrArg Fin.val h) (by simp)

theorem junkIdx_ne_wfIdx : junkIdx (k := k) ≠ wfIdx := by
  intro h; exact absurd (congrArg Fin.val h) (by simp)

theorem resIdx_ne_wfIdx : resIdx (k := k) ≠ wfIdx := fun h => wfIdx_ne_appIdx _ h.symm

theorem rfIdx_notMem_resetTargets : rfIdx ∉ resetTargets (k := k) := by
  rw [mem_resetTargets_iff]
  rintro ⟨j, hj⟩
  exact rfIdx_ne_appIdx _ hj.symm

theorem junkIdx_notMem_resetTargets : junkIdx ∉ resetTargets (k := k) := by
  rw [mem_resetTargets_iff]
  rintro ⟨j, hj⟩
  exact junkIdx_ne_appIdx _ hj.symm

/-- **Phase 4 of the body.** Blank the witness machine's scratch tapes and the
virtual-input tape, leaving the result tape (which carries the value being
moved), both fuel registers, and the junk tape exactly as they were. -/
theorem iterResetScratch_hoareTime (H : ℕ) (hH : 1 ≤ H)
    (inp₀ : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (W : Fin (3 + (k + 2) + 0) → Tape)
    (hSI : ∀ i, Tape.StartInvariant (W i))
    (hB : ∀ j : Fin (k + 1), (W (appIdx (Fin.castSucc j))).head ≤ H)
    (hfar : ∀ j : Fin (k + 1), ∀ c, H < c → (W (appIdx (Fin.castSucc j))).cells c = Γ.blank)
    (hwf : W wfIdx = regTape H) :
    (resetTapesTM (resetTargets k) wfIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work resIdx).head = 1 ∧
        (work resIdx).cells = (W resIdx).cells ∧
        (∀ i, i ≠ resIdx → work i = (⟨max (W i).head 1, (W i).cells⟩ : Tape)))
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work resIdx).head = 1 ∧
        (work resIdx).cells = (W resIdx).cells ∧
        (∀ j : Fin (k + 1), work (appIdx (Fin.castSucc j)) = parkedBlank) ∧
        work wfIdx = regTape H ∧
        work rfIdx = (⟨max (W rfIdx).head 1, (W rfIdx).cells⟩ : Tape) ∧
        work junkIdx = (⟨max (W junkIdx).head 1, (W junkIdx).cells⟩ : Tape))
      ((k + 1) * (H + 4) + H * 4 + 8 + 1 + ((k + 1) * (H + 4) + 1)) := by
  intro inp work out hpre
  obtain ⟨hi, ho, hrh, hrc, hrest⟩ := hpre
  rw [hi, ho]
  have hworkSI : ∀ j, j ≠ wfIdx → Tape.StartInvariant (work j) := by
    intro j _
    by_cases hjr : j = resIdx
    · exact ⟨by rw [hjr, hrc]; exact (hSI resIdx).1,
        fun c hc => by rw [hjr, hrc]; exact (hSI resIdx).2 c hc⟩
    · rw [hrest j hjr]
      exact ⟨(hSI j).1, fun c hc => (hSI j).2 c hc⟩
  have hbnd : ∀ j, j ∈ resetTargets k →
      (work j).head ≤ H ∧ ∀ c, H < c → (work j).cells c = Γ.blank := by
    intro j hj
    obtain ⟨j', rfl⟩ := (mem_resetTargets_iff j).mp hj
    have hne : appIdx (Fin.castSucc j') ≠ resIdx := by
      intro hc
      exact absurd (congrArg Fin.val (appIdx_injective hc)) (by simp; omega)
    rw [hrest _ hne]
    refine ⟨?_, fun c hc => hfar j' c hc⟩
    show max (W (appIdx (Fin.castSucc j'))).head 1 ≤ H
    have := hB j'
    omega
  have hwfEq : work wfIdx = regTape H := by
    rw [hrest wfIdx (fun h => resIdx_ne_wfIdx h.symm), hwf]
    refine Tape.ext ?_ rfl
    show max (regTape H).head 1 = 1
    rw [regT_head]
    omega
  obtain ⟨c', t, ht, hreach, hhalt, hi', ho', hts, hR', hkeep⟩ :=
    resetTapesTM_hoareTime_of_bounds (resetTargets k) resetTargets_nodup wfIdx
      wfIdx_notMem_resetTargets H inp₀ work parkedBlank hinpSI hinpP rfl
      (fun j hjw hjt => by
        by_cases hjr : j = resIdx
        · exact ⟨by rw [hjr, hrh], fun c hc => by
            rw [hjr, hrc]; exact (hSI resIdx).2 c hc⟩
        · rw [hrest j hjr]
          exact ⟨le_max_right _ _, fun c hc => (hSI j).2 c hc⟩)
      inp₀ work parkedBlank ⟨rfl, rfl, hworkSI, hbnd, hwfEq, fun _ _ _ => rfl⟩
  rw [resetTargets_length] at ht
  refine ⟨c', t, ht, hreach, hhalt, hi', ho', ?_, ?_, ?_, hR', ?_, ?_⟩
  · rw [hkeep resIdx (fun h => resIdx_ne_wfIdx h) resIdx_notMem_resetTargets]; exact hrh
  · rw [hkeep resIdx (fun h => resIdx_ne_wfIdx h) resIdx_notMem_resetTargets]; exact hrc
  · intro j
    exact hts _ ((mem_resetTargets_iff _).mpr ⟨j, rfl⟩)
  · rw [hkeep rfIdx rfIdx_ne_wfIdx rfIdx_notMem_resetTargets]
    exact hrest rfIdx (fun h => rfIdx_ne_appIdx _ h)
  · rw [hkeep junkIdx junkIdx_ne_wfIdx junkIdx_notMem_resetTargets]
    exact hrest junkIdx (fun h => junkIdx_ne_appIdx _ h)

/-- `TM.applyPre` in closed form: the virtual-input tape carries the value, and
every other tape of the block is blank. -/
theorem applyPre_eq (M : TM k) (x : List Bool) (inp₀ : Tape) (j : Fin (k + 2)) :
    TM.applyPre M x inp₀ j =
      if j = Fin.castSucc (Fin.last k) then (Tape.init (x.map Γ.ofBool)).move Dir3.right
      else parkedBlank := by
  refine Fin.lastCases ?_ ?_ j
  · rw [TM.applyPre, Fin.snoc_last, ite_eq_right]
    intro hc
    exact absurd (congrArg Fin.val hc) (by simp)
  · intro j'
    rw [TM.applyPre, Fin.snoc_castSucc]
    show (TM.retargetInputStartedCfg M x inp₀).work j' = _
    rw [TM.retargetInputStartedCfg]
    dsimp only
    by_cases hj : j' = Fin.last k
    · rw [hj, ite_eq_right (by simp), ite_eq_left rfl]
    · have hlt : j'.val < k := by
        have := j'.isLt
        rcases Nat.lt_or_ge j'.val k with h | h
        · exact h
        · exact absurd (Fin.ext (show j'.val = (Fin.last k).val by
            rw [Fin.val_last]; omega)) hj
      rw [ite_eq_left hlt, ite_eq_right (fun hc => hj (Fin.castSucc_injective (k + 1) hc))]
      rfl

theorem resIdx_ne_vinIdx : resIdx (k := k) ≠ vinIdx := by
  intro h
  exact absurd (congrArg Fin.val (appIdx_injective h)) (by simp)

theorem rfIdx_ne_resIdx : rfIdx (k := k) ≠ resIdx := rfIdx_ne_appIdx _
theorem junkIdx_ne_resIdx : junkIdx (k := k) ≠ resIdx := junkIdx_ne_appIdx _
theorem wfIdx_ne_resIdx : wfIdx (k := k) ≠ resIdx := wfIdx_ne_appIdx _
theorem rfIdx_ne_vinIdx : rfIdx (k := k) ≠ vinIdx := rfIdx_ne_appIdx _
theorem junkIdx_ne_vinIdx : junkIdx (k := k) ≠ vinIdx := junkIdx_ne_appIdx _
theorem wfIdx_ne_vinIdx : wfIdx (k := k) ≠ vinIdx := wfIdx_ne_appIdx _

theorem junkIdx_ne_rfIdx : junkIdx (k := k) ≠ rfIdx := by
  intro h; exact absurd (congrArg Fin.val h) (by simp)

/-- **Phases 5–6 of the body.** Move the freshly computed value from the result
tape onto the virtual-input tape — where the next application will read it —
and then blank the result tape, restoring `TM.applyPre`'s entry shape for the
new value. -/
theorem iterFinish_hoareTime (M : TM k) (H : ℕ)
    (x : List Bool) (hx : x.length + 1 ≤ H)
    (inp₀ : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (resT rfT junkT : Tape)
    (hresH : resT.head = 1) (hresOut : resT.HasOutput x)
    (hresSI : Tape.StartInvariant resT)
    (hresFar : ∀ c, H < c → resT.cells c = Γ.blank)
    (hrfP : Parked rfT) (hrfSI : Tape.StartInvariant rfT)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) :
    (seqTM (copyToVirtualInputTM resIdx vinIdx)
      (resetTapesTM (resetResult k) wfIdx)).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        work resIdx = resT ∧ work rfIdx = rfT ∧ work junkIdx = junkT ∧
        work wfIdx = regTape H ∧
        (∀ j : Fin (k + 1), work (appIdx (Fin.castSucc j)) = parkedBlank))
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        work rfIdx = rfT ∧ work junkIdx = junkT ∧ work wfIdx = regTape H ∧
        (∀ j, work (appIdx j) = TM.applyPre M x inp₀ j))
      (2 * x.length + 5 + 1 +
        (1 * (H + 4) + H * 4 + 8 + 1 + (1 * (H + 4) + 1))) := by
  have hregP : Parked (regTape H) :=
    ⟨le_refl 1, fun i hi => by
      show regCells H i ≠ Γ.start
      simp only [regCells]; split
      · omega
      · split <;> decide⟩
  have hregSI : Tape.StartInvariant (regTape H) := ⟨rfl, hregP.2⟩
  have houtP : Parked parkedBlank := parked_parkedBlank
  have hblankSI : Tape.StartInvariant parkedBlank := startInvariant_initNil.move Dir3.right
  -- the tape family entering phase 5
  set W₀ : Fin (3 + (k + 2) + 0) → Tape := fun i =>
    if i = resIdx then resT else if i = rfIdx then rfT else if i = junkIdx then junkT
    else if i = wfIdx then regTape H else parkedBlank with hW₀
  have hW₀SI : ∀ i, Tape.StartInvariant (W₀ i) := by
    intro i; rw [hW₀]; dsimp only
    split; · exact hresSI
    split; · exact hrfSI
    split; · exact hjunkSI
    split; · exact hregSI
    exact hblankSI
  have hW₀other : ∀ i, i ≠ resIdx → i ≠ vinIdx → Parked (W₀ i) := by
    intro i hir _; rw [hW₀]; dsimp only
    rw [ite_eq_right hir]
    split; · exact hrfP
    split; · exact hjunkP
    split; · exact hregP
    exact houtP
  have hW₀res : W₀ resIdx = resT := by rw [hW₀]; simp
  have hW₀vin : W₀ vinIdx = parkedBlank := by
    rw [hW₀]
    dsimp only
    rw [ite_eq_right (fun h => resIdx_ne_vinIdx h.symm),
      ite_eq_right (fun h => rfIdx_ne_appIdx _ h.symm),
      ite_eq_right (fun h => junkIdx_ne_appIdx _ h.symm),
      ite_eq_right (fun h => wfIdx_ne_appIdx _ h.symm)]
  have hW₀app : ∀ j : Fin (k + 2), appIdx j ≠ resIdx → W₀ (appIdx j) = parkedBlank := by
    intro j hj
    rw [hW₀]
    dsimp only
    rw [ite_eq_right hj, ite_eq_right (fun h => rfIdx_ne_appIdx _ h.symm),
      ite_eq_right (fun h => junkIdx_ne_appIdx _ h.symm),
      ite_eq_right (fun h => wfIdx_ne_appIdx _ h.symm)]
  have hW₀rf : W₀ rfIdx = rfT := by
    rw [hW₀]
    dsimp only
    rw [ite_eq_right rfIdx_ne_resIdx, ite_eq_left rfl]
  have hW₀junk : W₀ junkIdx = junkT := by
    rw [hW₀]
    dsimp only
    rw [ite_eq_right junkIdx_ne_resIdx, ite_eq_right junkIdx_ne_rfIdx, ite_eq_left rfl]
  have hW₀wf : W₀ wfIdx = regTape H := by
    rw [hW₀]
    dsimp only
    rw [ite_eq_right wfIdx_ne_resIdx, ite_eq_right (fun h => rfIdx_ne_wfIdx h.symm),
      ite_eq_right (fun h => junkIdx_ne_wfIdx h.symm), ite_eq_left rfl]
  -- the value tape produced by the copy, and the family after each phase
  set vinT : Tape := (Tape.init (x.map Γ.ofBool)).move Dir3.right with hvinT
  have hvinSI : Tape.StartInvariant vinT := (startInvariant_initOfBool x).move Dir3.right
  have hvinP : Parked vinT := ⟨le_refl 1, hvinSI.2⟩
  set W₁ : Fin (3 + (k + 2) + 0) → Tape :=
    Function.update (Function.update W₀ vinIdx vinT) resIdx
      (⟨x.length + 1, (W₀ resIdx).cells⟩ : Tape) with hW₁
  set W₂ : Fin (3 + (k + 2) + 0) → Tape := Function.update W₁ resIdx parkedBlank with hW₂
  have hW₁res : W₁ resIdx = (⟨x.length + 1, resT.cells⟩ : Tape) := by
    rw [hW₁, Function.update_self, hW₀res]
  have hW₁vin : W₁ vinIdx = vinT := by
    rw [hW₁, Function.update_of_ne resIdx_ne_vinIdx.symm, Function.update_self]
  have hW₁other : ∀ i, i ≠ resIdx → i ≠ vinIdx → W₁ i = W₀ i := by
    intro i hir hiv
    rw [hW₁, Function.update_of_ne hir, Function.update_of_ne hiv]
  have hW₁P : ∀ i, Parked (W₁ i) := by
    intro i
    by_cases hir : i = resIdx
    · rw [hir, hW₁res]
      exact ⟨show 1 ≤ x.length + 1 by omega, fun j hj => hresSI.2 j hj⟩
    · by_cases hiv : i = vinIdx
      · rw [hiv, hW₁vin]; exact hvinP
      · rw [hW₁other i hir hiv]; exact hW₀other i hir hiv
  -- phase 5: the copy
  have hcopy := copyToVirtualInputTM_hoareTime resIdx vinIdx resIdx_ne_vinIdx x inp₀ W₀
    parkedBlank (by rw [hW₀res]; exact hresH) (by rw [hW₀res]; exact hresOut)
    (by rw [hW₀res]; exact ⟨by omega, fun j hj => hresSI.2 j hj⟩) hW₀vin hinpP houtP hW₀other
  -- phase 6: blanking the result tape
  have hreset := resetTapesTM_hoareTime (resetResult k) resetResult_nodup wfIdx
    wfIdx_notMem_resetResult H inp₀ W₁ parkedBlank hinpSI hinpP rfl
    (fun j _ => by
      by_cases hjr : j = resIdx
      · rw [hjr, hW₁res]; exact ⟨hresSI.1, fun c hc => hresSI.2 c hc⟩
      · by_cases hjv : j = vinIdx
        · rw [hjv, hW₁vin]; exact hvinSI
        · rw [hW₁other j hjr hjv]; exact hW₀SI j)
    (fun j hj => by
      rw [List.mem_singleton.mp hj, hW₁res]
      show x.length + 1 ≤ H
      omega)
    (fun j hj c hc => by
      rw [List.mem_singleton.mp hj, hW₁res]
      exact hresFar c hc)
    (by rw [hW₁other wfIdx (fun h => resIdx_ne_wfIdx h.symm) (fun h => wfIdx_ne_appIdx _ h),
      hW₀wf])
    (fun j hjw hjt => hW₁P j)
  have hreset' : (resetTapesTM (resetResult k) wfIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W₁ ∧ out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ work = W₂ ∧ out = parkedBlank)
      (1 * (H + 4) + H * 4 + 8 + 1 + (1 * (H + 4) + 1)) := by
    refine (hreset.strengthen_post ?_).mono_bound (by simp [resetResult])
    rintro inp work out ⟨hi, ho, hts, hR, hrest⟩
    refine ⟨hi, funext fun j => ?_, ho⟩
    by_cases hjr : j = resIdx
    · rw [hjr, hts resIdx (by simp [resetResult]), hW₂, Function.update_self]
      rfl
    · rw [hW₂, Function.update_of_ne hjr]
      by_cases hjw : j = wfIdx
      · rw [hjw, hR, hW₁other wfIdx (fun h => resIdx_ne_wfIdx h.symm)
          (fun h => wfIdx_ne_appIdx _ h), hW₀wf]
      · exact hrest j hjw (by simp only [resetResult, List.mem_singleton]; exact hjr)
  -- chain the two phases and read the result off
  have hpre_imp : ∀ (inp : Tape) (work : Fin (3 + (k + 2) + 0) → Tape) (out : Tape),
      (inp = inp₀ ∧ out = parkedBlank ∧
        work resIdx = resT ∧ work rfIdx = rfT ∧ work junkIdx = junkT ∧
        work wfIdx = regTape H ∧
        (∀ j : Fin (k + 1), work (appIdx (Fin.castSucc j)) = parkedBlank)) →
      (inp = inp₀ ∧ work = W₀ ∧ out = parkedBlank) := by
    rintro inp work out ⟨hi, ho, hres, hrf, hjunk, hwf, happ⟩
    refine ⟨hi, funext fun i => ?_, ho⟩
    rcases layout_cases i with hi' | hi' | hi' | ⟨j, hi'⟩
    · rw [hi', hrf, hW₀rf]
    · rw [hi', hwf, hW₀wf]
    · rw [hi', hjunk, hW₀junk]
    · subst hi'
      refine Fin.lastCases ?_ ?_ j
      · rw [show appIdx (Fin.last (k + 1)) = resIdx from rfl, hres, hW₀res]
      · intro j'
        rw [happ j', hW₀app _ (fun h => absurd (appIdx_injective h)
          (Fin.castSucc_lt_last j').ne)]
  refine (((seqTM_det (copyToVirtualInputTM resIdx vinIdx)
    (resetTapesTM (resetResult k) wfIdx) hinpP houtP hW₁P hcopy
    hreset').weaken_pre hpre_imp).strengthen_post ?_).mono_bound le_rfl
  · rintro inp work out ⟨hi, hw, ho⟩
    subst hw
    refine ⟨hi, ho, ?_, ?_, ?_, fun j => ?_⟩
    · rw [hW₂, Function.update_of_ne rfIdx_ne_resIdx,
        hW₁other rfIdx rfIdx_ne_resIdx rfIdx_ne_vinIdx, hW₀rf]
    · rw [hW₂, Function.update_of_ne junkIdx_ne_resIdx,
        hW₁other junkIdx junkIdx_ne_resIdx junkIdx_ne_vinIdx, hW₀junk]
    · rw [hW₂, Function.update_of_ne wfIdx_ne_resIdx,
        hW₁other wfIdx wfIdx_ne_resIdx wfIdx_ne_vinIdx, hW₀wf]
    · rw [applyPre_eq]
      by_cases hj : j = Fin.castSucc (Fin.last k)
      · rw [ite_eq_left hj, hj, show appIdx (Fin.castSucc (Fin.last k)) = vinIdx from rfl,
          hW₂, Function.update_of_ne resIdx_ne_vinIdx.symm, hW₁vin]
      · rw [ite_eq_right hj]
        by_cases hjl : j = Fin.last (k + 1)
        · rw [hjl, show appIdx (Fin.last (k + 1)) = resIdx from rfl, hW₂, Function.update_self]
        · have hjr : appIdx j ≠ resIdx := fun h =>
            hjl (appIdx_injective (h.trans (rfl : resIdx = appIdx (Fin.last (k + 1)))))
          have hjv : appIdx j ≠ vinIdx := fun h =>
            hj (appIdx_injective (h.trans (rfl : vinIdx = appIdx (Fin.castSucc (Fin.last k)))))
          rw [hW₂, Function.update_of_ne hjr, hW₁other _ hjr hjv, hW₀app j hjr]


end Complexity
