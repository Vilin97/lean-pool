/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics.PolyBound
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.IterateLayout
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.Horner
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.InputLen
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairEmit
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.NormalForm

/-!
# The bounded-iteration machine — proof internals

`Complexity.Cobham.iterate_mem_FP` needs one machine: given a polynomial-time
`G`, a machine that applies `G` to its own input `|x|` times. This file builds
it out of the phase contracts of
`Complexitylib.Classes.P.Cobham.Internal.IterateLayout`.

## Layout

Three bookkeeping tapes (`rfIdx` the loop's fuel register, `wfIdx` the reset's
fuel register, `junkIdx` scratch for the register arithmetic) followed by
`TM.applyTM`'s own block (`appIdx`), whose virtual input `vinIdx` carries the
running value and whose last tape `resIdx` receives each result.

## Phases

* `Complexity.iterTail` — the five phases that follow every application: park,
  rewind the result, blank the scratch, move the result into virtual-input
  position, blank the result tape. Shared by the loop body and the setup.
* `Complexity.iterBody` — one application of the iterated function followed by
  the tail; this is what the loop iterates.
* `Complexity.iterSetup` — bump, load `|x|` into the loop register, evaluate a
  padding polynomial into the reset register, put `pair [] x` on the result
  tape, then the tail.
* `Complexity.iterTM` — setup, loop, and one final application whose output is
  the real output tape.
-/


public section

namespace Complexity

open Complexity.TM

variable {k : ℕ}

/-! ## A confinement frame for an arbitrary bounded run

Resetting the scratch of an opaque machine needs to know how far its heads can
have travelled. Any `b`-step run from tapes parked at cell `1` and blank beyond
it stays inside cell `1 + b`. -/

/-- **Every bounded run is confined.** From work tapes parked at cell `1` whose
content is confined to cell `1`, a `b`-step run leaves every work tape inside
`H` and blank beyond `H`. -/
theorem hoareTime_confined {n : ℕ} {tm : TM n} {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b) (W : Fin n → Tape) (H : ℕ) (hH : 1 + b ≤ H)
    (S : Fin n → Prop) (hWSI : ∀ i, Tape.StartInvariant (W i))
    (hWh : ∀ i, S i → (W i).head = 1)
    (hWfar : ∀ i, S i → ∀ j, 1 < j → (W i).cells j = Γ.blank) :
    tm.HoareTime
      (fun inp work out => pre inp work out ∧ work = W ∧
        Tape.StartInvariant inp ∧ Tape.StartInvariant out)
      (fun inp work out => post inp work out ∧ Tape.StartInvariant inp ∧
        Tape.StartInvariant out ∧
        ∀ i, Tape.StartInvariant (work i) ∧ (S i →
          (work i).head ≤ H ∧ ∀ j, H < j → (work i).cells j = Γ.blank))
      b := by
  rintro inp work out ⟨hpre, rfl, hinpSI, houtSI⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h inp work out hpre
  have hSI := TM.reachesIn_startInvariant hreach hinpSI hWSI houtSI
  refine ⟨c', t, ht, hreach, hhalt, hpost, hSI.1, hSI.2.2,
    fun i => ⟨hSI.2.1 i, fun hSi => ⟨?_, fun j hj => ?_⟩⟩⟩
  · have hh := (head_le_start_add_of_reachesIn tm hreach).2.2 i
    rw [show ((⟨tm.qstart, inp, work, out⟩ : Cfg n tm.Q).work i).head = 1 from hWh i hSi] at hh
    omega
  · rw [TM.reachesIn_work_cells_far hreach i j (by rw [show
      ((⟨tm.qstart, inp, work, out⟩ : Cfg n tm.Q).work i).head = 1 from hWh i hSi]; omega)]
    exact hWfar i hSi j (by omega)

/-! ## The shared tail

Every application of the iterated function — the loop body's, and the setup's
`pair [] x` — leaves its result on `resIdx` with the scratch dirty. The five
phases below restore the entry shape `TM.applyPre` demands. -/

/-- Park, rewind the result, blank the witness machine's scratch and the
virtual input, move the result into virtual-input position, blank the result
tape. -/
def iterTail (k : ℕ) : TM (3 + (k + 2) + 0) :=
  seqTM
    (seqTM (seqTM skipTM (rewindWorkTM resIdx)) (resetTapesTM (resetTargets k) wfIdx))
    (seqTM (copyToVirtualInputTM resIdx vinIdx) (resetTapesTM (resetResult k) wfIdx))

/-- `Complexity.iterTail`'s time bound. -/
def tailBound (k H m : ℕ) : ℕ :=
  1 + 1 + (H + 1 + 2) + 1 +
      ((k + 1) * (H + 4) + H * 4 + 8 + 1 + ((k + 1) * (H + 4) + 1)) + 1 +
    (2 * m + 5 + 1 + (1 * (H + 4) + H * 4 + 8 + 1 + (1 * (H + 4) + 1)))

theorem startInvariant_regTape (H : ℕ) : Tape.StartInvariant (regTape H) :=
  ⟨by rw [regT_cells]; simp [regCells], (parked_regTape H).2⟩

/-- **The tail's contract.** From a result tape carrying `v` and a block whose
tapes are confined to `1 … H`, the five phases rebuild `TM.applyPre M v`. -/
theorem iterTail_hoareTime (M : TM k) (H : ℕ) (v : List Bool) (hv : v.length + 1 ≤ H)
    (inp₀ : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (rfT junkT : Tape) (hrfP : Parked rfT) (hrfSI : Tape.StartInvariant rfT)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) :
    (iterTail k).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work resIdx).HasOutput v ∧
        (∀ j : Fin (k + 2), Tape.StartInvariant (work (appIdx j)) ∧
          (work (appIdx j)).head ≤ H ∧
          ∀ c, H < c → (work (appIdx j)).cells c = Γ.blank) ∧
        work rfIdx = rfT ∧ work wfIdx = regTape H ∧ work junkIdx = junkT)
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        work rfIdx = rfT ∧ work junkIdx = junkT ∧ work wfIdx = regTape H ∧
        (∀ j, work (appIdx j) = TM.applyPre M v inp₀ j))
      (tailBound k H v.length) := by
  intro inp work out hpre
  obtain ⟨hi, ho, hres, hbnd, hrf, hwf, hjunk⟩ := hpre
  subst hi
  subst ho
  have houtP : Parked parkedBlank := parked_parkedBlank
  have houtSI : Tape.StartInvariant parkedBlank := startInvariant_initNil.move Dir3.right
  have hregSI : Tape.StartInvariant (regTape H) := startInvariant_regTape H
  have hSI : ∀ i, Tape.StartInvariant (work i) := by
    intro i
    rcases layout_cases i with h | h | h | ⟨j, h⟩
    · rw [h, hrf]; exact hrfSI
    · rw [h, hwf]; exact hregSI
    · rw [h, hjunk]; exact hjunkSI
    · rw [h]; exact (hbnd j).1
  -- the three phase contracts, instantiated at the actual tape family
  have hpark := iterPark_hoareTime H inp hinpP hinpSI work hSI (hbnd (Fin.last (k + 1))).2.1
  have hrst := iterResetScratch_hoareTime H (by omega) inp hinpP hinpSI work hSI
    (fun j => (hbnd (Fin.castSucc j)).2.1)
    (fun j c hc => (hbnd (Fin.castSucc j)).2.2 c hc) hwf
  have hrfeq : (⟨max (work rfIdx).head 1, (work rfIdx).cells⟩ : Tape) = rfT := by
    rw [hrf]
    exact Tape.ext (by show max rfT.head 1 = rfT.head; have := hrfP.1; omega) rfl
  have hjunkeq : (⟨max (work junkIdx).head 1, (work junkIdx).cells⟩ : Tape) = junkT := by
    rw [hjunk]
    exact Tape.ext (by show max junkT.head 1 = junkT.head; have := hjunkP.1; omega) rfl
  have hfin := iterFinish_hoareTime M H v hv inp hinpP hinpSI
    (⟨1, (work resIdx).cells⟩ : Tape) rfT junkT rfl
    ((Tape.hasOutput_congr rfl v).mp hres)
    ⟨(hbnd (Fin.last (k + 1))).1.1, fun c hc => (hbnd (Fin.last (k + 1))).1.2 c hc⟩
    (fun c hc => (hbnd (Fin.last (k + 1))).2.2 c hc)
    hrfP hrfSI hjunkP hjunkSI
  -- chain the three, converting the seams through the parked frame
  have hAB := seqTM_hoareTime _ _ hpark (by
    rintro inp' work' out' ⟨rfl, rfl, e3, e4, e5⟩
    have hP : ∀ i, Parked (work' i) := by
      intro i
      by_cases hir : i = resIdx
      · exact ⟨by rw [hir, e3], fun c hc => by rw [hir, e4]; exact (hSI resIdx).2 c hc⟩
      · rw [e5 i hir]
        exact ⟨le_max_right _ _, fun c hc => (hSI i).2 c hc⟩
    obtain ⟨t1, t2, t3⟩ := parked_transition hinpP hP houtP
    rw [t1, t2, t3]
    exact ⟨rfl, rfl, e3, e4, e5⟩) hrst
  have hABC := seqTM_hoareTime _ _ hAB (by
    rintro inp' work' out' ⟨rfl, rfl, e3, e4, e5, e6, e7, e8⟩
    have hP : ∀ i, Parked (work' i) := by
      intro i
      by_cases hir : i = resIdx
      · exact ⟨by rw [hir, e3], fun c hc => by rw [hir, e4]; exact (hSI resIdx).2 c hc⟩
      · rcases layout_cases i with h | h | h | ⟨j, h⟩
        · rw [h, e7, hrfeq]; exact hrfP
        · rw [h, e6]; exact parked_regTape H
        · rw [h, e8, hjunkeq]; exact hjunkP
        · by_cases hjl : j = Fin.last (k + 1)
          · exact absurd (by rw [h, hjl]; rfl) hir
          · have hjv : j.val < k + 1 :=
              lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) (fun hc => hjl (Fin.ext hc))
            rw [h, show j = Fin.castSucc (⟨j.val, hjv⟩ : Fin (k + 1)) from Fin.ext rfl,
              e5 ⟨j.val, hjv⟩]
            exact houtP
    obtain ⟨t1, t2, t3⟩ := parked_transition hinpP hP houtP
    rw [t1, t2, t3]
    exact ⟨rfl, rfl, Tape.ext e3 e4, e7.trans hrfeq, e8.trans hjunkeq, e6, e5⟩) hfin
  exact hABC inp work parkedBlank ⟨rfl, rfl, rfl⟩

/-! ## One iteration

The loop body is one application of the iterated function followed by the
tail. -/

/-- One combinator seam on a tape satisfying the left-marker invariant: the
cells are untouched and the head only ever bounces off `▷`. -/
theorem transitionTape_of_startInvariant {t : Tape} (h : Tape.StartInvariant t) :
    transitionTape t = (⟨max t.head 1, t.cells⟩ : Tape) := by
  by_cases hh : t.read = Γ.start
  · have hh0 : t.head = 0 := by
      by_contra hc
      exact (h.2 t.head (by omega)) hh
    refine Tape.ext ?_ (transitionTape_cells t (fun j hj => h.2 j hj))
    have h1 := one_le_head_transitionTape t h.1
    have h2 := head_transitionTape_le (p_bound := 0) h.1 (le_of_eq hh0)
    show (transitionTape t).head = max t.head 1
    omega
  · rw [transitionTape_eq_self hh]
    have hh0 : t.head ≠ 0 := fun hc => hh (by rw [Tape.read, hc]; exact h.1)
    exact Tape.ext (by show t.head = max t.head 1; omega) rfl

/-- The three bookkeeping tapes, packaged as a placement frame. -/
def bookTapes (rfT junkT : Tape) (H : ℕ) : Fin (3 + (k + 2) + 0) → Tape :=
  fun i => if i = rfIdx then rfT else if i = wfIdx then regTape H else junkT

@[simp] theorem bookTapes_rf (rfT junkT : Tape) (H : ℕ) :
    bookTapes (k := k) rfT junkT H rfIdx = rfT := by
  rw [bookTapes, ite_eq_left rfl]

@[simp] theorem bookTapes_wf (rfT junkT : Tape) (H : ℕ) :
    bookTapes (k := k) rfT junkT H wfIdx = regTape H := by
  rw [bookTapes, ite_eq_right (fun h => rfIdx_ne_wfIdx h.symm), ite_eq_left rfl]

@[simp] theorem bookTapes_junk (rfT junkT : Tape) (H : ℕ) :
    bookTapes (k := k) rfT junkT H junkIdx = junkT := by
  rw [bookTapes, ite_eq_right junkIdx_ne_rfIdx, ite_eq_right junkIdx_ne_wfIdx]

theorem eq_bookTapes_of_not_middle {work : Fin (3 + (k + 2) + 0) → Tape}
    {rfT junkT : Tape} {H : ℕ}
    (hrf : work rfIdx = rfT) (hwf : work wfIdx = regTape H) (hjunk : work junkIdx = junkT) :
    ∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → work i = bookTapes rfT junkT H i := by
  intro i hi
  rcases layout_cases i with h | h | h | ⟨j, h⟩
  · rw [h, hrf, bookTapes_rf]
  · rw [h, hwf, bookTapes_wf]
  · rw [h, hjunk, bookTapes_junk]
  · exact absurd (h ▸ appIdx_middle j) hi

theorem bookTapes_startInvariant {rfT junkT : Tape} {H : ℕ}
    (hrfSI : Tape.StartInvariant rfT) (hjunkSI : Tape.StartInvariant junkT) :
    ∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → Tape.StartInvariant (bookTapes rfT junkT H i) := by
  intro i hi
  rcases layout_cases i with h | h | h | ⟨j, h⟩
  · rw [h, bookTapes_rf]; exact hrfSI
  · rw [h, bookTapes_wf]; exact startInvariant_regTape H
  · rw [h, bookTapes_junk]; exact hjunkSI
  · exact absurd (h ▸ appIdx_middle j) hi

theorem bookTapes_head {rfT junkT : Tape} {H : ℕ}
    (hrfP : Parked rfT) (hjunkP : Parked junkT) :
    ∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → 1 ≤ (bookTapes rfT junkT H i).head := by
  intro i hi
  rcases layout_cases i with h | h | h | ⟨j, h⟩
  · rw [h, bookTapes_rf]; exact hrfP.1
  · rw [h, bookTapes_wf]; exact (parked_regTape H).1
  · rw [h, bookTapes_junk]; exact hjunkP.1
  · exact absurd (h ▸ appIdx_middle j) hi

/-- The loop body: apply the iterated function once, then restore the entry
shape. -/
def iterBody (M : TM k) : TM (3 + (k + 2) + 0) :=
  seqTM (placeWorkTM 3 0 (TM.applyTM M)) (iterTail k)

/-- **The body's contract.** From the entry shape for `y`, the body reaches the
entry shape for `G y`, holding both registers and the junk tape fixed. -/
theorem iterBody_hoareTime (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (H : ℕ) (y : List Bool)
    (hHy : y.length ≤ H) (hHT : 1 + T y.length ≤ H) (hGy : (G y).length + 1 ≤ H)
    (inp₀ : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (rfT junkT : Tape) (hrfP : Parked rfT) (hrfSI : Tape.StartInvariant rfT)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) :
    (iterBody M).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (∀ j, work (appIdx j) = TM.applyPre M y inp₀ j) ∧
        work rfIdx = rfT ∧ work wfIdx = regTape H ∧ work junkIdx = junkT)
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        work rfIdx = rfT ∧ work junkIdx = junkT ∧ work wfIdx = regTape H ∧
        (∀ j, work (appIdx j) = TM.applyPre M (G y) inp₀ j))
      (T y.length + 1 + tailBound k H (G y).length) := by
  have happ := placedApply_hoareTime M hcomp y inp₀ hinpP hinpSI H hHy hHT
    (bookTapes rfT junkT H) (bookTapes_startInvariant hrfSI hjunkSI)
    (bookTapes_head hrfP hjunkP)
  refine seqTM_hoareTime _ _ (happ.weaken_pre ?_) ?_
    (iterTail_hoareTime M H (G y) hGy inp₀ hinpP hinpSI rfT junkT hrfP hrfSI hjunkP hjunkSI)
  · rintro inp work out ⟨hi, ho, happ', hrf, hwf, hjunk⟩
    exact ⟨hi, happ', eq_bookTapes_of_not_middle hrf hwf hjunk, ho⟩
  · rintro inp work out ⟨rfl, rfl, hres, hbnd, hext⟩
    dsimp only
    have hrfe : work rfIdx = rfT := by
      rw [hext rfIdx rfIdx_not_middle, bookTapes_rf]
    have hwfe : work wfIdx = regTape H := by
      rw [hext wfIdx wfIdx_not_middle, bookTapes_wf]
    have hjunke : work junkIdx = junkT := by
      rw [hext junkIdx junkIdx_not_middle, bookTapes_junk]
    have hSIall : ∀ i, Tape.StartInvariant (work i) := by
      intro i
      rcases layout_cases i with h | h | h | ⟨j, h⟩
      · rw [h, hrfe]; exact hrfSI
      · rw [h, hwfe]; exact startInvariant_regTape H
      · rw [h, hjunke]; exact hjunkSI
      · rw [h]; exact (hbnd j).1
    have htin : transitionInput inp = inp := transitionInput_eq_self hinpP.read_ne_start
    have htout : transitionTape parkedBlank = parkedBlank :=
      transitionTape_eq_self parked_parkedBlank.read_ne_start
    have hcells : ∀ i, (transitionTape (work i)).cells = (work i).cells := fun i =>
      transitionTape_cells _ (fun j hj => (hSIall i).2 j hj)
    refine ⟨htin, htout, ?_, fun j => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · exact (Tape.hasOutput_congr (hcells resIdx).symm (G y)).mp hres
    · exact ⟨(hcells (appIdx j)) ▸ (hbnd j).1.1,
        fun c hc => (hcells (appIdx j)) ▸ (hbnd j).1.2 c hc⟩
    · rw [transitionTape_of_startInvariant (hSIall (appIdx j))]
      show max (work (appIdx j)).head 1 ≤ H
      have := (hbnd j).2.1
      omega
    · intro c hc
      rw [hcells (appIdx j)]
      exact (hbnd j).2.2 c hc
    · rw [hrfe, transitionTape_eq_self hrfP.read_ne_start]
    · rw [hwfe, transitionTape_eq_self (parked_regTape H).read_ne_start]
    · rw [hjunke, transitionTape_eq_self hjunkP.read_ne_start]

/-! ## The loop

`TM.forRegTM` drives the body once per mark of the fuel register `rfIdx`,
threading the iteration-indexed ghost family below. -/

/-- The whole tape family at iteration `i`: the entry shape for the `i`-th
iterate on `TM.applyTM`'s block, the two registers, and the junk tape. -/
def iterFamily (M : TM k) (Y : ℕ → List Bool) (inp₀ junkT : Tape) (v H : ℕ) :
    ℕ → Fin (3 + (k + 2) + 0) → Tape :=
  fun i j => if hj : placeWorkInMiddle 3 (k + 2) j
    then TM.applyPre M (Y i) inp₀ (placeWorkCoord 3 (k + 2) j hj)
    else bookTapes (regTape v) junkT H j

variable {M : TM k} {Y : ℕ → List Bool} {inp₀ junkT : Tape} {v H : ℕ}

@[simp] theorem iterFamily_app (i : ℕ) (j : Fin (k + 2)) :
    iterFamily M Y inp₀ junkT v H i (appIdx j) = TM.applyPre M (Y i) inp₀ j := by
  rw [iterFamily]
  rw [dif_pos (appIdx_middle j)]
  congr 1
  exact placeWorkCoord_placeWorkIdx 3 0 j

theorem iterFamily_book (i : ℕ) (j : Fin (3 + (k + 2) + 0))
    (hj : ¬ placeWorkInMiddle 3 (k + 2) j) :
    iterFamily M Y inp₀ junkT v H i j = bookTapes (regTape v) junkT H j := by
  rw [iterFamily, dite_eq_right hj]

@[simp] theorem iterFamily_rf (i : ℕ) :
    iterFamily M Y inp₀ junkT v H i rfIdx = regTape v := by
  rw [iterFamily_book i rfIdx rfIdx_not_middle, bookTapes_rf]

@[simp] theorem iterFamily_wf (i : ℕ) :
    iterFamily M Y inp₀ junkT v H i wfIdx = regTape H := by
  rw [iterFamily_book i wfIdx wfIdx_not_middle, bookTapes_wf]

@[simp] theorem iterFamily_junk (i : ℕ) :
    iterFamily M Y inp₀ junkT v H i junkIdx = junkT := by
  rw [iterFamily_book i junkIdx junkIdx_not_middle, bookTapes_junk]

theorem iterFamily_parked (hjunkP : Parked junkT) (i : ℕ) (j : Fin (3 + (k + 2) + 0))
    (hj : j ≠ rfIdx) : Parked (iterFamily M Y inp₀ junkT v H i j) := by
  rcases layout_cases j with h | h | h | ⟨jj, h⟩
  · exact absurd h hj
  · rw [h, iterFamily_wf]; exact parked_regTape H
  · rw [h, iterFamily_junk]; exact hjunkP
  · rw [h, iterFamily_app]
    exact ⟨le_of_eq (TM.applyPre_head M (Y i) inp₀ jj).symm,
      fun c hc => (TM.applyPre_startInvariant M (Y i) inp₀ jj).2 c hc⟩

/-- **The loop's contract.** `v` applications of the iterated function, each
returning the block to its entry shape. -/
theorem iterLoop_hoareTime {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T)
    (hY : ∀ i, Y (i + 1) = G (Y i))
    (hlen : ∀ i, i ≤ v → (Y i).length + 1 ≤ H)
    (hT : ∀ i, i < v → 1 + T (Y i).length ≤ H)
    (b_iter : ℕ)
    (hb : ∀ i, i < v → T (Y i).length + 1 + tailBound k H (Y (i + 1)).length ≤ b_iter)
    (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) :
    (forRegTM (iterBody M) rfIdx).HoareTime
      (EmitPred inp₀ (iterFamily M Y inp₀ junkT v H 0) [])
      (EmitPred inp₀ (iterFamily M Y inp₀ junkT v H v) [])
      (v * (b_iter + 2) + (v + 2)) := by
  refine forRegTM_hoareTime (iterBody M) rfIdx v inp₀ (iterFamily M Y inp₀ junkT v H)
    (fun _ => []) b_iter hinpP (fun i => iterFamily_rf i)
    (fun i j hj => iterFamily_parked hjunkP i j hj) (fun i hi => ?_)
  have hrfP : Parked (⟨i + 2, regCells v⟩ : Tape) := regIterCells_parked v i
  have hrfSI : Tape.StartInvariant (⟨i + 2, regCells v⟩ : Tape) :=
    ⟨(startInvariant_regTape v).1, hrfP.2⟩
  have hbody := iterBody_hoareTime M hcomp H (Y i)
    (by have := hlen i (by omega); omega) (hT i hi)
    (by rw [← hY i]; exact hlen (i + 1) (by omega))
    inp₀ hinpP hinpSI (⟨i + 2, regCells v⟩ : Tape) junkT hrfP hrfSI hjunkP hjunkSI
  refine ((hbody.weaken_pre ?_).strengthen_post ?_).mono_bound ?_
  · rintro inp work out ⟨hi', hw, hout⟩
    refine ⟨hi', eq_parkedBlank_of_outAcc_nil hout, fun j => ?_, ?_, ?_, ?_⟩
    · rw [hw, Function.update_of_ne (fun h => rfIdx_ne_appIdx j h.symm), iterFamily_app]
    · rw [hw, Function.update_self]
    · rw [hw, Function.update_of_ne rfIdx_ne_wfIdx.symm, iterFamily_wf]
    · rw [hw, Function.update_of_ne junkIdx_ne_rfIdx, iterFamily_junk]
  · rintro inp work out ⟨hi', hout, hrf, hjunk, hwf, happ⟩
    refine ⟨hi', funext fun j => ?_, ?_⟩
    · rcases layout_cases j with h | h | h | ⟨jj, h⟩
      · rw [h, hrf, Function.update_self]
      · rw [h, hwf, Function.update_of_ne rfIdx_ne_wfIdx.symm, iterFamily_wf]
      · rw [h, hjunk, Function.update_of_ne junkIdx_ne_rfIdx, iterFamily_junk]
      · rw [h, happ jj, Function.update_of_ne (fun hc => rfIdx_ne_appIdx jj hc.symm),
          iterFamily_app, hY i]
    · rw [hout]
      exact outAcc_nil_of_parkedBlank
  · rw [← hY i]
    exact hb i hi

/-! ## The setup

Bump, load `|x|` into the loop register, evaluate the padding polynomial into
the reset register, and put `pair [] x` on the result tape. -/

@[simp] theorem parkedBlank_head : parkedBlank.head = 1 := rfl

theorem parkedBlank_cells (j : ℕ) :
    parkedBlank.cells j = if j = 0 then Γ.start else Γ.blank := by
  show ((Tape.init ([] : List Γ)).move Dir3.right).cells j = _
  rw [Tape.move_cells, initNil_cells]

theorem hasOutput_nil_parkedBlank : parkedBlank.HasOutput [] :=
  ⟨fun i hi => absurd hi (Nat.not_lt_zero i), by simp [parkedBlank_cells]⟩

/-- The tape family the emission phase starts from: `TM.applyTM`'s block blank,
the bookkeeping tapes as given. -/
def emitStart (extras : Fin (3 + (k + 2) + 0) → Tape) : Fin (3 + (k + 2) + 0) → Tape :=
  fun i => if placeWorkInMiddle 3 (k + 2) i then parkedBlank else extras i

theorem emitStart_middle (extras : Fin (3 + (k + 2) + 0) → Tape) (j : Fin (k + 2)) :
    emitStart extras (appIdx j) = parkedBlank := by
  rw [emitStart, ite_eq_left (appIdx_middle j)]

theorem emitStart_extra (extras : Fin (3 + (k + 2) + 0) → Tape)
    (i : Fin (3 + (k + 2) + 0)) (hi : ¬ placeWorkInMiddle 3 (k + 2) i) :
    emitStart extras i = extras i := by
  rw [emitStart, ite_eq_right hi]

/-- **The setup's emission phase.** From the bumped input holding `x` and an
all-blank block, `pair [] x` lands on the result tape and the whole block stays
inside `H`. -/
theorem placedEmit_hoareTime (x : List Bool) (H : ℕ) (hH : x.length + 4 ≤ H)
    (extras : Fin (3 + (k + 2) + 0) → Tape)
    (hextraSI : ∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → Tape.StartInvariant (extras i))
    (hextraH : ∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → 1 ≤ (extras i).head) :
    (placeWorkTM 3 0 (TM.retargetOutput (TM.pairInputWorkTM (Fin.last k)))).HoareTime
      (fun inp work out => inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        out = parkedBlank ∧ work = emitStart extras)
      (fun inp work out => Tape.StartInvariant inp ∧ out = parkedBlank ∧
        (work resIdx).HasOutput (pair [] x) ∧
        (∀ j : Fin (k + 2), Tape.StartInvariant (work (appIdx j)) ∧
          (work (appIdx j)).head ≤ H ∧
          ∀ c, H < c → (work (appIdx j)).cells c = Γ.blank) ∧
        (∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → work i = extras i))
      (x.length + 3) := by
  have hblankSI : Tape.StartInvariant parkedBlank := startInvariant_initNil.move Dir3.right
  have hplaced := TM.placeWorkTM_hoareTime_frame (pre := 3) (post := 0)
    (TM.retargetOutput (TM.pairInputWorkTM (Fin.last k)))
    (TM.retargetOutput_hoareTime _ (TM.pairInputWorkTM_hoareTime (Fin.last k) [] x))
    extras hextraSI hextraH
  have hconf := hoareTime_confined hplaced (emitStart extras) H
    (by simp only [TM.pairInputWorkTime, List.length_nil]; omega)
    (placeWorkInMiddle 3 (k + 2))
    (fun i => by
      by_cases hi : placeWorkInMiddle 3 (k + 2) i
      · rw [emitStart, ite_eq_left hi]; exact hblankSI
      · rw [emitStart, ite_eq_right hi]; exact hextraSI i hi)
    (fun i hi => by rw [emitStart, ite_eq_left hi, parkedBlank_head])
    (fun i hi j hj => by
      rw [emitStart, ite_eq_left hi]
      show ((Tape.init ([] : List Γ)).move Dir3.right).cells j = Γ.blank
      rw [Tape.move_cells, initNil_cells, ite_eq_right (by omega)])
  refine ((hconf.weaken_pre ?_).strengthen_post ?_).mono_bound
    (by simp only [TM.pairInputWorkTime, List.length_nil]; omega)
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨⟨⟨⟨rfl, ?_, ?_, ?_, ?_⟩, rfl⟩,
      fun i hi => emitStart_extra extras i hi⟩, rfl,
      (startInvariant_initOfBool x).move Dir3.right, hblankSI⟩
    · show (emitStart extras (appIdx (Fin.castSucc (Fin.last k)))).head = 1
      rw [emitStart_middle, parkedBlank_head]
    · show (emitStart extras (appIdx (Fin.castSucc (Fin.last k)))).HasOutput []
      rw [emitStart_middle]
      exact hasOutput_nil_parkedBlank
    · intro i
      show Tape.StartInvariant (emitStart extras (appIdx (Fin.castSucc i))) ∧
        1 ≤ (emitStart extras (appIdx (Fin.castSucc i))).head
      rw [emitStart_middle]
      exact ⟨hblankSI, le_refl 1⟩
    · show emitStart extras (appIdx (Fin.last (k + 1))) = (Tape.init []).move Dir3.right
      rw [emitStart_middle]
      rfl
  · rintro inp work out ⟨⟨⟨hout, ho⟩, hext⟩, hinpSI, -, hconf'⟩
    exact ⟨hinpSI, ho, hout, fun j => ⟨(hconf' (appIdx j)).1,
      ((hconf' (appIdx j)).2 (appIdx_middle j)).1,
      ((hconf' (appIdx j)).2 (appIdx_middle j)).2⟩, hext⟩

theorem parkedBlank_eq_regTape_zero : parkedBlank = regTape 0 := by
  refine Tape.ext rfl (funext fun j => ?_)
  rw [parkedBlank_cells, regT_cells]
  show _ = regCells 0 j
  rw [regCells]
  by_cases hj : j = 0
  · rw [ite_eq_left hj, ite_eq_left hj]
  · rw [ite_eq_right hj, ite_eq_right hj, ite_eq_right (by omega)]

/-- The register value cap the padding polynomial's evaluation runs under. -/
def polyM (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  ((polyCoeffs p).sum + 1) * (n + 1) ^ (polyCoeffs p).length + n + p.eval n

/-- The setup machine: bump every head off cell `0`, load `|x|` into the loop
register, evaluate the padding polynomial into the reset register, and emit
`pair [] x` onto the result tape. -/
def iterSetup (k : ℕ) (p : Polynomial ℕ) : TM (3 + (k + 2) + 0) :=
  seqTM (seqTM (seqTM skipTM (inputLenRegTM rfIdx)) (polyEvalTM rfIdx wfIdx junkIdx p))
    (placeWorkTM 3 0 (TM.retargetOutput (TM.pairInputWorkTM (Fin.last k))))

/-- `Complexity.iterSetup`'s time bound. -/
def setupBound (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  1 + 1 + (2 * n + 4) + 1 +
      (opBudget (polyM p n) + 1 + ((p.natDegree + 1) * (layerBudget (polyM p n) + 1) + 1)) +
    1 + (n + 3)

theorem iterSetup_hoareTime (p : Polynomial ℕ) (x : List Bool) (H : ℕ)
    (hH : H = p.eval x.length) (hHx : x.length + 4 ≤ H) :
    (iterSetup k p).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out => Tape.StartInvariant inp ∧ out = parkedBlank ∧
        (work resIdx).HasOutput (pair [] x) ∧
        (∀ j : Fin (k + 2), Tape.StartInvariant (work (appIdx j)) ∧
          (work (appIdx j)).head ≤ H ∧
          ∀ c, H < c → (work (appIdx j)).cells c = Γ.blank) ∧
        work rfIdx = regTape x.length ∧ work wfIdx = regTape H ∧ work junkIdx = regTape H)
      (setupBound p x.length) := by
  set inpx : Tape := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ with hinpx
  have hinpxP : Parked inpx :=
    ⟨le_refl 1, fun j hj => (startInvariant_initOfBool x).2 j hj⟩
  have hblankSI : Tape.StartInvariant parkedBlank := startInvariant_initNil.move Dir3.right
  set W₀ : Fin (3 + (k + 2) + 0) → Tape := fun _ => parkedBlank with hW₀
  have hW₀P : ∀ i, Parked (W₀ i) := fun _ => parked_parkedBlank
  -- phase 1: bump
  have hA : (skipTM (n := 3 + (k + 2) + 0)).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (EmitPred inpx W₀ []) 1 := by
    refine (parkAll_hoareTime (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init [])
      (Tape.init []) (startInvariant_initOfBool x) (fun _ => startInvariant_initNil)
      startInvariant_initNil).strengthen_post ?_
    rintro inp work out ⟨hi, hw, ho⟩
    refine ⟨hi, funext fun i => (hw i).trans ?_, ?_⟩
    · rw [hW₀]
      exact Tape.ext (by show max 0 1 = 1; omega) rfl
    · rw [ho]
      show OutAcc [] (⟨max 0 1, (Tape.init ([] : List Γ)).cells⟩ : Tape)
      have : (⟨max 0 1, (Tape.init ([] : List Γ)).cells⟩ : Tape) = parkedBlank :=
        Tape.ext (by show max 0 1 = 1; omega) rfl
      rw [this]
      exact outAcc_nil_of_parkedBlank
  -- phase 2: the loop register
  have hB := inputLenRegTM_hoareTime (n := 3 + (k + 2) + 0) rfIdx x W₀ []
    (fun i _ => hW₀P i) (by rw [hW₀]; exact parkedBlank_eq_regTape_zero)
  set W₁ : Fin (3 + (k + 2) + 0) → Tape :=
    Function.update W₀ rfIdx (regTape x.length) with hW₁
  have hW₁P : ∀ i, Parked (W₁ i) := by
    intro i
    by_cases hi : i = rfIdx
    · rw [hW₁, hi, Function.update_self]; exact parked_regTape _
    · rw [hW₁, Function.update_of_ne hi]; exact hW₀P i
  -- phase 3: the reset register
  have hC := polyEvalTM_hoareTime rfIdx wfIdx junkIdx rfIdx_ne_wfIdx
    (fun h => junkIdx_ne_rfIdx h.symm) junkIdx_ne_wfIdx.symm p (polyM p x.length)
    x.length 0 0 (by rw [polyM]; omega) (by omega) (by omega)
    (fun j _ => le_trans (hornerFold_take_le x.length (polyCoeffs p) j) (by rw [polyM]; omega))
    inpx W₁ [] hinpxP hW₁P (by rw [hW₁, Function.update_self])
    (by rw [hW₁, Function.update_of_ne rfIdx_ne_wfIdx.symm, hW₀]
        exact parkedBlank_eq_regTape_zero)
    (by rw [hW₁, Function.update_of_ne junkIdx_ne_rfIdx, hW₀]
        exact parkedBlank_eq_regTape_zero)
  -- phase 4: the emission
  have hfam : Function.update (Function.update W₁ junkIdx (regTape (p.eval x.length))) wfIdx
      (regTape (p.eval x.length))
      = emitStart (bookTapes (regTape x.length) (regTape H) H) := by
    funext i
    rcases layout_cases i with h | h | h | ⟨j, h⟩
    · rw [h, Function.update_of_ne rfIdx_ne_wfIdx, Function.update_of_ne junkIdx_ne_rfIdx.symm,
        hW₁, Function.update_self, emitStart_extra _ _ rfIdx_not_middle, bookTapes_rf]
    · rw [h, Function.update_self, emitStart_extra _ _ wfIdx_not_middle, bookTapes_wf, hH]
    · rw [h, Function.update_of_ne junkIdx_ne_wfIdx, Function.update_self,
        emitStart_extra _ _ junkIdx_not_middle, bookTapes_junk, hH]
    · rw [h, Function.update_of_ne (fun hc => wfIdx_ne_appIdx j hc.symm),
        Function.update_of_ne (fun hc => junkIdx_ne_appIdx j hc.symm), hW₁,
        Function.update_of_ne (fun hc => rfIdx_ne_appIdx j hc.symm), hW₀, emitStart_middle]
  have hD := placedEmit_hoareTime (k := k) x H (by omega)
    (bookTapes (regTape x.length) (regTape H) H)
    (bookTapes_startInvariant (startInvariant_regTape _) (startInvariant_regTape _))
    (bookTapes_head (parked_regTape _) (parked_regTape _))
  -- chain
  have hAB := seqTM_hoareTime _ _ hA (emitPred_transition hinpxP hW₀P []) hB
  have hBC := seqTM_hoareTime _ _ hAB (emitPred_transition hinpxP hW₁P []) hC
  refine ((seqTM_hoareTime _ _ hBC ?_ hD).strengthen_post ?_).mono_bound (by rw [setupBound])
  · rintro inp work out ⟨rfl, hw, hout⟩
    rw [hfam] at hw
    subst hw
    have houtEq := eq_parkedBlank_of_outAcc_nil hout
    have hPall : ∀ i : Fin (3 + (k + 2) + 0),
        Parked (emitStart (bookTapes (regTape x.length) (regTape H) H) i) := by
      intro i
      by_cases hi : placeWorkInMiddle 3 (k + 2) i
      · rw [emitStart, ite_eq_left hi]; exact parked_parkedBlank
      · rw [emitStart, ite_eq_right hi]
        exact ⟨bookTapes_head (parked_regTape _) (parked_regTape _) i hi,
          (bookTapes_startInvariant (startInvariant_regTape _)
            (startInvariant_regTape _) i hi).2⟩
    obtain ⟨t1, t2, t3⟩ := parked_transition (inp₀ := inpx) (out₀ := out) hinpxP hPall
      (houtEq ▸ parked_parkedBlank)
    rw [t1, t2, t3]
    exact ⟨rfl, houtEq, rfl⟩
  · rintro inp work out ⟨hinpSI, ho, hres, hbnd, hext⟩
    refine ⟨hinpSI, ho, hres, hbnd, ?_, ?_, ?_⟩
    · rw [hext rfIdx rfIdx_not_middle, bookTapes_rf]
    · rw [hext wfIdx wfIdx_not_middle, bookTapes_wf]
    · rw [hext junkIdx junkIdx_not_middle, bookTapes_junk]

/-! ## The whole machine

Setup, loop, and one final application whose output lands on the real output
tape. Over-iteration is harmless, so that last application is just one more
iteration. -/

theorem not_middle_succ_cases (i : Fin (3 + (k + 2) + 0))
    (hi : ¬ placeWorkInMiddle (post := 1) 3 (k + 1) i) :
    i = rfIdx ∨ i = wfIdx ∨ i = junkIdx ∨ i = resIdx := by
  have hlt := i.isLt
  have hres : (resIdx (k := k)).val = 3 + (k + 1) := rfl
  unfold placeWorkInMiddle at hi
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 + (k + 1) := by omega
  rcases h with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext (h.trans hres.symm))))

/-- The frame of the final application: the three bookkeeping tapes and the
result tape, which the last application no longer needs. -/
def teardownExtras (v H : ℕ) : Fin (3 + (k + 2) + 0) → Tape :=
  fun i => if i = resIdx then parkedBlank else bookTapes (regTape v) (regTape H) H i

/-- Setup, loop, and the final application. -/
def iterMain (M : TM k) : TM (3 + (k + 2) + 0) :=
  seqTM (seqTM (iterTail k) (forRegTM (iterBody M) rfIdx))
    (placeWorkTM 3 1 (TM.retargetInputStarted M))

/-- **The main run.** From the result tape carrying the initial value, the
machine iterates `v + 1` times and writes the last value to the real output. -/
theorem iterMain_hoareTime (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (H : ℕ) (v : ℕ)
    (Y : ℕ → List Bool) (hY : ∀ i, Y (i + 1) = G (Y i))
    (hlen : ∀ i, i ≤ v → (Y i).length + 1 ≤ H)
    (hT : ∀ i, i < v → 1 + T (Y i).length ≤ H)
    (b_iter : ℕ)
    (hb : ∀ i, i < v → T (Y i).length + 1 + tailBound k H (Y (i + 1)).length ≤ b_iter) :
    (iterMain M).HoareTime
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧ out = parkedBlank ∧
        (work resIdx).HasOutput (Y 0) ∧
        (∀ j : Fin (k + 2), Tape.StartInvariant (work (appIdx j)) ∧
          (work (appIdx j)).head ≤ H ∧
          ∀ c, H < c → (work (appIdx j)).cells c = Γ.blank) ∧
        work rfIdx = regTape v ∧ work wfIdx = regTape H ∧ work junkIdx = regTape H)
      (fun _inp _work out => out.HasOutput (G (Y v)))
      (tailBound k H (Y 0).length + 1 + (v * (b_iter + 2) + (v + 2)) + 1 + T (Y v).length) := by
  rw [iterMain]
  intro inp work out hpre
  obtain ⟨hinpP, hinpSI, ho, hres, hbnd, hrf, hwf, hjunk⟩ := hpre
  have hregP := parked_regTape H
  have hregSI := startInvariant_regTape H
  have hfamP : ∀ (i : ℕ) (j : Fin (3 + (k + 2) + 0)),
      Parked (iterFamily M Y inp (regTape H) v H i j) := by
    intro i j
    by_cases hj : j = rfIdx
    · rw [hj, iterFamily_rf]; exact parked_regTape v
    · exact iterFamily_parked hregP i j hj
  -- the tail, the loop, and the final application
  have h1 := iterTail_hoareTime M H (Y 0) (hlen 0 (by omega)) inp hinpP hinpSI
    (regTape v) (regTape H) (parked_regTape v) (startInvariant_regTape v) hregP hregSI
  have h2 := iterLoop_hoareTime (M := M) (Y := Y) (inp₀ := inp) (junkT := regTape H)
    (v := v) (H := H) hcomp hY hlen hT b_iter hb hinpP hinpSI hregP hregSI
  have h3 := TM.placeWorkTM_hoareTime_frame (pre := 3) (post := 1)
    (TM.retargetInputStarted M) (TM.retargetInputStarted_hoareTime M hcomp (Y v))
    (teardownExtras v H)
    (fun i hi => by
      rcases not_middle_succ_cases i hi with h | h | h | h
      · rw [h, teardownExtras, ite_eq_right rfIdx_ne_resIdx, bookTapes_rf]
        exact startInvariant_regTape v
      · rw [h, teardownExtras, ite_eq_right wfIdx_ne_resIdx, bookTapes_wf]; exact hregSI
      · rw [h, teardownExtras, ite_eq_right junkIdx_ne_resIdx, bookTapes_junk]; exact hregSI
      · rw [h, teardownExtras, ite_eq_left rfl]
        exact startInvariant_initNil.move Dir3.right)
    (fun i hi => by
      rcases not_middle_succ_cases i hi with h | h | h | h
      · rw [h, teardownExtras, ite_eq_right rfIdx_ne_resIdx, bookTapes_rf]
        exact (parked_regTape v).1
      · rw [h, teardownExtras, ite_eq_right wfIdx_ne_resIdx, bookTapes_wf]; exact hregP.1
      · rw [h, teardownExtras, ite_eq_right junkIdx_ne_resIdx, bookTapes_junk]; exact hregP.1
      · rw [h, teardownExtras, ite_eq_left rfl]; exact parked_parkedBlank.1)
  -- the two seams are the identity: every tape is parked
  have hseam : ∀ (W : Fin (3 + (k + 2) + 0) → Tape), (∀ i, Parked (W i)) →
      ∀ (inp' : Tape) (out' : Tape), inp' = inp → out' = parkedBlank →
      transitionInput inp' = inp ∧ (fun i => transitionTape (W i)) = W ∧
        transitionTape out' = parkedBlank := by
    rintro W hW inp' out' rfl rfl
    exact parked_transition hinpP hW parked_parkedBlank
  have h12 := seqTM_hoareTime _ _ h1 (by
    rintro inp' work' out' ⟨rfl, rfl, hrf', hjunk', hwf', happ'⟩
    have hWP : ∀ i, Parked (work' i) := by
      intro i
      rcases layout_cases i with h | h | h | ⟨j, h⟩
      · rw [h, hrf']; exact parked_regTape v
      · rw [h, hwf']; exact hregP
      · rw [h, hjunk']; exact hregP
      · rw [h, happ' j]
        exact ⟨le_of_eq (TM.applyPre_head M (Y 0) _ j).symm,
          fun c hc => (TM.applyPre_startInvariant M (Y 0) _ j).2 c hc⟩
    obtain ⟨t1, t2, t3⟩ := hseam work' hWP inp' parkedBlank rfl rfl
    rw [t1, t2, t3]
    refine ⟨rfl, funext fun i => ?_, outAcc_nil_of_parkedBlank⟩
    rcases layout_cases i with h | h | h | ⟨j, h⟩
    · rw [h, hrf', iterFamily_rf]
    · rw [h, hwf', iterFamily_wf]
    · rw [h, hjunk', iterFamily_junk]
    · rw [h, happ' j, iterFamily_app]) h2
  refine (seqTM_hoareTime _ _ h12 ?_ h3).strengthen_post
    (post' := fun _inp _work out => out.HasOutput (G (Y v))) ?_ inp work out
    ⟨rfl, ho, hres, hbnd, hrf, hwf, hjunk⟩
  · rintro inp' work' out' ⟨rfl, rfl, hout'⟩
    obtain ⟨t1, t2, t3⟩ := hseam _ (hfamP v) inp' out'
      rfl (eq_parkedBlank_of_outAcc_nil hout')
    rw [t1, t2, t3]
    refine ⟨⟨funext fun i => ?_, rfl⟩, fun i hi => ?_⟩
    · show iterFamily M Y inp' (regTape H) v H v (appIdx (Fin.castSucc i)) = _
      rw [iterFamily_app]
      exact congrFun (TM.applyPre_spec M (Y v) inp').1 i
    · rcases not_middle_succ_cases i hi with h | h | h | h
      · rw [h, iterFamily_rf, teardownExtras, ite_eq_right rfIdx_ne_resIdx, bookTapes_rf]
      · rw [h, iterFamily_wf, teardownExtras, ite_eq_right wfIdx_ne_resIdx, bookTapes_wf]
      · rw [h, iterFamily_junk, teardownExtras, ite_eq_right junkIdx_ne_resIdx, bookTapes_junk]
      · rw [h, show (resIdx (k := k)) = appIdx (Fin.last (k + 1)) from rfl, iterFamily_app,
          teardownExtras, ite_eq_left (show appIdx (Fin.last (k + 1)) = resIdx from rfl),
          TM.applyPre, Fin.snoc_last]
  · rintro inp' work' out' ⟨hout, -⟩
    exact hout

/-- The complete iteration machine. -/
def iterTM (M : TM k) (p : Polynomial ℕ) : TM (3 + (k + 2) + 0) :=
  seqTM (iterSetup k p) (iterMain M)

theorem tailBound_mono (k H : ℕ) {m m' : ℕ} (h : m ≤ m') :
    tailBound k H m ≤ tailBound k H m' := by
  rw [tailBound, tailBound]; omega

/-- `Complexity.iterTM`'s time bound. -/
def iterBound (k : ℕ) (tp p r : Polynomial ℕ) (n : ℕ) : ℕ :=
  setupBound p n + 1 +
    (tailBound k (p.eval n) (n + 2) + 1 +
      (n * (tp.eval (r.eval n) + 1 + tailBound k (p.eval n) (r.eval n) + 2) + (n + 2)) + 1 +
      tp.eval (r.eval n))

/-- **The iteration machine computes the iterate.** On input `x` it applies `G`
to `pair [] x` exactly `|x| + 1` times, provided the padding polynomial `p`
dominates the length bound `r` and the source machine's own bound `tp`. -/
theorem iterTM_computesInTime (M : TM k) {G : List Bool → List Bool} {tp : Polynomial ℕ}
    (hcomp : M.ComputesInTime G tp.eval) (p r : Polynomial ℕ)
    (hp₁ : ∀ n, n + 4 ≤ p.eval n) (hp₂ : ∀ n, r.eval n + 1 ≤ p.eval n)
    (hp₃ : ∀ n, 1 + tp.eval (r.eval n) ≤ p.eval n)
    (hr : ∀ (x : List Bool), ∀ i ≤ x.length, (G^[i] (pair [] x)).length ≤ r.eval x.length) :
    (iterTM M p).ComputesInTime (fun x => G^[x.length + 1] (pair [] x))
      (iterBound k tp p r) := by
  intro x
  set n := x.length with hn
  set H := p.eval n with hH
  set Y : ℕ → List Bool := fun i => G^[i] (pair [] x) with hY0
  have hYsucc : ∀ i, Y (i + 1) = G (Y i) := by
    intro i
    rw [hY0]
    exact Function.iterate_succ_apply' G i (pair [] x)
  have hYlen : ∀ i, i ≤ n → (Y i).length ≤ r.eval n := fun i hi => hr x i hi
  have hHpos : 1 ≤ H := by have := hp₁ n; omega
  have hlen : ∀ i, i ≤ n → (Y i).length + 1 ≤ H := by
    intro i hi
    have := hYlen i hi
    have := hp₂ n
    omega
  have hTle : ∀ i, i ≤ n → tp.eval (Y i).length ≤ tp.eval (r.eval n) := fun i hi =>
    polynomial_eval_mono_nat tp (hYlen i hi)
  have hsetup := iterSetup_hoareTime (k := k) p x H rfl (by have := hp₁ n; omega)
  have hmain := iterMain_hoareTime M hcomp H n Y hYsucc hlen
    (fun i hi => by have := hTle i (by omega); have := hp₃ n; omega)
    (tp.eval (r.eval n) + 1 + tailBound k H (r.eval n))
    (fun i hi => by
      have h1 := hTle i (by omega)
      have h2 := tailBound_mono k H (hYlen (i + 1) (by omega))
      omega)
  have hseam : ∀ (inp : Tape) (work : Fin (3 + (k + 2) + 0) → Tape) (out : Tape),
      (Tape.StartInvariant inp ∧ out = parkedBlank ∧
        (work resIdx).HasOutput (pair [] x) ∧
        (∀ j : Fin (k + 2), Tape.StartInvariant (work (appIdx j)) ∧
          (work (appIdx j)).head ≤ H ∧
          ∀ c, H < c → (work (appIdx j)).cells c = Γ.blank) ∧
        work rfIdx = regTape n ∧ work wfIdx = regTape H ∧ work junkIdx = regTape H) →
      (Parked (transitionInput inp) ∧ Tape.StartInvariant (transitionInput inp) ∧
        transitionTape out = parkedBlank ∧
        ((fun i => transitionTape (work i)) resIdx).HasOutput (Y 0) ∧
        (∀ j : Fin (k + 2),
          Tape.StartInvariant ((fun i => transitionTape (work i)) (appIdx j)) ∧
          ((fun i => transitionTape (work i)) (appIdx j)).head ≤ H ∧
          ∀ c, H < c → ((fun i => transitionTape (work i)) (appIdx j)).cells c = Γ.blank) ∧
        (fun i => transitionTape (work i)) rfIdx = regTape n ∧
        (fun i => transitionTape (work i)) wfIdx = regTape H ∧
        (fun i => transitionTape (work i)) junkIdx = regTape H) := by
    rintro inp work out ⟨hinpSI, rfl, hres, hbnd, hrf, hwf, hjunk⟩
    dsimp only
    have hinpEq : transitionInput inp = (⟨max inp.head 1, inp.cells⟩ : Tape) :=
      move_idleDir_eq_of_startInvariant hinpSI
    refine ⟨?_, ?_, transitionTape_eq_self parked_parkedBlank.read_ne_start, ?_,
      fun j => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hinpEq]; exact ⟨le_max_right _ _, fun c hc => hinpSI.2 c hc⟩
    · rw [hinpEq]; exact ⟨hinpSI.1, fun c hc => hinpSI.2 c hc⟩
    · exact (Tape.hasOutput_congr
        (transitionTape_cells _ (fun c hc => (hbnd (Fin.last (k + 1))).1.2 c hc)).symm _).mp hres
    · refine ⟨?_, fun c hc => ?_⟩
      · rw [transitionTape_cells _ (fun c' hc' => (hbnd j).1.2 c' hc')]
        exact (hbnd j).1.1
      · rw [transitionTape_cells _ (fun c' hc' => (hbnd j).1.2 c' hc')]
        exact (hbnd j).1.2 c hc
    · rw [transitionTape_of_startInvariant (hbnd j).1]
      show max (work (appIdx j)).head 1 ≤ H
      have := (hbnd j).2.1
      omega
    · intro c hc
      rw [transitionTape_cells _ (fun c' hc' => (hbnd j).1.2 c' hc')]
      exact (hbnd j).2.2 c hc
    · show transitionTape (work rfIdx) = regTape n
      rw [hrf]; exact transitionTape_eq_self (parked_regTape n).read_ne_start
    · show transitionTape (work wfIdx) = regTape H
      rw [hwf]; exact transitionTape_eq_self (parked_regTape H).read_ne_start
    · show transitionTape (work junkIdx) = regTape H
      rw [hjunk]; exact transitionTape_eq_self (parked_regTape H).read_ne_start
  have hfull := seqTM_hoareTime _ _ hsetup hseam hmain
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := hfull (Tape.init (x.map Γ.ofBool))
    (fun _ => Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
  have hY0len : (Y 0).length = n + 2 := by
    rw [hY0]
    show (pair [] x).length = n + 2
    rw [pair_length]
    simp
    omega
  refine ⟨c', t, ?_, hreach, hhalt, ?_⟩
  · refine le_trans ht ?_
    rw [iterBound, hY0len]
    simp only [← hn, hH]
    have := hTle n le_rfl
    omega
  · show c'.output.HasOutput (G^[x.length + 1] (pair [] x))
    rw [Function.iterate_succ_apply']
    exact hpost

/-! ## Polynomial bounds

`Complexity.iterBound` is a sum of products of polynomial evaluations, so the
closure API of `Complexitylib.Asymptotics.PolyBound` bounds it directly. -/

theorem polyBound_iterBound (k : ℕ) (tp p r : Polynomial ℕ) :
    PolyBound (iterBound k tp p r) := by
  have hcomp : PolyBound (fun n => tp.eval (r.eval n)) :=
    PolyBound.mono (PolyBound.eval (tp.comp r))
      (fun n => le_of_eq (by rw [Polynomial.eval_comp]))
  have hp : PolyBound (fun n => p.eval n) := PolyBound.eval p
  have hr : PolyBound (fun n => r.eval n) := PolyBound.eval r
  have hpow : PolyBound (fun n => (n + 1) ^ (polyCoeffs p).length) :=
    PolyBound.pow (PolyBound.add PolyBound.id (PolyBound.const 1)) _
  have hM : PolyBound (fun n => polyM p n) := by
    rw [show (fun n => polyM p n) = fun n =>
      ((polyCoeffs p).sum + 1) * (n + 1) ^ (polyCoeffs p).length + n + p.eval n from rfl]
    exact PolyBound.add (PolyBound.add (PolyBound.mul (PolyBound.const _) hpow) PolyBound.id) hp
  have hop : PolyBound (fun n => opBudget (polyM p n)) := by
    rw [show (fun n => opBudget (polyM p n)) = fun n =>
      32 * ((polyM p n + 2) * (polyM p n + 2) * (polyM p n + 2)) from rfl]
    exact PolyBound.mul (PolyBound.const _)
      (PolyBound.mul (PolyBound.mul (PolyBound.add hM (PolyBound.const _))
        (PolyBound.add hM (PolyBound.const _))) (PolyBound.add hM (PolyBound.const _)))
  have hlayer : PolyBound (fun n => layerBudget (polyM p n)) := by
    rw [show (fun n => layerBudget (polyM p n)) = fun n =>
      4 * opBudget (polyM p n) + 3 from rfl]
    exact PolyBound.add (PolyBound.mul (PolyBound.const _) hop) (PolyBound.const _)
  have hsetup : PolyBound (setupBound p) := by
    rw [show setupBound p = fun n => 1 + 1 + (2 * n + 4) + 1 +
        (opBudget (polyM p n) + 1 +
          ((p.natDegree + 1) * (layerBudget (polyM p n) + 1) + 1)) + 1 + (n + 3) from rfl]
    exact PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      (PolyBound.add (PolyBound.const _) (PolyBound.const _))
      (PolyBound.add (PolyBound.mul (PolyBound.const 2) PolyBound.id) (PolyBound.const _)))
      (PolyBound.const _))
      (PolyBound.add (PolyBound.add hop (PolyBound.const _))
        (PolyBound.add
          (PolyBound.mul (PolyBound.const _) (PolyBound.add hlayer (PolyBound.const _)))
          (PolyBound.const _))))
      (PolyBound.const _)) (PolyBound.add PolyBound.id (PolyBound.const _))
  have htail : ∀ m : ℕ → ℕ, PolyBound m →
      PolyBound (fun n => tailBound k (p.eval n) (m n)) := by
    intro m hm
    rw [show (fun n => tailBound k (p.eval n) (m n)) = fun n =>
      1 + 1 + (p.eval n + 1 + 2) + 1 +
        ((k + 1) * (p.eval n + 4) + p.eval n * 4 + 8 + 1 + ((k + 1) * (p.eval n + 4) + 1)) + 1 +
      (2 * m n + 5 + 1 +
        (1 * (p.eval n + 4) + p.eval n * 4 + 8 + 1 + (1 * (p.eval n + 4) + 1))) from rfl]
    have hbase : PolyBound (fun n => p.eval n + 4) := PolyBound.add hp (PolyBound.const _)
    have hk : PolyBound (fun n => (k + 1) * (p.eval n + 4)) :=
      PolyBound.mul (PolyBound.const _) hbase
    have h1 : PolyBound (fun n => 1 * (p.eval n + 4)) := PolyBound.mul (PolyBound.const _) hbase
    have h4 : PolyBound (fun n => p.eval n * 4) := PolyBound.mul hp (PolyBound.const _)
    exact PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      (PolyBound.add (PolyBound.const _) (PolyBound.const _))
      (PolyBound.add (PolyBound.add hp (PolyBound.const _)) (PolyBound.const _)))
      (PolyBound.const _))
      (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add hk h4) (PolyBound.const _))
        (PolyBound.const _)) (PolyBound.add hk (PolyBound.const _)))) (PolyBound.const _))
      (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.mul (PolyBound.const 2) hm)
        (PolyBound.const _)) (PolyBound.const _))
        (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add h1 h4) (PolyBound.const _))
          (PolyBound.const _)) (PolyBound.add h1 (PolyBound.const _))))
  rw [show iterBound k tp p r = fun n => setupBound p n + 1 +
      (tailBound k (p.eval n) (n + 2) + 1 +
        (n * (tp.eval (r.eval n) + 1 + tailBound k (p.eval n) (r.eval n) + 2) + (n + 2)) + 1 +
        tp.eval (r.eval n)) from rfl]
  exact PolyBound.add (PolyBound.add hsetup (PolyBound.const _))
    (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      (htail _ (PolyBound.add PolyBound.id (PolyBound.const _))) (PolyBound.const _))
      (PolyBound.add (PolyBound.mul PolyBound.id (PolyBound.add (PolyBound.add (PolyBound.add hcomp
        (PolyBound.const _)) (htail _ hr)) (PolyBound.const _)))
        (PolyBound.add PolyBound.id (PolyBound.const _)))) (PolyBound.const _)) hcomp)

/-- **`FP` is closed under iterating a polynomial-time function once per input
bit**, provided every intermediate value stays polynomially bounded. -/
theorem iterate_input_mem_FP {G : List Bool → List Bool} (hG : G ∈ FP) (r : Polynomial ℕ)
    (hr : ∀ (x : List Bool), ∀ i ≤ x.length, (G^[i] (pair [] x)).length ≤ r.eval x.length) :
    (fun x => G^[x.length + 1] (pair [] x)) ∈ FP := by
  obtain ⟨k, M, tp, hcomp⟩ := mem_FP_iff_computesInTime_polynomial.mp hG
  set p : Polynomial ℕ :=
    Polynomial.X + Polynomial.C 4 + r + Polynomial.C 1 + tp.comp r + Polynomial.C 1 with hpdef
  have hpeval : ∀ n, p.eval n = n + 4 + r.eval n + 1 + tp.eval (r.eval n) + 1 := by
    intro n
    rw [hpdef]
    simp [Polynomial.eval_comp]
  obtain ⟨d, hd⟩ := (polyBound_iterBound k tp p r).bigO
  exact ⟨d, 3 + (k + 2) + 0, iterTM M p, iterBound k tp p r,
    iterTM_computesInTime M hcomp p r (fun n => by rw [hpeval]; omega)
      (fun n => by rw [hpeval]; omega) (fun n => by rw [hpeval]; omega) hr, hd⟩

end Complexity
