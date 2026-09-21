/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.TaggedDefs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Defs

/-!
# Positive-tag sparse updates -- proof internals
-/


public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

private theorem hasBinaryPrefix_parked {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t := by
  refine ⟨by rw [h.1]; omega, ?_⟩
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  by_cases hi : i < bits.length
  · rw [h.2.1 i hi]
    exact Γ.ofBool_ne_start _
  · rw [h.2.2 i (Nat.le_of_not_gt hi)]
    decide

theorem taggedEntryUpdateTM_hoareTime_frame_internal
    (tapes : EntryUpdateTapes n) (overlay : Store) (address value : ℕ)
    (emittedBits : List Bool) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape) (hcanonical : Canonical overlay)
    (hready : EntryScanReady tapes.entry (overlay.flatMap Entry.encode)
      address.bits initialWork initialWork)
    (hreplacement : (initialWork tapes.replacement).HasBinaryNat value)
    (hremaining :
      (initialWork tapes.remaining).HasBinaryNat overlay.length)
    (hfound : (initialWork tapes.found).HasBinaryNat 0)
    (hresultCount :
      (initialWork tapes.resultCount).HasBinaryNat overlay.length)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (taggedEntryUpdateTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        TaggedEntryUpdateResult tapes overlay address value initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay address value).flatMap Entry.encode))
      (taggedEntryUpdateTime tapes overlay address value) := by
  have houtputParked := hasBinaryPrefix_parked houtput
  have hsucc := TM.binarySuccTM_hoareTime_frame tapes.replacement value
    inp₀ initialWork out₀ hreplacement hinput.read_ne_start
    (fun i _ => (hready.parked i).read_ne_start)
    houtputParked.read_ne_start
  let taggedPost : TM.TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (∀ i, i ≠ tapes.replacement → work i = initialWork i) ∧
    (work tapes.replacement).HasBinaryNat (value + 1) ∧ out = out₀
  let finalPost : TM.TapePred n := fun inp work out =>
    inp = inp₀ ∧
    TaggedEntryUpdateResult tapes overlay address value initialWork work ∧
    out.HasBinaryPrefix
      (emittedBits ++
        (DenseOverlay.write overlay address value).flatMap Entry.encode)
  have hupdate : (entryUpdateTM tapes).HoareTime taggedPost finalPost
      (entryUpdateTime tapes overlay address (value + 1)) := by
    rintro inp work out ⟨hinp, hother, htag, hout⟩
    have hslotEq (slot : Fin 13) (hne : slot ≠ 10) :
        work (tapes.idx slot) = initialWork (tapes.idx slot) :=
      hother _ (tapes.ne hne)
    have hready' : EntryScanReady tapes.entry
        (overlay.flatMap Entry.encode) address.bits work work := by
      refine
        { source := ?_
          address := ?_
          addressStart := ?_
          value := ?_
          valueStart := ?_
          addressCounter := ?_
          addressWidth := ?_
          valueCounter := ?_
          valueWidth := ?_
          query := ?_
          queryStart := ?_
          result := ?_
          resultStart := ?_
          parked := ?_
          frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
      · change (work (tapes.idx 0)).HasBinarySuffix _
        rw [hslotEq 0 (by decide)]
        exact hready.source
      · change (work (tapes.idx 1)).HasBinaryPrefix []
        rw [hslotEq 1 (by decide)]
        exact hready.address
      · change (work (tapes.idx 1)).cells 0 = Γ.start
        rw [hslotEq 1 (by decide)]
        exact hready.addressStart
      · change (work (tapes.idx 2)).HasBinaryPrefix []
        rw [hslotEq 2 (by decide)]
        exact hready.value
      · change (work (tapes.idx 2)).cells 0 = Γ.start
        rw [hslotEq 2 (by decide)]
        exact hready.valueStart
      · change (work (tapes.idx 3)).HasBinaryNat 0
        rw [hslotEq 3 (by decide)]
        exact hready.addressCounter
      · change (work (tapes.idx 4)).HasBinaryNat 0
        rw [hslotEq 4 (by decide)]
        exact hready.addressWidth
      · change (work (tapes.idx 5)).HasBinaryNat 0
        rw [hslotEq 5 (by decide)]
        exact hready.valueCounter
      · change (work (tapes.idx 6)).HasBinaryNat 0
        rw [hslotEq 6 (by decide)]
        exact hready.valueWidth
      · change (work (tapes.idx 7)).HasBinaryString address.bits
        rw [hslotEq 7 (by decide)]
        exact hready.query
      · change (work (tapes.idx 7)).cells 0 = Γ.start
        rw [hslotEq 7 (by decide)]
        exact hready.queryStart
      · change (work (tapes.idx 8)).HasBinaryPrefix []
        rw [hslotEq 8 (by decide)]
        exact hready.result
      · change (work (tapes.idx 8)).cells 0 = Γ.start
        rw [hslotEq 8 (by decide)]
        exact hready.resultStart
      · intro i
        by_cases hi : i = tapes.replacement
        · subst i
          exact ⟨by rw [htag.2.1],
            htag.2.hasBinaryContent.cells_ne_start⟩
        · rw [hother i hi]
          exact hready.parked i
    have hremaining' : (work tapes.remaining).HasBinaryNat overlay.length := by
      change (work (tapes.idx 9)).HasBinaryNat _
      rw [hslotEq 9 (by decide)]
      exact hremaining
    have hfound' : (work tapes.found).HasBinaryNat 0 := by
      change (work (tapes.idx 11)).HasBinaryNat 0
      rw [hslotEq 11 (by decide)]
      exact hfound
    have hresultCount' :
        (work tapes.resultCount).HasBinaryNat overlay.length := by
      change (work (tapes.idx 12)).HasBinaryNat _
      rw [hslotEq 12 (by decide)]
      exact hresultCount
    have hrun := entryUpdateTM_hoareTime_frame tapes overlay address
      (value + 1) emittedBits work inp₀ out₀ hcanonical hready' htag
      hremaining' hfound' hresultCount' hinput houtput
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        houtcome, hfinalOutput, hsource⟩ :=
      hrun inp work out ⟨hinp, rfl, hout⟩
    have hsourceInitial :
        work tapes.entry.source = initialWork tapes.entry.source :=
      hother _ (tapes.ne (by decide))
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨work, htag, hother, houtcome,
        hsource.trans (congrArg Tape.cells hsourceInitial)⟩,
      by simpa only [DenseOverlay.write] using hfinalOutput⟩
  have htransition : ∀ inp work out, taggedPost inp work out →
      taggedPost (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    rintro inp work out ⟨hinp, hother, htag, hout⟩
    have hworkParked : ∀ i, TM.Parked (work i) := by
      intro i
      by_cases hi : i = tapes.replacement
      · subst i
        exact ⟨by rw [htag.2.1],
          htag.2.hasBinaryContent.cells_ne_start⟩
      · rw [hother i hi]
        exact hready.parked i
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      (inp := inp) (work := work) (out := out)
      (by simpa [hinp] using hinput.read_ne_start)
      (fun i => (hworkParked i).read_ne_start)
      (by simpa [hout] using houtputParked.read_ne_start)
    rw [hi, hw, ho]
    exact ⟨hinp, hother, htag, hout⟩
  have hall := TM.seqTM_hoareTime (TM.binarySuccTM tapes.replacement)
    (entryUpdateTM tapes) hsucc htransition hupdate
  simpa [taggedEntryUpdateTM, taggedEntryUpdateTime, taggedPost, finalPost]
    using hall

end Machine
end RegisterStore
end RAM
end Complexity
