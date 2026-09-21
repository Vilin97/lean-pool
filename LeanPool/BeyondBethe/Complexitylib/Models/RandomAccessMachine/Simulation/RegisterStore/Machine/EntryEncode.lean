/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryEncode.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryEncode.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.RetargetOutput

/-!
# Sparse entry emission
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Emit exactly `Entry.encode entry` from distinct canonical address and value
work tapes, with a literal frame around those sources. -/
theorem entryEncodeTM_hoareTime_frame {n : ℕ}
    (tapes : EntryEncodeTapes n) (entry : Entry) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (haddress : (work₀ tapes.address).HasBinaryNat entry.1)
    (hvalue : (work₀ tapes.value).HasBinaryNat entry.2)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ tapes.address → i ≠ tapes.value →
      TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (entryEncodeTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work tapes.address).HasBinarySuffix [] ∧
        (work tapes.address).cells = (work₀ tapes.address).cells ∧
        (work tapes.address).head = entry.1.bits.length + 1 ∧
        (work tapes.value).HasBinarySuffix [] ∧
        (work tapes.value).cells = (work₀ tapes.value).cells ∧
        (work tapes.value).head = entry.2.bits.length + 1 ∧
        (∀ i, i ≠ tapes.address → i ≠ tapes.value → work i = work₀ i) ∧
        out.HasBinaryPrefix (emitted ++ Entry.encode entry))
      (entryEncodeTime entry) :=
  entryEncodeTM_hoareTime_frame_internal tapes entry emitted inp₀ work₀ out₀
    haddress hvalue hinput hother houtput

/-- Rewind arbitrary bounded decoded address/value cursors and emit exactly
`Entry.encode entry`, retaining a literal frame around both sources. -/
theorem rewindEntryEncodeTM_hoareTime_frame {n : ℕ}
    (tapes : EntryEncodeTapes n) (entry : Entry)
    (addressHeadBound valueHeadBound : ℕ) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (haddress : (work₀ tapes.address).HasBinaryContent entry.1.bits)
    (haddressStart : (work₀ tapes.address).cells 0 = Γ.start)
    (haddressHead : 1 ≤ (work₀ tapes.address).head ∧
      (work₀ tapes.address).head ≤ addressHeadBound)
    (hvalue : (work₀ tapes.value).HasBinaryContent entry.2.bits)
    (hvalueStart : (work₀ tapes.value).cells 0 = Γ.start)
    (hvalueHead : 1 ≤ (work₀ tapes.value).head ∧
      (work₀ tapes.value).head ≤ valueHeadBound)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ tapes.address → i ≠ tapes.value →
      TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (rewindEntryEncodeTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work tapes.address).HasBinarySuffix [] ∧
        (work tapes.address).cells = (work₀ tapes.address).cells ∧
        (work tapes.address).head = entry.1.bits.length + 1 ∧
        (work tapes.value).HasBinarySuffix [] ∧
        (work tapes.value).cells = (work₀ tapes.value).cells ∧
        (work tapes.value).head = entry.2.bits.length + 1 ∧
        (∀ i, i ≠ tapes.address → i ≠ tapes.value → work i = work₀ i) ∧
        out.HasBinaryPrefix (emitted ++ Entry.encode entry))
      (rewindEntryEncodeTime entry addressHeadBound valueHeadBound) :=
  rewindEntryEncodeTM_hoareTime_frame_internal tapes entry addressHeadBound
    valueHeadBound emitted inp₀ work₀ out₀ haddress haddressStart
    haddressHead hvalue hvalueStart hvalueHead hinput hother houtput

/-- Emit one entry from canonical address/value sources, then restore the
entire work family exactly. -/
theorem rewindEntryEncodeRestoreTM_hoareTime_frame {n : ℕ}
    (tapes : EntryEncodeTapes n) (entry : Entry) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (haddress : (work₀ tapes.address).HasBinaryNat entry.1)
    (hvalue : (work₀ tapes.value).HasBinaryNat entry.2)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ tapes.address → i ≠ tapes.value →
      TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (rewindEntryEncodeRestoreTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out.HasBinaryPrefix (emitted ++ Entry.encode entry))
      (rewindEntryEncodeRestoreTime entry) :=
  rewindEntryEncodeRestoreTM_hoareTime_frame_internal tapes entry emitted
    inp₀ work₀ out₀ haddress hvalue hinput hother houtput

/-- Redirect restored entry emission into the fresh last work tape. All base
work tapes are restored exactly and the real output remains standard blank. -/
theorem rewindEntryEncodeRestoreTM_retargetOutput_hoareTime_frame {n : ℕ}
    (tapes : EntryEncodeTapes n) (entry : Entry) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin (n + 1) → Tape)
    (haddress : (work₀ (Fin.castSucc tapes.address)).HasBinaryNat entry.1)
    (hvalue : (work₀ (Fin.castSucc tapes.value)).HasBinaryNat entry.2)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ tapes.address → i ≠ tapes.value →
      TM.Parked (work₀ (Fin.castSucc i)))
    (hbuffer : (work₀ (Fin.last n)).HasBinaryPrefix emitted) :
    (rewindEntryEncodeRestoreTM tapes).retargetOutput.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
          out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ Fin.last n → work i = work₀ i) ∧
        (work (Fin.last n)).HasBinaryPrefix
          (emitted ++ Entry.encode entry) ∧
        out = (Tape.init []).move Dir3.right)
      (rewindEntryEncodeRestoreTime entry) := by
  let baseWork : Fin n → Tape := fun i => work₀ (Fin.castSucc i)
  have hbase := rewindEntryEncodeRestoreTM_hoareTime_frame tapes entry emitted
    inp₀ baseWork (work₀ (Fin.last n)) haddress hvalue hinput hother hbuffer
  have hlift := TM.retargetOutput_hoareTime
    (rewindEntryEncodeRestoreTM tapes) hbase
  apply hlift.consequence
  · rintro inp work out ⟨hinp, hwork, hout⟩
    subst inp
    subst work
    exact ⟨⟨rfl, rfl, rfl⟩, hout⟩
  · intro inp work out hpost
    rcases hpost with ⟨⟨hinp, hbaseWork, hbuffer'⟩, hout⟩
    refine ⟨hinp, ?_, hbuffer', hout⟩
    intro i hi
    have hil : i.val < n := by
      have hle : i.val ≤ n := by omega
      have hne : i.val ≠ n := by
        intro hval
        apply hi
        apply Fin.ext
        simpa using hval
      omega
    let j : Fin n := ⟨i.val, hil⟩
    have hij : i = Fin.castSucc j := by
      apply Fin.ext
      rfl
    rw [hij]
    exact congrFun hbaseWork j
  · exact le_rfl

/-- Entry emission is append-only on the output tape. -/
theorem entryEncodeTM_isTransducer {n : ℕ} (tapes : EntryEncodeTapes n) :
    (entryEncodeTM tapes).IsTransducer :=
  (wordEncodeTM_isTransducer tapes.address).seqTM
    (wordEncodeTM_isTransducer tapes.value)

/-- Rewind-and-emit entry encoding is append-only on the output tape. -/
theorem rewindEntryEncodeTM_isTransducer {n : ℕ}
    (tapes : EntryEncodeTapes n) :
    (rewindEntryEncodeTM tapes).IsTransducer :=
  (rewindWordEncodeTM_isTransducer tapes.address).seqTM
    (rewindWordEncodeTM_isTransducer tapes.value)

/-- Coarse all-prefix auxiliary-space envelope for entry emission. -/
theorem entryEncodeTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryEncodeTapes n) (entry : Entry)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryEncodeTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryEncodeTM tapes).reachesIn time start current)
    (htime : time ≤ entryEncodeTime entry) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryEncodeTime entry) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Coarse all-prefix envelope for rewind-and-emit entry encoding. -/
theorem rewindEntryEncodeTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryEncodeTapes n) (entry : Entry)
    (addressHeadBound valueHeadBound inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (rewindEntryEncodeTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (rewindEntryEncodeTM tapes).reachesIn time start current)
    (htime : time ≤
      rewindEntryEncodeTime entry addressHeadBound valueHeadBound) :
    current.WithinAuxSpace inputLength
      (initialSpace +
        rewindEntryEncodeTime entry addressHeadBound valueHeadBound) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
