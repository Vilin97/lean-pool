/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordDecode.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordDecode.Internal
public import
LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordDecode.LinearInternal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Defs

/-!
# RAM snapshot word-width decoder

This module exposes the exact framed semantics of the first concrete snapshot
decoder phase. Starting on a self-delimiting word, `wordWidthTM` stops on its
zero separator and leaves the unary-prefix length as a canonical binary
natural on a separate work tape.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Rewind a decoded append-position target to cell one without changing its
binary contents or any framed tape. This converts `HasBinaryPrefix` into the
read-position convention `HasBinaryString` in at most `|bits| + 3` steps. -/
theorem wordTargetRewind_reachesIn_frame {n : ℕ}
    (targetIdx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : (work₀ targetIdx).HasBinaryPrefix bits)
    (htargetStart : (work₀ targetIdx).cells 0 = Γ.start)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ targetIdx →
      (work₀ i).read ≠ Γ.start ∧ 1 ≤ (work₀ i).head)
    (houtput : out₀.read ≠ Γ.start) (houtputHead : 1 ≤ out₀.head) :
    ∃ c' t,
      t ≤ bits.length + 3 ∧
      (TM.rewindWorkTM targetIdx).reachesIn t
        { state := (TM.rewindWorkTM targetIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (TM.rewindWorkTM targetIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work targetIdx).HasBinaryString bits ∧
      (∀ i, i ≠ targetIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  wordTargetRewind_reachesIn_frame_internal targetIdx bits inp₀ work₀ out₀
    htarget htargetStart hinput hother houtput houtputHead

/-- Exact framed execution of unary-width decoding. The source begins at the
first prefix bit, the width counter begins at canonical zero, and all unrelated
tapes are preserved exactly. -/
theorem wordWidthTM_reachesIn_frame {n : ℕ}
    (sourceIdx widthIdx : Fin n) (hindices : sourceIdx ≠ widthIdx)
    (width : ℕ) (payload : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: payload))
    (hwidth : (work₀ widthIdx).HasBinaryNat 0)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ widthIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordWidthTM sourceIdx widthIdx).reachesIn (wordWidthTime width)
        { state := (wordWidthTM sourceIdx widthIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordWidthTM sourceIdx widthIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix (false :: payload) ∧
      (c'.work widthIdx).HasBinaryNat width ∧
      (∀ i, i ≠ sourceIdx → i ≠ widthIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  wordWidthTM_reachesIn_frame_internal sourceIdx widthIdx hindices width
    payload inp₀ work₀ out₀ hsource hwidth hinput hother houtput

/-- Unary-width decoding is safe for one-way-output composition. -/
theorem wordWidthTM_isTransducer {n : ℕ} (sourceIdx widthIdx : Fin n) :
    (wordWidthTM sourceIdx widthIdx).IsTransducer :=
  wordWidthTM_isTransducer_internal sourceIdx widthIdx

/-- Exact one-step framed execution of the payload-copy leaf. It consumes one
source bit, appends it to the target, and preserves every unrelated tape. -/
theorem payloadBitTM_reachesIn_frame {n : ℕ}
    (sourceIdx targetIdx : Fin n) (hindices : sourceIdx ≠ targetIdx)
    (bit : Bool) (suffix pre : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (bit :: suffix))
    (htarget : (work₀ targetIdx).HasBinaryPrefix pre)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (payloadBitTM sourceIdx targetIdx).reachesIn 1
        { state := (payloadBitTM sourceIdx targetIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (payloadBitTM sourceIdx targetIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix suffix ∧
      (c'.work targetIdx).HasBinaryPrefix (pre ++ [bit]) ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  payloadBitTM_reachesIn_frame_internal sourceIdx targetIdx hindices bit
    suffix pre inp₀ work₀ out₀ hsource htarget hinput hother houtput

/-- The one-bit payload copier never moves the output head left. -/
theorem payloadBitTM_isTransducer {n : ℕ} (sourceIdx targetIdx : Fin n) :
    (payloadBitTM sourceIdx targetIdx).IsTransducer :=
  payloadBitTM_isTransducer_internal sourceIdx targetIdx

/-- The separator phase consumes one zero and otherwise preserves the frame. -/
theorem wordSeparatorTM_reachesIn_frame {n : ℕ}
    (sourceIdx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (false :: bits))
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordSeparatorTM sourceIdx).reachesIn 1
        { state := (wordSeparatorTM sourceIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordSeparatorTM sourceIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix bits ∧
      (∀ i, i ≠ sourceIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  wordSeparatorTM_reachesIn_frame_internal sourceIdx bits inp₀ work₀ out₀
    hsource hinput hother houtput

/-- Exact framed execution of the bounded payload loop. The source begins on
the first payload bit, the target is an empty appendable prefix, the counter is
zero, and the preserved width tape equals the payload length. The machine
copies the complete payload and leaves the source at the next encoded word. -/
theorem wordPayloadTM_reachesIn_frame {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload rest : List Bool) (width : ℕ) (hwidthLength : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (payload ++ rest))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hwidth : (work₀ widthIdx).HasBinaryNat width)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).reachesIn
        (wordPayloadTime width)
        { state := (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix rest ∧
      (c'.work targetIdx).HasBinaryPrefix payload ∧
      (c'.work counterIdx).HasBinaryNat width ∧
      (c'.work widthIdx).HasBinaryNat width ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
        i ≠ widthIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  wordPayloadTM_reachesIn_frame_internal sourceIdx targetIdx counterIdx widthIdx
    hdistinct payload rest width hwidthLength inp₀ work₀ out₀ hsource htarget
      hcounter hwidth hinput hother houtput

/-- The bounded payload loop preserves one-way-output safety. -/
theorem wordPayloadTM_isTransducer {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n) :
    (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).IsTransducer :=
  wordPayloadTM_isTransducer_internal sourceIdx targetIdx counterIdx widthIdx

/-- Exact end-to-end decoding of one self-delimiting width/payload layout.
The source is left at the next word and the target contains the complete
payload as an appendable binary prefix. -/
theorem wordDecodeTM_reachesIn_frame {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload rest : List Bool) (width : ℕ) (hwidthLength : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: (payload ++ rest)))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hwidth : (work₀ widthIdx).HasBinaryNat 0)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).reachesIn
        (wordDecodeTime width)
        { state := (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix rest ∧
      (c'.work targetIdx).HasBinaryPrefix payload ∧
      (c'.work counterIdx).HasBinaryNat width ∧
      (c'.work widthIdx).HasBinaryNat width ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
        i ≠ widthIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  wordDecodeTM_reachesIn_frame_internal sourceIdx targetIdx counterIdx widthIdx
    hdistinct payload rest width hwidthLength inp₀ work₀ out₀ hsource htarget
      hcounter hwidth hinput hother houtput

/-- Coarse all-prefix space envelope for complete word decoding. Starting from
auxiliary-space budget `initialSpace`, no prefix of the exact decoder run can
use more than `initialSpace + wordDecodeTime width`; this follows from the
one-cell-per-transition head-growth bound and is independent of endpoint
correctness. -/
theorem wordDecodeTM_prefix_withinAuxSpace {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (width inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n
      (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).reachesIn
      time start current)
    (htime : time ≤ wordDecodeTime width) :
    current.WithinAuxSpace inputLength (initialSpace + wordDecodeTime width) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- A canonical `WordCode.encode` prefix decodes to the natural's canonical
little-endian bit string and leaves the following encoded stream untouched. -/
theorem wordDecodeTM_reachesIn_frame_encode {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (value : ℕ) (rest : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (WordCode.encode value ++ rest))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hwidth : (work₀ widthIdx).HasBinaryNat 0)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).reachesIn
        (wordDecodeTime (bitlen value))
        { state := (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix rest ∧
      (c'.work targetIdx).HasBinaryPrefix value.bits ∧
      (c'.work counterIdx).HasBinaryNat (bitlen value) ∧
      (c'.work widthIdx).HasBinaryNat (bitlen value) ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
        i ≠ widthIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  have hsource' : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate (bitlen value) true ++
        false :: (Nat.toBitsLE (bitlen value) value ++ rest)) := by
    simpa [WordCode.encode, List.append_assoc] using hsource
  obtain ⟨c', hreach, hhalt, hinput', hsource'', htarget', hcounter',
      hwidth', hframe, houtput'⟩ :=
    wordDecodeTM_reachesIn_frame sourceIdx targetIdx counterIdx widthIdx
      hdistinct (Nat.toBitsLE (bitlen value) value) rest (bitlen value)
        (by simp) inp₀ work₀ out₀ hsource' htarget hcounter hwidth hinput hother houtput
  refine ⟨c', hreach, hhalt, hinput', hsource'', ?_, hcounter', hwidth',
    hframe, houtput'⟩
  simpa [bitlen, Nat.toBitsLE_size] using htarget'

/-- The existing checked decoder is quasi-linear in the decoded word width.
This tightens the former quadratic charging by retaining the bit-width of the
binary loop limit instead of replacing it by the limit's numeric value. -/
theorem wordDecodeTime_le_size (width : ℕ) :
    wordDecodeTime width ≤
      8 * (width + 1) * (width.size + 2) :=
  wordDecodeTime_le_size_internal width

/-- Complete word decoding preserves one-way-output safety. -/
theorem wordDecodeTM_isTransducer {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n) :
    (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).IsTransducer :=
  wordDecodeTM_isTransducer_internal sourceIdx targetIdx counterIdx widthIdx

/-! ## Linear unary-marker decoder -/

/-- Exact framed execution of the optimized decoder. It uses one unary marker
instead of a binary width/counter pair and takes exactly `3 * width + 3`
transitions. -/
theorem wordDecodeLinearTM_reachesIn_frame {n : ℕ}
    (sourceIdx targetIdx markerIdx : Fin n)
    (hdistinct : LinearWordDistinct sourceIdx targetIdx markerIdx)
    (payload rest : List Bool) (width : ℕ) (hwidth : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: (payload ++ rest)))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hmarker : (work₀ markerIdx).HasBinaryPrefix [])
    (hmarkerStart : (work₀ markerIdx).cells 0 = Γ.start)
    (hinput : inp₀.read ≠ Γ.start)
    (hreads : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).reachesIn
        (wordDecodeLinearTime width)
        { state := (wordDecodeLinearTM sourceIdx targetIdx markerIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix rest ∧
      (c'.work targetIdx).HasBinaryPrefix payload ∧
      (c'.work markerIdx).HasBinaryPrefix (List.replicate width true) ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ markerIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  wordDecodeLinearTM_reachesIn_frame_internal sourceIdx targetIdx markerIdx
    hdistinct payload rest width hwidth inp₀ work₀ out₀ hsource htarget
      hmarker hmarkerStart hinput hreads houtput

/-- The optimized decoder handles a canonical natural-number word in time
linear in the encoded word width. -/
theorem wordDecodeLinearTM_reachesIn_frame_encode {n : ℕ}
    (sourceIdx targetIdx markerIdx : Fin n)
    (hdistinct : LinearWordDistinct sourceIdx targetIdx markerIdx)
    (value : ℕ) (rest : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (WordCode.encode value ++ rest))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hmarker : (work₀ markerIdx).HasBinaryPrefix [])
    (hmarkerStart : (work₀ markerIdx).cells 0 = Γ.start)
    (hinput : inp₀.read ≠ Γ.start)
    (hreads : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).reachesIn
        (wordDecodeLinearTime (bitlen value))
        { state := (wordDecodeLinearTM sourceIdx targetIdx markerIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix rest ∧
      (c'.work targetIdx).HasBinaryPrefix value.bits ∧
      (c'.work markerIdx).HasBinaryPrefix
        (List.replicate (bitlen value) true) ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ markerIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  have hsource' : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate (bitlen value) true ++
        false :: (Nat.toBitsLE (bitlen value) value ++ rest)) := by
    simpa [WordCode.encode, List.append_assoc] using hsource
  obtain ⟨c', hreach, hhalt, hinput', hsource'', htarget', hmarker',
      hframe, houtput'⟩ :=
    wordDecodeLinearTM_reachesIn_frame sourceIdx targetIdx markerIdx hdistinct
      (Nat.toBitsLE (bitlen value) value) rest (bitlen value) (by simp)
      inp₀ work₀ out₀ hsource' htarget hmarker hmarkerStart hinput hreads houtput
  refine ⟨c', hreach, hhalt, hinput', hsource'', ?_, hmarker', hframe, houtput'⟩
  simpa [bitlen, Nat.toBitsLE_size] using htarget'

/-- The optimized decoder never moves the output head left. -/
theorem wordDecodeLinearTM_isTransducer {n : ℕ}
    (sourceIdx targetIdx markerIdx : Fin n) :
    (wordDecodeLinearTM sourceIdx targetIdx markerIdx).IsTransducer :=
  wordDecodeLinearTM_isTransducer_internal sourceIdx targetIdx markerIdx

end Machine

end RegisterStore

end RAM

end Complexity
