/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordEncode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordEncode.Internal

/-!
# Self-delimiting word emission
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- One generic work-tape pass appends either the unary width header or the
payload bits while preserving input and every unrelated work tape exactly. -/
theorem workEmitTM_hoareTime_frame {n : ℕ}
    (idx : Fin n) (mode : WorkEmitMode) (bits emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ idx).HasBinarySuffix bits)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ idx → TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (workEmitTM idx mode).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work idx).HasBinarySuffix [] ∧
        (work idx).cells = (work₀ idx).cells ∧
        (work idx).head = (work₀ idx).head + bits.length ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        out.HasBinaryPrefix (emitted ++ workEmitBits mode bits))
      (workEmitTime bits) :=
  workEmitTM_hoareTime_frame_internal idx mode bits emitted inp₀ work₀
    out₀ hsource hinput hother houtput

/-- Emit `WordCode.encode value` from a canonical natural-number work tape,
preserving the input, source cells, and every unrelated work tape exactly. -/
theorem wordEncodeTM_hoareTime_frame {n : ℕ}
    (idx : Fin n) (value : ℕ) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ idx → TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (wordEncodeTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work idx).HasBinarySuffix [] ∧
        (work idx).cells = (work₀ idx).cells ∧
        (work idx).head = value.bits.length + 1 ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        out.HasBinaryPrefix (emitted ++ WordCode.encode value))
      (wordEncodeTime value) :=
  wordEncodeTM_hoareTime_frame_internal idx value emitted inp₀ work₀ out₀
    hvalue hinput hother houtput

/-- Rewind any bounded cursor over canonical binary contents and emit the
complete self-delimiting word, retaining a literal external frame. -/
theorem rewindWordEncodeTM_hoareTime_frame {n : ℕ}
    (idx : Fin n) (value headBound : ℕ) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcontent : (work₀ idx).HasBinaryContent value.bits)
    (hstart : (work₀ idx).cells 0 = Γ.start)
    (hhead : 1 ≤ (work₀ idx).head ∧ (work₀ idx).head ≤ headBound)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ idx → TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (rewindWordEncodeTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work idx).HasBinarySuffix [] ∧
        (work idx).cells = (work₀ idx).cells ∧
        (work idx).head = value.bits.length + 1 ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        out.HasBinaryPrefix (emitted ++ WordCode.encode value))
      (rewindWordEncodeTime value headBound) :=
  rewindWordEncodeTM_hoareTime_frame_internal idx value headBound emitted
    inp₀ work₀ out₀ hcontent hstart hhead hinput hother houtput

/-- Each emission pass is append-only on the output tape. -/
theorem workEmitTM_isTransducer {n : ℕ}
    (idx : Fin n) (mode : WorkEmitMode) :
    (workEmitTM idx mode).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | scan =>
      cases hread : wHeads idx <;>
        simp [workEmitTM, hread, TM.allReadBack, TM.idleDir] <;>
        split <;> cases oHead <;> simp
  | done =>
      cases oHead <;> simp [workEmitTM, TM.allIdle, TM.idleDir]

/-- Complete word emission is append-only on the output tape. -/
theorem wordEncodeTM_isTransducer {n : ℕ} (idx : Fin n) :
    (wordEncodeTM idx).IsTransducer :=
  (workEmitTM_isTransducer idx .width).seqTM
    ((TM.rewindWorkTM_isTransducer idx).seqTM
      (workEmitTM_isTransducer idx .payload))

/-- Rewind-and-emit word encoding is append-only on the output tape. -/
theorem rewindWordEncodeTM_isTransducer {n : ℕ} (idx : Fin n) :
    (rewindWordEncodeTM idx).IsTransducer :=
  (TM.rewindWorkTM_isTransducer idx).seqTM
    (wordEncodeTM_isTransducer idx)

/-- Coarse all-prefix auxiliary-space envelope for one emission pass. -/
theorem workEmitTM_prefix_withinAuxSpace {n : ℕ}
    (idx : Fin n) (mode : WorkEmitMode) (bits : List Bool)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (workEmitTM idx mode).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (workEmitTM idx mode).reachesIn time start current)
    (htime : time ≤ workEmitTime bits) :
    current.WithinAuxSpace inputLength
      (initialSpace + workEmitTime bits) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Coarse all-prefix auxiliary-space envelope for complete word emission. -/
theorem wordEncodeTM_prefix_withinAuxSpace {n : ℕ}
    (idx : Fin n) (value inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (wordEncodeTM idx).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (wordEncodeTM idx).reachesIn time start current)
    (htime : time ≤ wordEncodeTime value) :
    current.WithinAuxSpace inputLength
      (initialSpace + wordEncodeTime value) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Coarse all-prefix envelope for rewind followed by word emission. -/
theorem rewindWordEncodeTM_prefix_withinAuxSpace {n : ℕ}
    (idx : Fin n) (value headBound inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (rewindWordEncodeTM idx).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (rewindWordEncodeTM idx).reachesIn time start current)
    (htime : time ≤ rewindWordEncodeTime value headBound) :
    current.WithinAuxSpace inputLength
      (initialSpace + rewindWordEncodeTime value headBound) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
