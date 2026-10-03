/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal.Pure
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal.Rewind
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal.Scan
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Linear-time canonical binary addition -- composed semantics

This file composes the one-pass full-adder scan with the three checked rewind
contracts. The resulting machine restores both operands, returns a canonical
sum, preserves the complete external tape frame, and carries explicit time and
all-prefix auxiliary-space bounds.
-/


@[expose] public section

namespace Complexity

namespace TM

private def binaryRippleAddScanPost {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work lhsIdx).HasBinaryContent lhs.bits ∧
    (work lhsIdx).cells 0 = Γ.start ∧
    (work lhsIdx).head = lhs.size + 1 ∧
    (work rhsIdx).HasBinaryContent rhs.bits ∧
    (work rhsIdx).cells 0 = Γ.start ∧
    (work rhsIdx).head = rhs.size + 1 ∧
    (work resultIdx).HasBinaryContent (lhs + rhs).bits ∧
    (work resultIdx).cells 0 = Γ.start ∧
    (work resultIdx).head = (lhs + rhs).size + 1 ∧
    (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      work i = work₀ i) ∧
    out = out₀

/-- Postcondition for completed binary ripple addition. -/
def binaryRippleAddPost {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work lhsIdx).HasBinaryNat lhs ∧
    (work rhsIdx).HasBinaryNat rhs ∧
    (work resultIdx).HasBinaryNat (lhs + rhs) ∧
    (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      work i = work₀ i) ∧
    out = out₀

private theorem binaryRippleAddScanTM_hoareTime_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryRippleAddScanPost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀)
      (binaryRippleAddScanTime lhs.bits rhs.bits) := by
  rintro inp work out ⟨hinputEq, hworkEq, houtputEq⟩
  subst inp
  subst work
  subst out
  have hresultPrefix : (work₀ resultIdx).HasBinaryPrefix [] := by
    simpa [Tape.HasBinaryString, Tape.HasBinaryPrefix] using hresult.2
  obtain ⟨c', hreach, hhalt, hfinalInput, hfinalLhs, hfinalLhsHead,
      hfinalRhs, hfinalRhsHead, hfinalResult, hfinalResultStart,
      hfinalOther, hfinalOutput⟩ :=
    binaryRippleAddScanTM_reachesIn_frame_internal lhsIdx rhsIdx resultIdx
      hdistinct lhs.bits rhs.bits inp₀ work₀ out₀ hlhs.2 hrhs.2
      hresultPrefix hresult.1 hinput hother houtput
  refine ⟨c', binaryRippleAddScanTime lhs.bits rhs.bits, le_rfl,
    hreach, hhalt, ?_⟩
  refine ⟨hfinalInput, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfinalResultStart,
    ?_, hfinalOther, hfinalOutput⟩
  · simpa only [Tape.HasBinaryContent, hfinalLhs] using
      hlhs.2.hasBinaryContent
  · rw [hfinalLhs]
    exact hlhs.1
  · simpa [Nat.size_eq_bits_len] using hfinalLhsHead
  · simpa only [Tape.HasBinaryContent, hfinalRhs] using
      hrhs.2.hasBinaryContent
  · rw [hfinalRhs]
    exact hrhs.1
  · simpa [Nat.size_eq_bits_len] using hfinalRhsHead
  · simpa [BinaryRippleAdd.ripple_natBits_internal] using! hfinalResult.2
  · simpa [BinaryRippleAdd.ripple_natBits_internal,
      Nat.size_eq_bits_len] using hfinalResult.1

private theorem binaryRippleAddRewindTail_hoareTime_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (seqTM (rewindWorkTM lhsIdx)
      (seqTM (rewindWorkTM rhsIdx) (rewindWorkTM resultIdx))).HoareTime
      (binaryRippleAddScanPost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀)
      (binaryRippleAddPost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀)
      ((lhs.size + 1) + (rhs.size + 1) + ((lhs + rhs).size + 1) + 8) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hlhs, hlhsStart, hlhsHead, hrhs, hrhsStart,
    hrhsHead, hresult, hresultStart, hresultHead, hframe, hout⟩
  have hrewind := binaryRippleAddRewindTM_hoareTime_frame_internal
    lhsIdx rhsIdx resultIdx hdistinct lhs.bits rhs.bits (lhs + rhs).bits
    (lhs.size + 1) (rhs.size + 1) ((lhs + rhs).size + 1)
    inp work out hlhs hlhsStart
    ⟨by rw [hlhsHead]; omega, by rw [hlhsHead]⟩
    hrhs hrhsStart
    ⟨by rw [hrhsHead]; omega, by rw [hrhsHead]⟩
    hresult hresultStart
    ⟨by rw [hresultHead]; omega, by rw [hresultHead]⟩
    (hinp.symm ▸ hinput)
    (fun i hil hir hires => by
      rw [hframe i hil hir hires]
      exact hother i hil hir hires)
    (hout.symm ▸ houtput)
  obtain ⟨c', time, htime, hreach, hhalt, hfinalInput, hfinalLhs,
      hfinalRhs, hfinalResult, hfinalOther, hfinalOutput⟩ :=
    hrewind inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', time, htime, hreach, hhalt, ?_⟩
  refine ⟨hfinalInput.trans hinp, ?_, ?_, ?_, ?_, hfinalOutput.trans hout⟩
  · rw [hfinalLhs]
    exact Tape.init_move_right_hasBinaryNat lhs
  · rw [hfinalRhs]
    exact Tape.init_move_right_hasBinaryNat rhs
  · rw [hfinalResult]
    exact Tape.init_move_right_hasBinaryNat (lhs + rhs)
  · intro i hil hir hires
    exact (hfinalOther i hil hir hires).trans (hframe i hil hir hires)

theorem binaryRippleAddTM_hoareTime_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryRippleAddTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryRippleAddPost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀)
      (binaryRippleAddTime lhs rhs) := by
  have hscan := binaryRippleAddScanTM_hoareTime_frame_internal
    lhsIdx rhsIdx resultIdx hdistinct lhs rhs inp₀ work₀ out₀ hlhs hrhs
    hresult hinput.read_ne_start
    (fun i hil hir hires => (hother i hil hir hires).read_ne_start)
    houtput.read_ne_start
  have htail := binaryRippleAddRewindTail_hoareTime_internal
    lhsIdx rhsIdx resultIdx hdistinct lhs rhs inp₀ work₀ out₀
    hinput hother houtput
  have htransition : ∀ inp work out,
      binaryRippleAddScanPost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀
        inp work out →
      binaryRippleAddScanPost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀
        (transitionInput inp) (fun i => transitionTape (work i))
          (transitionTape out) := by
    intro inp work out hpost
    rcases hpost with ⟨hinp, hlhsContent, hlhsStart, hlhsHead,
      hrhsContent, hrhsStart, hrhsHead, hresultContent, hresultStart,
      hresultHead, hframe, hout⟩
    have hworkRead : ∀ i, (work i).read ≠ Γ.start := by
      intro i
      by_cases hil : i = lhsIdx
      · subst i
        exact hlhsContent.cells_ne_start _ (by rw [hlhsHead]; omega)
      by_cases hir : i = rhsIdx
      · subst i
        exact hrhsContent.cells_ne_start _ (by rw [hrhsHead]; omega)
      by_cases hires : i = resultIdx
      · subst i
        exact hresultContent.cells_ne_start _ (by rw [hresultHead]; omega)
      · rw [hframe i hil hir hires]
        exact (hother i hil hir hires).read_ne_start
    obtain ⟨hinputTransition, hworkTransition, houtputTransition⟩ :=
      phaseTransition_eq_self_of_reads_ne_start
        (hinp.symm ▸ hinput.read_ne_start) hworkRead
        (hout.symm ▸ houtput.read_ne_start)
    rw [hinputTransition, hworkTransition, houtputTransition]
    exact ⟨hinp, hlhsContent, hlhsStart, hlhsHead, hrhsContent, hrhsStart,
      hrhsHead, hresultContent, hresultStart, hresultHead, hframe, hout⟩
  have hrun := seqTM_hoareTime
    (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx)
    (seqTM (rewindWorkTM lhsIdx)
      (seqTM (rewindWorkTM rhsIdx) (rewindWorkTM resultIdx)))
    hscan htransition htail
  unfold binaryRippleAddTM
  apply hrun.mono_bound
  rw [binaryRippleAddScanTime_natBits_internal]
  simp only [binaryRippleAddTime]
  omega

theorem binaryRippleAddTM_hoareTimeSpace_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀)
    (hinitial :
      ({ state := (binaryRippleAddTM lhsIdx rhsIdx resultIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binaryRippleAddTM lhsIdx rhsIdx resultIdx).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryRippleAddTM lhsIdx rhsIdx resultIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryRippleAddPost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀)
      (binaryRippleAddTime lhs rhs) inputLength
      (initialSpace + binaryRippleAddTime lhs rhs) := by
  apply (binaryRippleAddTM_hoareTime_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother
    houtput).toHoareTimeSpace
  rintro inp work out ⟨hinputEq, hworkEq, houtputEq⟩
  subst inp
  subst work
  subst out
  exact hinitial

end TM

end Complexity
