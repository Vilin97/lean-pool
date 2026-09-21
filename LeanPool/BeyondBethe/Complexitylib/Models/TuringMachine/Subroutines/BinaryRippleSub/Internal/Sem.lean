/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Internal.Backward
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Internal.Rewind
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Internal.Scan
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Linear-time canonical binary subtraction -- composed semantics

This file composes the exact forward borrow scan with its backward
canonicalization pass, then restores both preserved operands through the
checked rewind tail. The complete machine computes natural-number monus,
preserves the external tape frame literally, and carries explicit time and
all-prefix auxiliary-space bounds.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Postcondition at the end of the core binary ripple-subtraction phase. -/
def binaryRippleSubCorePost {n : ℕ}
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
    (work resultIdx).HasBinaryNat (lhs - rhs) ∧
    (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      work i = work₀ i) ∧
    out = out₀

/-- Postcondition for completed binary ripple subtraction. -/
def binaryRippleSubPost {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work lhsIdx).HasBinaryNat lhs ∧
    (work rhsIdx).HasBinaryNat rhs ∧
    (work resultIdx).HasBinaryNat (lhs - rhs) ∧
    (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      work i = work₀ i) ∧
    out = out₀

/-- The direct core executes its forward and backward passes in exactly twice
the larger operand width plus the two turn/bounce transitions. -/
theorem binaryRippleSubCoreTM_reachesIn_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).reachesIn
        (binaryRippleSubCoreTime lhs.bits rhs.bits)
        { state := (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).halted c' ∧
      binaryRippleSubCorePost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀
        c'.input c'.work c'.output := by
  let raw := BinaryRippleSub.scan false lhs.bits rhs.bits
  have hresultPrefix : (work₀ resultIdx).HasBinaryPrefix [] := by
    simpa [Tape.HasBinaryString, Tape.HasBinaryPrefix] using hresult.2
  obtain ⟨c₁, hscanReach, hscanState, hscanInput, hscanLhsCells,
      hscanLhsHead, hscanRhsCells, hscanRhsHead, hscanResult,
      hscanResultHead, hscanResultStart, hscanOther, hscanOutput⟩ :=
    binaryRippleSubCoreTM_scan_reachesIn_frame_internal
      lhsIdx rhsIdx resultIdx hdistinct lhs.bits rhs.bits inp₀ work₀ out₀
      hlhs.2 hrhs.2 hresultPrefix hresult.1 hinput hother houtput
  have hscanLhsContent : (c₁.work lhsIdx).HasBinaryContent lhs.bits := by
    simpa only [Tape.HasBinaryContent, hscanLhsCells] using
      hlhs.2.hasBinaryContent
  have hscanRhsContent : (c₁.work rhsIdx).HasBinaryContent rhs.bits := by
    simpa only [Tape.HasBinaryContent, hscanRhsCells] using
      hrhs.2.hasBinaryContent
  have hcleanupOther : ∀ i, i ≠ resultIdx →
      (c₁.work i).read ≠ Γ.start := by
    intro i hires
    by_cases hil : i = lhsIdx
    · subst i
      exact hscanLhsContent.cells_ne_start _ (by rw [hscanLhsHead]; omega)
    by_cases hir : i = rhsIdx
    · subst i
      exact hscanRhsContent.cells_ne_start _ (by rw [hscanRhsHead]; omega)
    · rw [hscanOther i hil hir hires]
      exact hother i hil hir hires
  obtain ⟨c₂, hcleanupReach, hcleanupHalt, hcleanupInput,
      hcleanupOtherEq, hcleanupResult, hcleanupResultStart, hcleanupOutput⟩ :=
    binaryRippleSubCoreTM_cleanup_run_internal lhsIdx rhsIdx resultIdx raw.bits
      raw.borrow c₁.input c₁.work c₁.output
      (hscanInput.symm ▸ hinput) hcleanupOther
      (hscanOutput.symm ▸ houtput) hscanResult hscanResultStart hscanResultHead
  have hcleanupStart :
      ({ state := if raw.borrow then .erase else .trim false
         input := c₁.input
         work := c₁.work
         output := c₁.output } :
        Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q) = c₁ := by
    exact Cfg.ext hscanState.symm rfl rfl rfl
  rw [hcleanupStart] at hcleanupReach
  have hrun := (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).reachesIn_trans
    hscanReach hcleanupReach
  have htime : binaryRippleSubScanTime lhs.bits rhs.bits +
      (raw.bits.length + 1) = binaryRippleSubCoreTime lhs.bits rhs.bits := by
    have hrawLength : raw.bits.length = max lhs.bits.length rhs.bits.length := by
      simpa [raw] using BinaryRippleSub.scan_bits_length_internal
        false lhs.bits rhs.bits
    rw [hrawLength]
    simp only [binaryRippleSubScanTime, binaryRippleSubCoreTime]
    omega
  have hfinalLhs : c₂.work lhsIdx = c₁.work lhsIdx :=
    hcleanupOtherEq lhsIdx hdistinct.lhs_result
  have hfinalRhs : c₂.work rhsIdx = c₁.work rhsIdx :=
    hcleanupOtherEq rhsIdx hdistinct.rhs_result
  have hfinalResult : (c₂.work resultIdx).HasBinaryNat (lhs - rhs) := by
    refine ⟨hcleanupResultStart, ?_⟩
    have hresultBits :
        (if raw.borrow then [] else BinaryRippleSub.trimHighZeros raw.bits) =
          (lhs - rhs).bits := by
      simpa only [BinaryRippleSub.subtract, raw] using
        BinaryRippleSub.subtract_natBits_internal lhs rhs
    rw [← hresultBits]
    exact hcleanupResult
  refine ⟨c₂, ?_, hcleanupHalt, ?_⟩
  · simpa [htime] using hrun
  · refine ⟨hcleanupInput.trans hscanInput, ?_, ?_, ?_, ?_, ?_, ?_,
      hfinalResult, ?_, hcleanupOutput.trans hscanOutput⟩
    · rw [hfinalLhs]
      exact hscanLhsContent
    · rw [hfinalLhs, hscanLhsCells]
      exact hlhs.1
    · rw [hfinalLhs, hscanLhsHead, Nat.size_eq_bits_len]
    · rw [hfinalRhs]
      exact hscanRhsContent
    · rw [hfinalRhs, hscanRhsCells]
      exact hrhs.1
    · rw [hfinalRhs, hscanRhsHead, Nat.size_eq_bits_len]
    · intro i hil hir hires
      exact (hcleanupOtherEq i hires).trans (hscanOther i hil hir hires)

/-- Hoare-time form of the exact direct-core execution. -/
theorem binaryRippleSubCoreTM_hoareTime_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryRippleSubCorePost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀)
      (binaryRippleSubCoreTime lhs.bits rhs.bits) := by
  rintro inp work out ⟨hinputEq, hworkEq, houtputEq⟩
  subst inp
  subst work
  subst out
  obtain ⟨c', hreach, hhalt, hpost⟩ :=
    binaryRippleSubCoreTM_reachesIn_frame_internal lhsIdx rhsIdx resultIdx
      hdistinct lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother
      houtput
  exact ⟨c', binaryRippleSubCoreTime lhs.bits rhs.bits, le_rfl,
    hreach, hhalt, hpost⟩

private theorem binaryRippleSubRewindTail_hoareTime_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (seqTM (rewindWorkTM lhsIdx) (rewindWorkTM rhsIdx)).HoareTime
      (binaryRippleSubCorePost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀)
      (binaryRippleSubPost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀)
      ((lhs.size + 1) + (rhs.size + 1) + 5) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hlhs, hlhsStart, hlhsHead, hrhs, hrhsStart,
    hrhsHead, hresult, hframe, hout⟩
  have hresultParked : Parked (work resultIdx) :=
    ⟨by rw [hresult.2.1], hresult.2.hasBinaryContent.cells_ne_start⟩
  have hrewind := binaryRippleSubRewindTM_hoareTime_frame_internal
    lhsIdx rhsIdx resultIdx hdistinct lhs.bits rhs.bits
    (lhs.size + 1) (rhs.size + 1) inp work out hlhs hlhsStart
    ⟨by rw [hlhsHead]; omega, by rw [hlhsHead]⟩
    hrhs hrhsStart ⟨by rw [hrhsHead]; omega, by rw [hrhsHead]⟩
    hresultParked (hinp.symm ▸ hinput)
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
    exact hresult
  · intro i hil hir hires
    exact (hfinalOther i hil hir hires).trans (hframe i hil hir hires)

/-- The complete direct subtraction machine restores both operands and returns
canonical natural-number monus within the advertised width-linear bound. -/
theorem binaryRippleSubTM_hoareTime_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryRippleSubTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryRippleSubPost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀)
      (binaryRippleSubTime lhs rhs) := by
  have hcore := binaryRippleSubCoreTM_hoareTime_frame_internal
    lhsIdx rhsIdx resultIdx hdistinct lhs rhs inp₀ work₀ out₀ hlhs hrhs
    hresult hinput.read_ne_start
    (fun i hil hir hires => (hother i hil hir hires).read_ne_start)
    houtput.read_ne_start
  have htail := binaryRippleSubRewindTail_hoareTime_internal
    lhsIdx rhsIdx resultIdx hdistinct lhs rhs inp₀ work₀ out₀
    hinput hother houtput
  have htransition : ∀ inp work out,
      binaryRippleSubCorePost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀
        inp work out →
      binaryRippleSubCorePost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀
        (transitionInput inp) (fun i => transitionTape (work i))
          (transitionTape out) := by
    intro inp work out hpost
    rcases hpost with ⟨hinp, hlhsContent, hlhsStart, hlhsHead,
      hrhsContent, hrhsStart, hrhsHead, hresultNat, hframe, hout⟩
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
        exact hresultNat.2.hasBinaryContent.cells_ne_start _ (by
          rw [hresultNat.2.1])
      · rw [hframe i hil hir hires]
        exact (hother i hil hir hires).read_ne_start
    obtain ⟨hinputTransition, hworkTransition, houtputTransition⟩ :=
      phaseTransition_eq_self_of_reads_ne_start
        (hinp.symm ▸ hinput.read_ne_start) hworkRead
        (hout.symm ▸ houtput.read_ne_start)
    rw [hinputTransition, hworkTransition, houtputTransition]
    exact ⟨hinp, hlhsContent, hlhsStart, hlhsHead, hrhsContent, hrhsStart,
      hrhsHead, hresultNat, hframe, hout⟩
  have hrun := seqTM_hoareTime
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx)
    (seqTM (rewindWorkTM lhsIdx) (rewindWorkTM rhsIdx))
    hcore htransition htail
  unfold binaryRippleSubTM
  apply hrun.mono_bound
  rw [binaryRippleSubCoreTime_natBits_internal]
  simp only [binaryRippleSubTime]
  omega

/-- Time-and-space contract for complete direct subtraction. The generic
all-prefix envelope charges at most one additional cell per possible step. -/
theorem binaryRippleSubTM_hoareTimeSpace_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
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
      ({ state := (binaryRippleSubTM lhsIdx rhsIdx resultIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binaryRippleSubTM lhsIdx rhsIdx resultIdx).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryRippleSubTM lhsIdx rhsIdx resultIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryRippleSubPost lhsIdx rhsIdx resultIdx lhs rhs inp₀ work₀ out₀)
      (binaryRippleSubTime lhs rhs) inputLength
      (initialSpace + binaryRippleSubTime lhs rhs) := by
  apply (binaryRippleSubTM_hoareTime_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother
    houtput).toHoareTimeSpace
  rintro inp work out ⟨rfl, rfl, rfl⟩
  exact hinitial

end TM

end Complexity
