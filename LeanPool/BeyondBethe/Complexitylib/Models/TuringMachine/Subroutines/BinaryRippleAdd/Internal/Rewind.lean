/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinary.Internal

/-!
# Linear-time canonical binary addition -- rewind proof internals

This module packages the three-rewind tail of `binaryRippleAddTM` into one
framed Hoare-time contract.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Canonical parked tape containing the supplied little-endian binary digits. -/
def binaryRippleAddCanonicalTape (bits : List Bool) : Tape :=
  (Tape.init (bits.map Γ.ofBool)).move Dir3.right

private theorem binaryRippleAddCanonicalTape_parked (bits : List Bool) :
    Parked (binaryRippleAddCanonicalTape bits) := by
  refine ⟨by simp [binaryRippleAddCanonicalTape, Tape.move], ?_⟩
  simpa [binaryRippleAddCanonicalTape] using
    Tape.init_ofBool_move_right_cells_ne_start bits

private theorem binaryRippleAddRewindExact_hoareTime {n : ℕ}
    (idx : Fin n) (bits : List Bool) (headBound : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : (work₀ idx).HasBinaryContent bits)
    (htargetStart : (work₀ idx).cells 0 = Γ.start)
    (htargetHead : 1 ≤ (work₀ idx).head ∧ (work₀ idx).head ≤ headBound)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (houtput : Parked out₀) :
    (rewindWorkTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx (binaryRippleAddCanonicalTape bits) ∧
        out = out₀)
      (headBound + 2) := by
  have hrewind := rewindBinaryWorkTM_hoareTime_frame_internal idx bits
    headBound inp₀ work₀ out₀ htarget htargetStart htargetHead hinput
    hother houtput
  apply hrewind.consequence (b' := headBound + 2)
  · intro _inp _work _out hpre
    exact hpre
  · rintro inp work out ⟨hinp, htargetEq, hotherEq, hout⟩
    refine ⟨hinp, ?_, hout⟩
    funext i
    by_cases hi : i = idx
    · subst i
      rw [Function.update_self]
      simpa [binaryRippleAddCanonicalTape] using htargetEq
    · rw [Function.update_of_ne hi]
      exact hotherEq i hi
  · exact le_rfl

private theorem binaryRippleAddExactFrame_transition {n : ℕ}
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    ∀ inp work out,
      (inp = inp₀ ∧ work = work₀ ∧ out = out₀) →
      transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = work₀ ∧
        transitionTape out = out₀ := by
  rintro _inp _work _out ⟨rfl, rfl, rfl⟩
  exact ⟨hinput.transitionInput_eq_self,
    funext fun i => (hwork i).transitionTape_eq_self,
    houtput.transitionTape_eq_self⟩

theorem binaryRippleAddRewindTM_hoareTime_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhsBits rhsBits resultBits : List Bool)
    (lhsBound rhsBound resultBound : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryContent lhsBits)
    (hlhsStart : (work₀ lhsIdx).cells 0 = Γ.start)
    (hlhsHead : 1 ≤ (work₀ lhsIdx).head ∧
      (work₀ lhsIdx).head ≤ lhsBound)
    (hrhs : (work₀ rhsIdx).HasBinaryContent rhsBits)
    (hrhsStart : (work₀ rhsIdx).cells 0 = Γ.start)
    (hrhsHead : 1 ≤ (work₀ rhsIdx).head ∧
      (work₀ rhsIdx).head ≤ rhsBound)
    (hresult : (work₀ resultIdx).HasBinaryContent resultBits)
    (hresultStart : (work₀ resultIdx).cells 0 = Γ.start)
    (hresultHead : 1 ≤ (work₀ resultIdx).head ∧
      (work₀ resultIdx).head ≤ resultBound)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (seqTM (rewindWorkTM lhsIdx)
      (seqTM (rewindWorkTM rhsIdx) (rewindWorkTM resultIdx))).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work lhsIdx = binaryRippleAddCanonicalTape lhsBits ∧
        work rhsIdx = binaryRippleAddCanonicalTape rhsBits ∧
        work resultIdx = binaryRippleAddCanonicalTape resultBits ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (lhsBound + rhsBound + resultBound + 8) := by
  have hlhsParked : Parked (work₀ lhsIdx) :=
    ⟨hlhsHead.1, hlhs.cells_ne_start⟩
  have hrhsParked : Parked (work₀ rhsIdx) :=
    ⟨hrhsHead.1, hrhs.cells_ne_start⟩
  have hresultParked : Parked (work₀ resultIdx) :=
    ⟨hresultHead.1, hresult.cells_ne_start⟩
  have hwork₀ : ∀ i, Parked (work₀ i) := by
    intro i
    by_cases hlhsIdx : i = lhsIdx
    · subst i
      exact hlhsParked
    by_cases hrhsIdx : i = rhsIdx
    · subst i
      exact hrhsParked
    by_cases hresultIdx : i = resultIdx
    · subst i
      exact hresultParked
    exact hother i hlhsIdx hrhsIdx hresultIdx

  let lhsTape := binaryRippleAddCanonicalTape lhsBits
  let rhsTape := binaryRippleAddCanonicalTape rhsBits
  let resultTape := binaryRippleAddCanonicalTape resultBits
  let work₁ := Function.update work₀ lhsIdx lhsTape
  let work₂ := Function.update work₁ rhsIdx rhsTape
  let work₃ := Function.update work₂ resultIdx resultTape

  have hwork₁ : ∀ i, Parked (work₁ i) := by
    intro i
    by_cases hi : i = lhsIdx
    · subst i
      simpa [work₁, lhsTape] using
        binaryRippleAddCanonicalTape_parked lhsBits
    · simpa only [work₁, Function.update_of_ne hi] using hwork₀ i
  have hwork₂ : ∀ i, Parked (work₂ i) := by
    intro i
    by_cases hi : i = rhsIdx
    · subst i
      simpa [work₂, rhsTape] using
        binaryRippleAddCanonicalTape_parked rhsBits
    · simpa only [work₂, Function.update_of_ne hi] using hwork₁ i

  have hrhs₁ : (work₁ rhsIdx).HasBinaryContent rhsBits := by
    simpa only [work₁, Function.update_of_ne hdistinct.lhs_rhs.symm] using hrhs
  have hrhsStart₁ : (work₁ rhsIdx).cells 0 = Γ.start := by
    simpa only [work₁, Function.update_of_ne hdistinct.lhs_rhs.symm] using hrhsStart
  have hrhsHead₁ : 1 ≤ (work₁ rhsIdx).head ∧
      (work₁ rhsIdx).head ≤ rhsBound := by
    simpa only [work₁, Function.update_of_ne hdistinct.lhs_rhs.symm] using hrhsHead

  have hresult₂ : (work₂ resultIdx).HasBinaryContent resultBits := by
    simpa only [work₂, Function.update_of_ne hdistinct.rhs_result.symm,
      work₁, Function.update_of_ne hdistinct.lhs_result.symm] using hresult
  have hresultStart₂ : (work₂ resultIdx).cells 0 = Γ.start := by
    simpa only [work₂, Function.update_of_ne hdistinct.rhs_result.symm,
      work₁, Function.update_of_ne hdistinct.lhs_result.symm] using hresultStart
  have hresultHead₂ : 1 ≤ (work₂ resultIdx).head ∧
      (work₂ resultIdx).head ≤ resultBound := by
    simpa only [work₂, Function.update_of_ne hdistinct.rhs_result.symm,
      work₁, Function.update_of_ne hdistinct.lhs_result.symm] using hresultHead

  have hrewindLhs := binaryRippleAddRewindExact_hoareTime lhsIdx lhsBits
    lhsBound inp₀ work₀ out₀ hlhs hlhsStart hlhsHead hinput
    (fun i _ => hwork₀ i) houtput
  have hrewindRhs := binaryRippleAddRewindExact_hoareTime rhsIdx rhsBits
    rhsBound inp₀ work₁ out₀ hrhs₁ hrhsStart₁ hrhsHead₁ hinput
    (fun i _ => hwork₁ i) houtput
  have hrewindResult := binaryRippleAddRewindExact_hoareTime resultIdx
    resultBits resultBound inp₀ work₂ out₀ hresult₂ hresultStart₂
    hresultHead₂ hinput (fun i _ => hwork₂ i) houtput

  have htail := seqTM_hoareTime (rewindWorkTM rhsIdx)
    (rewindWorkTM resultIdx) hrewindRhs
    (binaryRippleAddExactFrame_transition inp₀ work₂ out₀ hinput
      hwork₂ houtput)
    hrewindResult
  have hrun := seqTM_hoareTime (rewindWorkTM lhsIdx)
    (seqTM (rewindWorkTM rhsIdx) (rewindWorkTM resultIdx)) hrewindLhs
    (binaryRippleAddExactFrame_transition inp₀ work₁ out₀ hinput
      hwork₁ houtput)
    htail
  apply hrun.consequence (b' := lhsBound + rhsBound + resultBound + 8)
  · intro _inp _work _out hpre
    exact hpre
  · rintro inp work out ⟨hinp, hworkEq, hout⟩
    refine ⟨hinp, ?_, ?_, ?_, ?_, hout⟩
    · rw [hworkEq]
      simp only [Function.update_of_ne hdistinct.lhs_result,
        work₂, Function.update_of_ne hdistinct.lhs_rhs,
        work₁, Function.update_self, lhsTape]
    · rw [hworkEq]
      simp only [Function.update_of_ne hdistinct.rhs_result,
        work₂, Function.update_self, rhsTape]
    · rw [hworkEq]
      simp only [Function.update_self]
    · intro i hlhsIdx hrhsIdx hresultIdx
      rw [hworkEq]
      simp only [Function.update_of_ne hresultIdx,
        work₂, Function.update_of_ne hrhsIdx,
        work₁, Function.update_of_ne hlhsIdx]
  · omega

end TM

end Complexity
