/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinary.Internal

/-!
# Linear-time canonical binary subtraction -- operand rewind internals

The subtraction core already returns its result to cell one. This module
packages the two remaining operand rewinds into one exact framed contract.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Canonical parked tape containing the supplied little-endian binary digits. -/
def binaryRippleSubCanonicalTape (bits : List Bool) : Tape :=
  (Tape.init (bits.map Γ.ofBool)).move Dir3.right

private theorem binaryRippleSubCanonicalTape_parked (bits : List Bool) :
    Parked (binaryRippleSubCanonicalTape bits) := by
  refine ⟨by simp [binaryRippleSubCanonicalTape, Tape.move], ?_⟩
  simpa [binaryRippleSubCanonicalTape] using
    Tape.init_ofBool_move_right_cells_ne_start bits

private theorem binaryRippleSubRewindExact_hoareTime {n : ℕ}
    (idx : Fin n) (bits : List Bool) (headBound : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : (work₀ idx).HasBinaryContent bits)
    (htargetStart : (work₀ idx).cells 0 = Γ.start)
    (htargetHead : 1 ≤ (work₀ idx).head ∧
      (work₀ idx).head ≤ headBound)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (houtput : Parked out₀) :
    (rewindWorkTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx
          (binaryRippleSubCanonicalTape bits) ∧
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
      simpa [binaryRippleSubCanonicalTape] using htargetEq
    · rw [Function.update_of_ne hi]
      exact hotherEq i hi
  · exact le_rfl

private theorem binaryRippleSubExactFrame_transition {n : ℕ}
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

theorem binaryRippleSubRewindTM_hoareTime_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
    (lhsBits rhsBits : List Bool) (lhsBound rhsBound : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryContent lhsBits)
    (hlhsStart : (work₀ lhsIdx).cells 0 = Γ.start)
    (hlhsHead : 1 ≤ (work₀ lhsIdx).head ∧
      (work₀ lhsIdx).head ≤ lhsBound)
    (hrhs : (work₀ rhsIdx).HasBinaryContent rhsBits)
    (hrhsStart : (work₀ rhsIdx).cells 0 = Γ.start)
    (hrhsHead : 1 ≤ (work₀ rhsIdx).head ∧
      (work₀ rhsIdx).head ≤ rhsBound)
    (hresult : Parked (work₀ resultIdx))
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (seqTM (rewindWorkTM lhsIdx) (rewindWorkTM rhsIdx)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work lhsIdx = binaryRippleSubCanonicalTape lhsBits ∧
        work rhsIdx = binaryRippleSubCanonicalTape rhsBits ∧
        work resultIdx = work₀ resultIdx ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (lhsBound + rhsBound + 5) := by
  have hlhsParked : Parked (work₀ lhsIdx) :=
    ⟨hlhsHead.1, hlhs.cells_ne_start⟩
  have hrhsParked : Parked (work₀ rhsIdx) :=
    ⟨hrhsHead.1, hrhs.cells_ne_start⟩
  have hwork₀ : ∀ i, Parked (work₀ i) := by
    intro i
    by_cases hil : i = lhsIdx
    · subst i
      exact hlhsParked
    by_cases hir : i = rhsIdx
    · subst i
      exact hrhsParked
    by_cases hires : i = resultIdx
    · subst i
      exact hresult
    exact hother i hil hir hires

  let lhsTape := binaryRippleSubCanonicalTape lhsBits
  let rhsTape := binaryRippleSubCanonicalTape rhsBits
  let work₁ := Function.update work₀ lhsIdx lhsTape
  let work₂ := Function.update work₁ rhsIdx rhsTape

  have hwork₁ : ∀ i, Parked (work₁ i) := by
    intro i
    by_cases hi : i = lhsIdx
    · subst i
      simpa [work₁, lhsTape] using
        binaryRippleSubCanonicalTape_parked lhsBits
    · simpa only [work₁, Function.update_of_ne hi] using hwork₀ i
  have hrhs₁ : (work₁ rhsIdx).HasBinaryContent rhsBits := by
    simpa only [work₁, Function.update_of_ne hdistinct.lhs_rhs.symm] using
      hrhs
  have hrhsStart₁ : (work₁ rhsIdx).cells 0 = Γ.start := by
    simpa only [work₁, Function.update_of_ne hdistinct.lhs_rhs.symm] using
      hrhsStart
  have hrhsHead₁ : 1 ≤ (work₁ rhsIdx).head ∧
      (work₁ rhsIdx).head ≤ rhsBound := by
    simpa only [work₁, Function.update_of_ne hdistinct.lhs_rhs.symm] using
      hrhsHead

  have hrewindLhs := binaryRippleSubRewindExact_hoareTime lhsIdx lhsBits
    lhsBound inp₀ work₀ out₀ hlhs hlhsStart hlhsHead hinput
    (fun i _ => hwork₀ i) houtput
  have hrewindRhs := binaryRippleSubRewindExact_hoareTime rhsIdx rhsBits
    rhsBound inp₀ work₁ out₀ hrhs₁ hrhsStart₁ hrhsHead₁ hinput
    (fun i _ => hwork₁ i) houtput
  have hrun := seqTM_hoareTime (rewindWorkTM lhsIdx)
    (rewindWorkTM rhsIdx) hrewindLhs
    (binaryRippleSubExactFrame_transition inp₀ work₁ out₀ hinput
      hwork₁ houtput)
    hrewindRhs
  apply hrun.consequence (b' := lhsBound + rhsBound + 5)
  · intro _inp _work _out hpre
    exact hpre
  · rintro inp work out ⟨hinp, hwork, hout⟩
    refine ⟨hinp, ?_, ?_, ?_, ?_, hout⟩
    · simpa [work₂, work₁, rhsTape, lhsTape,
        hdistinct.lhs_rhs] using congrFun hwork lhsIdx
    · simpa [work₂, rhsTape] using congrFun hwork rhsIdx
    · simpa [work₂, work₁, hdistinct.rhs_result,
        hdistinct.rhs_result.symm, hdistinct.lhs_result,
        hdistinct.lhs_result.symm] using congrFun hwork resultIdx
    · intro i hil hir hires
      simpa [work₂, work₁, hir, hil] using congrFun hwork i
  · omega

end TM

end Complexity
