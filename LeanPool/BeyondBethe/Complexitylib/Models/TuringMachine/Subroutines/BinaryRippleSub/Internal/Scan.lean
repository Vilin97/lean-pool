/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# Linear-time canonical binary subtraction -- forward scan proof

This file proves the exact framed contract for the forward borrow scan,
including its final turn into backward cleanup. Cleanup itself is proved in a
separate internal layer.
-/


@[expose] public section

namespace Complexity

namespace TM

private def binaryRippleSubScanAdvanceWork {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) (diff : Bool)
    (work : Fin n → Tape) : Fin n → Tape :=
  fun i =>
    if i = resultIdx then
      (work i).writeAndMove (Γw.ofBool diff) Dir3.right
    else if i = lhsIdx then
      if (work lhsIdx).read = Γ.blank then work i
      else (work i).move Dir3.right
    else if i = rhsIdx then
      if (work rhsIdx).read = Γ.blank then work i
      else (work i).move Dir3.right
    else work i

private def binaryRippleSubScanTurnWork {n : ℕ} (resultIdx : Fin n)
    (work : Fin n → Tape) : Fin n → Tape :=
  Function.update work resultIdx ((work resultIdx).move Dir3.left)

private theorem binaryRippleSubCoreTM_step_active {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (borrow : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hactive : ¬((work lhsIdx).read = Γ.blank ∧
      (work rhsIdx).read = Γ.blank))
    (hinput : inp.read ≠ Γ.start)
    (hlhs : (work lhsIdx).read ≠ Γ.start)
    (hrhs : (work rhsIdx).read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    let lhsBit := decide ((work lhsIdx).read = Γ.one)
    let rhsBit := decide ((work rhsIdx).read = Γ.one)
    let diff := BinaryRippleSub.diffBit borrow lhsBit rhsBit
    let nextBorrow := BinaryRippleSub.borrowBit borrow lhsBit rhsBit
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step
      { state := .scan borrow, input := inp, work := work, output := out } =
      some
        { state := .scan nextBorrow
          input := inp
          work := binaryRippleSubScanAdvanceWork lhsIdx rhsIdx resultIdx diff work
          output := out } := by
  dsimp only
  rw [TM.step, ite_eq_right (by simp [binaryRippleSubCoreTM])]
  simp only [binaryRippleSubCoreTM, hactive, ↓reduceIte]
  refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
    (transitionTape_eq_self houtput))
  funext i
  by_cases hresultIdx : i = resultIdx
  · subst i
    simp [binaryRippleSubScanAdvanceWork]
  · by_cases hlhsIdx : i = lhsIdx
    · subst i
      simp only [binaryRippleSubScanAdvanceWork, hresultIdx, ite_false, ite_eq_left]
      by_cases hblank : (work lhsIdx).read = Γ.blank
      · rw [ite_eq_left hblank, ite_eq_left hblank]
        rw [writeAndMove_readBack _ hlhs Dir3.stay]
        rfl
      · rw [ite_eq_right hblank, ite_eq_right hblank]
        exact writeAndMove_readBack (work lhsIdx) hlhs Dir3.right
    · by_cases hrhsIdx : i = rhsIdx
      · subst i
        simp only [binaryRippleSubScanAdvanceWork, hresultIdx, ite_false,
          hlhsIdx, ite_eq_left]
        by_cases hblank : (work rhsIdx).read = Γ.blank
        · rw [ite_eq_left hblank, ite_eq_left hblank]
          rw [writeAndMove_readBack _ hrhs Dir3.stay]
          rfl
        · rw [ite_eq_right hblank, ite_eq_right hblank]
          exact writeAndMove_readBack (work rhsIdx) hrhs Dir3.right
      · simp only [binaryRippleSubScanAdvanceWork, hresultIdx, ite_false,
          hlhsIdx, hrhsIdx]
        exact transitionTape_eq_self (hother i hlhsIdx hrhsIdx hresultIdx)

private theorem binaryRippleSubCoreTM_step_terminal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
    (borrow : Bool) (emitted : List Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hlhs : (work lhsIdx).read = Γ.blank)
    (hrhs : (work rhsIdx).read = Γ.blank)
    (hinput : inp.read ≠ Γ.start)
    (hresult : (work resultIdx).HasBinaryPrefix emitted)
    (hresultStart : (work resultIdx).cells 0 = Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    let finalWork := binaryRippleSubScanTurnWork resultIdx work
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step
      { state := .scan borrow, input := inp, work := work, output := out } =
      some
        { state := if borrow then .erase else .trim false
          input := inp
          work := finalWork
          output := out } ∧
    (finalWork lhsIdx).cells = (work lhsIdx).cells ∧
    (finalWork lhsIdx).head = (work lhsIdx).head ∧
    (finalWork rhsIdx).cells = (work rhsIdx).cells ∧
    (finalWork rhsIdx).head = (work rhsIdx).head ∧
    (finalWork resultIdx).HasBinaryContent emitted ∧
    (finalWork resultIdx).head = emitted.length ∧
    (finalWork resultIdx).cells 0 = Γ.start ∧
    (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      finalWork i = work i) := by
  dsimp only
  let finalWork := binaryRippleSubScanTurnWork resultIdx work
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [TM.step, ite_eq_right (by simp [binaryRippleSubCoreTM])]
    simp only [binaryRippleSubCoreTM, hlhs, hrhs, and_self, ite_eq_left]
    refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
      (transitionTape_eq_self houtput))
    funext i
    by_cases hires : i = resultIdx
    · subst i
      simp only [binaryRippleSubScanTurnWork, Function.update_self]
      rw [show moveLeftDir (work resultIdx).read = Dir3.left by
        rw [hresult.read_blank]
        rfl]
      exact writeAndMove_readBack (work resultIdx) (by
        rw [hresult.read_blank]
        decide) Dir3.left
    · by_cases hil : i = lhsIdx
      · subst i
        simpa [Γ.ofBool, transitionTape, Γw.toΓ, binaryRippleSubScanTurnWork,
          hdistinct.lhs_result] using
          transitionTape_eq_self (by rw [hlhs]; decide)
      · by_cases hir : i = rhsIdx
        · subst i
          simpa [Γ.ofBool, transitionTape, Γw.toΓ, binaryRippleSubScanTurnWork,
            hdistinct.rhs_result] using
            transitionTape_eq_self (by rw [hrhs]; decide)
        · simpa [binaryRippleSubScanTurnWork, hires] using!
            transitionTape_eq_self (hother i hil hir hires)
  · simp [binaryRippleSubScanTurnWork, hdistinct.lhs_result]
  · simp [binaryRippleSubScanTurnWork, hdistinct.lhs_result]
  · simp [binaryRippleSubScanTurnWork, hdistinct.rhs_result]
  · simp [binaryRippleSubScanTurnWork, hdistinct.rhs_result]
  · simpa [finalWork, binaryRippleSubScanTurnWork, Tape.move_cells] using!
      hresult.2
  · simp [binaryRippleSubScanTurnWork, Tape.move, hresult.1]
  · simpa [finalWork, binaryRippleSubScanTurnWork, Tape.move_cells] using
      hresultStart
  · intro i _ _ hires
    simp [binaryRippleSubScanTurnWork, hires]

private theorem binaryRippleSubCoreTM_suffix_reachesIn {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
    (borrow : Bool) (lhs rhs emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinarySuffix lhs)
    (hrhs : (work₀ rhsIdx).HasBinarySuffix rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix emitted)
    (hresultStart : (work₀ resultIdx).cells 0 = Γ.start)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).reachesIn
        (binaryRippleSubScanTime lhs rhs)
        { state := .scan borrow, input := inp₀, work := work₀, output := out₀ } c' ∧
      c'.state = (if (BinaryRippleSub.scan borrow lhs rhs).borrow then
          .erase else .trim false) ∧
      c'.input = inp₀ ∧
      (c'.work lhsIdx).cells = (work₀ lhsIdx).cells ∧
      (c'.work lhsIdx).head = (work₀ lhsIdx).head + lhs.length ∧
      (c'.work rhsIdx).cells = (work₀ rhsIdx).cells ∧
      (c'.work rhsIdx).head = (work₀ rhsIdx).head + rhs.length ∧
      (c'.work resultIdx).HasBinaryContent
        (emitted ++ (BinaryRippleSub.scan borrow lhs rhs).bits) ∧
      (c'.work resultIdx).head =
        (emitted ++ (BinaryRippleSub.scan borrow lhs rhs).bits).length ∧
      (c'.work resultIdx).cells 0 = Γ.start ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  induction hlength : lhs.length + rhs.length using Nat.strong_induction_on
      generalizing lhs rhs borrow emitted inp₀ work₀ out₀ with
  | h total ih =>
    cases lhs with
    | nil =>
      cases rhs with
      | nil =>
          have hterminal := binaryRippleSubCoreTM_step_terminal
            lhsIdx rhsIdx resultIdx hdistinct borrow emitted inp₀ work₀ out₀
            hlhs.read_nil hrhs.read_nil hinput hresult hresultStart hother houtput
          let finalWork := binaryRippleSubScanTurnWork resultIdx work₀
          let c' : Cfg n BinaryRippleSubPhase :=
            { state := if borrow then .erase else .trim false
              input := inp₀
              work := finalWork
              output := out₀ }
          rcases hterminal with ⟨hstep, hfinalLhs, hfinalLhsHead, hfinalRhs,
            hfinalRhsHead, hfinalResult, hfinalResultHead, hfinalResultStart,
            hfinalOther⟩
          refine ⟨c', ?_, by
            cases borrow <;> simp [c', BinaryRippleSub.scan] <;> rfl, rfl,
            hfinalLhs, ?_, hfinalRhs, ?_, ?_, ?_,
            hfinalResultStart, hfinalOther, rfl⟩
          · have hreach :
                (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).reachesIn 1
                  { state := .scan borrow, input := inp₀, work := work₀,
                    output := out₀ } c' :=
              .step hstep .zero
            simpa [binaryRippleSubScanTime] using hreach
          · simpa using hfinalLhsHead
          · simpa using hfinalRhsHead
          · simpa [BinaryRippleSub.scan] using hfinalResult
          · simpa [BinaryRippleSub.scan] using hfinalResultHead
      | cons rhsBit rhsTail =>
          have hlhsBit : decide ((work₀ lhsIdx).read = Γ.one) = false := by
            rw [hlhs.read_nil]
            decide
          have hrhsBit : decide ((work₀ rhsIdx).read = Γ.one) = rhsBit := by
            rw [hrhs.read_cons]
            cases rhsBit <;> rfl
          let diff := BinaryRippleSub.diffBit borrow false rhsBit
          let nextBorrow := BinaryRippleSub.borrowBit borrow false rhsBit
          let work₁ := binaryRippleSubScanAdvanceWork lhsIdx rhsIdx resultIdx
            diff work₀
          have hactive : ¬((work₀ lhsIdx).read = Γ.blank ∧
              (work₀ rhsIdx).read = Γ.blank) := by
            intro hblank
            rw [hrhs.read_cons] at hblank
            cases rhsBit <;> simp [Γ.ofBool] at hblank
          have hrhsNotBlank : (work₀ rhsIdx).read ≠ Γ.blank := by
            rw [hrhs.read_cons]
            cases rhsBit <;> decide
          have hstep :
              (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step
                { state := .scan borrow, input := inp₀, work := work₀,
                  output := out₀ } =
                some
                  { state := .scan nextBorrow
                    input := inp₀
                    work := work₁
                    output := out₀ } := by
            simpa [hlhsBit, hrhsBit, diff, nextBorrow, work₁] using
              binaryRippleSubCoreTM_step_active lhsIdx rhsIdx resultIdx borrow
                inp₀ work₀ out₀ hactive hinput hlhs.read_ne_start
                hrhs.read_ne_start hother houtput
          have hlhs₁ : (work₁ lhsIdx).HasBinarySuffix [] := by
            simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.lhs_result, hlhs.read_nil] using hlhs
          have hrhs₁ : (work₁ rhsIdx).HasBinarySuffix rhsTail := by
            simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhsNotBlank] using hrhs.move_right_cons
          have hresult₁ :
              (work₁ resultIdx).HasBinaryPrefix (emitted ++ [diff]) := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool diff).toΓ
                Dir3.right by
              simp [work₁, binaryRippleSubScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit diff hresult
          have hresultStart₁ : (work₁ resultIdx).cells 0 = Γ.start := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool diff).toΓ
                Dir3.right by
              simp [work₁, binaryRippleSubScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit_cell0 diff hresult hresultStart
          have hother₁ : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
              (work₁ i).read ≠ Γ.start := by
            intro i hil hir hires
            simpa [work₁, binaryRippleSubScanAdvanceWork, hil, hir, hires] using
              hother i hil hir hires
          have htailLength : rhsTail.length < total := by
            simp only [List.length_nil, zero_add, List.length_cons] at hlength
            omega
          obtain ⟨c', hreach, hstate, hfinalInput, hfinalLhs,
              hfinalLhsHead, hfinalRhs, hfinalRhsHead, hfinalResult,
              hfinalResultHead, hfinalResultStart, hfinalOther, hfinalOutput⟩ :=
            ih rhsTail.length htailLength nextBorrow [] rhsTail
              (emitted ++ [diff]) inp₀ work₁ out₀ hlhs₁ hrhs₁ hresult₁
              hresultStart₁ hinput hother₁ houtput (by simp)
          refine ⟨c', ?_, ?_, hfinalInput, ?_, ?_, ?_, ?_, ?_, ?_,
            hfinalResultStart, ?_, hfinalOutput⟩
          · simpa [binaryRippleSubScanTime] using
              TM.reachesIn.step hstep hreach
          · simpa [BinaryRippleSub.scan, nextBorrow] using hstate
          · simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.lhs_result, hlhs.read_nil] using hfinalLhs
          · simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.lhs_result, hlhs.read_nil] using hfinalLhsHead
          · simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhsNotBlank, Tape.move_cells] using hfinalRhs
          · rw [hfinalRhsHead]
            simp only [work₁, binaryRippleSubScanAdvanceWork,
              ite_eq_right hdistinct.rhs_result,
              ite_eq_right (Ne.symm hdistinct.lhs_rhs), ite_eq_left,
              ite_eq_right hrhsNotBlank, Tape.move, List.length_cons]
            omega
          · simpa [BinaryRippleSub.scan, diff, nextBorrow,
              List.append_assoc] using hfinalResult
          · simpa [BinaryRippleSub.scan, diff, nextBorrow,
              List.append_assoc] using hfinalResultHead
          · intro i hil hir hires
            rw [hfinalOther i hil hir hires]
            simp [work₁, binaryRippleSubScanAdvanceWork, hil, hir, hires]
    | cons lhsBit lhsTail =>
      cases rhs with
      | nil =>
          have hlhsBit : decide ((work₀ lhsIdx).read = Γ.one) = lhsBit := by
            rw [hlhs.read_cons]
            cases lhsBit <;> rfl
          have hrhsBit : decide ((work₀ rhsIdx).read = Γ.one) = false := by
            rw [hrhs.read_nil]
            decide
          let diff := BinaryRippleSub.diffBit borrow lhsBit false
          let nextBorrow := BinaryRippleSub.borrowBit borrow lhsBit false
          let work₁ := binaryRippleSubScanAdvanceWork lhsIdx rhsIdx resultIdx
            diff work₀
          have hactive : ¬((work₀ lhsIdx).read = Γ.blank ∧
              (work₀ rhsIdx).read = Γ.blank) := by
            intro hblank
            rw [hlhs.read_cons] at hblank
            cases lhsBit <;> simp [Γ.ofBool] at hblank
          have hlhsNotBlank : (work₀ lhsIdx).read ≠ Γ.blank := by
            rw [hlhs.read_cons]
            cases lhsBit <;> decide
          have hstep :
              (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step
                { state := .scan borrow, input := inp₀, work := work₀,
                  output := out₀ } =
                some
                  { state := .scan nextBorrow
                    input := inp₀
                    work := work₁
                    output := out₀ } := by
            simpa [hlhsBit, hrhsBit, diff, nextBorrow, work₁] using
              binaryRippleSubCoreTM_step_active lhsIdx rhsIdx resultIdx borrow
                inp₀ work₀ out₀ hactive hinput hlhs.read_ne_start
                hrhs.read_ne_start hother houtput
          have hlhs₁ : (work₁ lhsIdx).HasBinarySuffix lhsTail := by
            simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.lhs_result, hlhsNotBlank] using hlhs.move_right_cons
          have hrhs₁ : (work₁ rhsIdx).HasBinarySuffix [] := by
            simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhs.read_nil] using hrhs
          have hresult₁ :
              (work₁ resultIdx).HasBinaryPrefix (emitted ++ [diff]) := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool diff).toΓ
                Dir3.right by
              simp [work₁, binaryRippleSubScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit diff hresult
          have hresultStart₁ : (work₁ resultIdx).cells 0 = Γ.start := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool diff).toΓ
                Dir3.right by
              simp [work₁, binaryRippleSubScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit_cell0 diff hresult hresultStart
          have hother₁ : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
              (work₁ i).read ≠ Γ.start := by
            intro i hil hir hires
            simpa [work₁, binaryRippleSubScanAdvanceWork, hil, hir, hires] using
              hother i hil hir hires
          have htailLength : lhsTail.length < total := by
            simp only [List.length_nil, Nat.add_zero, List.length_cons] at hlength
            omega
          obtain ⟨c', hreach, hstate, hfinalInput, hfinalLhs,
              hfinalLhsHead, hfinalRhs, hfinalRhsHead, hfinalResult,
              hfinalResultHead, hfinalResultStart, hfinalOther, hfinalOutput⟩ :=
            ih lhsTail.length htailLength nextBorrow lhsTail []
              (emitted ++ [diff]) inp₀ work₁ out₀ hlhs₁ hrhs₁ hresult₁
              hresultStart₁ hinput hother₁ houtput (by simp)
          refine ⟨c', ?_, ?_, hfinalInput, ?_, ?_, ?_, ?_, ?_, ?_,
            hfinalResultStart, ?_, hfinalOutput⟩
          · simpa [binaryRippleSubScanTime] using
              TM.reachesIn.step hstep hreach
          · simpa [BinaryRippleSub.scan, nextBorrow] using hstate
          · simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.lhs_result, hlhsNotBlank, Tape.move_cells] using
              hfinalLhs
          · rw [hfinalLhsHead]
            simp only [work₁, binaryRippleSubScanAdvanceWork,
              ite_eq_right hdistinct.lhs_result, ite_eq_left, ite_eq_right hlhsNotBlank,
              Tape.move, List.length_cons]
            omega
          · simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhs.read_nil] using hfinalRhs
          · simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhs.read_nil] using hfinalRhsHead
          · simpa [BinaryRippleSub.scan, diff, nextBorrow,
              List.append_assoc] using hfinalResult
          · simpa [BinaryRippleSub.scan, diff, nextBorrow,
              List.append_assoc] using hfinalResultHead
          · intro i hil hir hires
            rw [hfinalOther i hil hir hires]
            simp [work₁, binaryRippleSubScanAdvanceWork, hil, hir, hires]
      | cons rhsBit rhsTail =>
          have hlhsBit : decide ((work₀ lhsIdx).read = Γ.one) = lhsBit := by
            rw [hlhs.read_cons]
            cases lhsBit <;> rfl
          have hrhsBit : decide ((work₀ rhsIdx).read = Γ.one) = rhsBit := by
            rw [hrhs.read_cons]
            cases rhsBit <;> rfl
          let diff := BinaryRippleSub.diffBit borrow lhsBit rhsBit
          let nextBorrow := BinaryRippleSub.borrowBit borrow lhsBit rhsBit
          let work₁ := binaryRippleSubScanAdvanceWork lhsIdx rhsIdx resultIdx
            diff work₀
          have hactive : ¬((work₀ lhsIdx).read = Γ.blank ∧
              (work₀ rhsIdx).read = Γ.blank) := by
            intro hblank
            rw [hlhs.read_cons] at hblank
            cases lhsBit <;> simp [Γ.ofBool] at hblank
          have hlhsNotBlank : (work₀ lhsIdx).read ≠ Γ.blank := by
            rw [hlhs.read_cons]
            cases lhsBit <;> decide
          have hrhsNotBlank : (work₀ rhsIdx).read ≠ Γ.blank := by
            rw [hrhs.read_cons]
            cases rhsBit <;> decide
          have hstep :
              (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step
                { state := .scan borrow, input := inp₀, work := work₀,
                  output := out₀ } =
                some
                  { state := .scan nextBorrow
                    input := inp₀
                    work := work₁
                    output := out₀ } := by
            simpa [hlhsBit, hrhsBit, diff, nextBorrow, work₁] using
              binaryRippleSubCoreTM_step_active lhsIdx rhsIdx resultIdx borrow
                inp₀ work₀ out₀ hactive hinput hlhs.read_ne_start
                hrhs.read_ne_start hother houtput
          have hlhs₁ : (work₁ lhsIdx).HasBinarySuffix lhsTail := by
            simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.lhs_result, hlhsNotBlank] using hlhs.move_right_cons
          have hrhs₁ : (work₁ rhsIdx).HasBinarySuffix rhsTail := by
            simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhsNotBlank] using hrhs.move_right_cons
          have hresult₁ :
              (work₁ resultIdx).HasBinaryPrefix (emitted ++ [diff]) := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool diff).toΓ
                Dir3.right by
              simp [work₁, binaryRippleSubScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit diff hresult
          have hresultStart₁ : (work₁ resultIdx).cells 0 = Γ.start := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool diff).toΓ
                Dir3.right by
              simp [work₁, binaryRippleSubScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit_cell0 diff hresult hresultStart
          have hother₁ : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
              (work₁ i).read ≠ Γ.start := by
            intro i hil hir hires
            simpa [work₁, binaryRippleSubScanAdvanceWork, hil, hir, hires] using
              hother i hil hir hires
          have htailLength : lhsTail.length + rhsTail.length < total := by
            simp only [List.length_cons] at hlength
            omega
          obtain ⟨c', hreach, hstate, hfinalInput, hfinalLhs,
              hfinalLhsHead, hfinalRhs, hfinalRhsHead, hfinalResult,
              hfinalResultHead, hfinalResultStart, hfinalOther, hfinalOutput⟩ :=
            ih (lhsTail.length + rhsTail.length) htailLength nextBorrow lhsTail
              rhsTail (emitted ++ [diff]) inp₀ work₁ out₀ hlhs₁ hrhs₁
              hresult₁ hresultStart₁ hinput hother₁ houtput rfl
          refine ⟨c', ?_, ?_, hfinalInput, ?_, ?_, ?_, ?_, ?_, ?_,
            hfinalResultStart, ?_, hfinalOutput⟩
          · simpa [binaryRippleSubScanTime, Nat.succ_max_succ] using
              TM.reachesIn.step hstep hreach
          · simpa [BinaryRippleSub.scan, nextBorrow] using hstate
          · simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.lhs_result, hlhsNotBlank, Tape.move_cells] using
              hfinalLhs
          · rw [hfinalLhsHead]
            simp only [work₁, binaryRippleSubScanAdvanceWork,
              ite_eq_right hdistinct.lhs_result, ite_eq_left, ite_eq_right hlhsNotBlank,
              Tape.move, List.length_cons]
            omega
          · simpa [work₁, binaryRippleSubScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhsNotBlank, Tape.move_cells] using hfinalRhs
          · rw [hfinalRhsHead]
            simp only [work₁, binaryRippleSubScanAdvanceWork,
              ite_eq_right hdistinct.rhs_result,
              ite_eq_right (Ne.symm hdistinct.lhs_rhs), ite_eq_left,
              ite_eq_right hrhsNotBlank, Tape.move, List.length_cons]
            omega
          · simpa [BinaryRippleSub.scan, diff, nextBorrow,
              List.append_assoc] using hfinalResult
          · simpa [BinaryRippleSub.scan, diff, nextBorrow,
              List.append_assoc] using hfinalResultHead
          · intro i hil hir hires
            rw [hfinalOther i hil hir hires]
            simp [work₁, binaryRippleSubScanAdvanceWork, hil, hir, hires]

theorem binaryRippleSubCoreTM_scan_reachesIn_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hresultStart : (work₀ resultIdx).cells 0 = Γ.start)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    let raw := BinaryRippleSub.scan false lhs rhs
    ∃ c',
      (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).reachesIn
        (binaryRippleSubScanTime lhs rhs)
        { state := (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      c'.state = (if raw.borrow then .erase else .trim false) ∧
      c'.input = inp₀ ∧
      (c'.work lhsIdx).cells = (work₀ lhsIdx).cells ∧
      (c'.work lhsIdx).head = lhs.length + 1 ∧
      (c'.work rhsIdx).cells = (work₀ rhsIdx).cells ∧
      (c'.work rhsIdx).head = rhs.length + 1 ∧
      (c'.work resultIdx).HasBinaryContent raw.bits ∧
      (c'.work resultIdx).head = raw.bits.length ∧
      (c'.work resultIdx).cells 0 = Γ.start ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  dsimp only
  obtain ⟨c', hreach, hstate, hfinalInput, hfinalLhs, hfinalLhsHead,
      hfinalRhs, hfinalRhsHead, hfinalResult, hfinalResultHead,
      hfinalResultStart, hfinalOther, hfinalOutput⟩ :=
    binaryRippleSubCoreTM_suffix_reachesIn lhsIdx rhsIdx resultIdx hdistinct
      false lhs rhs [] inp₀ work₀ out₀ hlhs.hasBinarySuffix
      hrhs.hasBinarySuffix hresult hresultStart hinput hother houtput
  refine ⟨c', hreach, hstate, hfinalInput, hfinalLhs, ?_, hfinalRhs, ?_, ?_,
    ?_, hfinalResultStart, hfinalOther, hfinalOutput⟩
  · simpa [hlhs.1, Nat.add_comm] using hfinalLhsHead
  · simpa [hrhs.1, Nat.add_comm] using hfinalRhsHead
  · simpa using hfinalResult
  · simpa using hfinalResultHead

end TM

end Complexity
