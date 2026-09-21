/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Linear-time canonical binary addition -- scan proof

This file proves the exact operational contract for the carry-bearing forward
scan. Rewinding and the complete canonical-natural interface are composed in
later internal layers.
-/


public section

namespace Complexity

namespace TM

private def binaryRippleAddScanAdvanceWork {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) (sum : Bool)
    (work : Fin n → Tape) : Fin n → Tape :=
  fun i =>
    if i = resultIdx then
      (work i).writeAndMove (Γw.ofBool sum) Dir3.right
    else if i = lhsIdx then
      if (work lhsIdx).read = Γ.blank then work i
      else (work i).move Dir3.right
    else if i = rhsIdx then
      if (work rhsIdx).read = Γ.blank then work i
      else (work i).move Dir3.right
    else work i

private theorem writeAndMove_readBack_right {tape : Tape}
    (hread : tape.read ≠ Γ.start) :
    tape.writeAndMove (readBackWrite tape.read) Dir3.right =
      tape.move Dir3.right := by
  cases tape with
  | mk head cells =>
      simp only [Tape.writeAndMove, Tape.read] at hread ⊢
      rw [toΓ_readBackWrite_of_ne_start hread]
      simp [Tape.write, Tape.move, Function.update_eq_self]

private theorem writeAndMove_readBack_stay {tape : Tape}
    (hread : tape.read ≠ Γ.start) :
    tape.writeAndMove (readBackWrite tape.read) Dir3.stay = tape := by
  rw [toΓ_readBackWrite_of_ne_start hread]
  simp only [Tape.writeAndMove, Tape.move, Tape.write]
  split
  · rfl
  · simp only [Tape.read, Function.update_eq_self]

private theorem binaryRippleAddScanTM_step_active {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (carry : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
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
    let sum := BinaryRippleAdd.sumBit carry lhsBit rhsBit
    let nextCarry := BinaryRippleAdd.carryBit carry lhsBit rhsBit
    (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).step
      { state := .scan carry, input := inp, work := work, output := out } =
      some
        { state := .scan nextCarry
          input := inp
          work := binaryRippleAddScanAdvanceWork lhsIdx rhsIdx resultIdx sum work
          output := out } := by
  dsimp only
  rw [TM.step, ite_eq_right (by simp [binaryRippleAddScanTM])]
  simp only [binaryRippleAddScanTM, hactive, ↓reduceIte]
  refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
    (transitionTape_eq_self houtput))
  funext i
  by_cases hresultIdx : i = resultIdx
  · subst i
    simp [binaryRippleAddScanAdvanceWork]
  · by_cases hlhsIdx : i = lhsIdx
    · subst i
      simp only [binaryRippleAddScanAdvanceWork, hresultIdx, ite_false,
        ite_eq_left]
      by_cases hblank : (work lhsIdx).read = Γ.blank
      · rw [ite_eq_left hblank, ite_eq_left hblank]
        simpa [hblank] using
          writeAndMove_readBack_stay (show (work lhsIdx).read ≠ Γ.start from hlhs)
      · rw [ite_eq_right hblank, ite_eq_right hblank]
        exact writeAndMove_readBack_right hlhs
    · by_cases hrhsIdx : i = rhsIdx
      · subst i
        simp only [binaryRippleAddScanAdvanceWork, hresultIdx, ite_false,
          hlhsIdx, ite_eq_left]
        by_cases hblank : (work rhsIdx).read = Γ.blank
        · rw [ite_eq_left hblank, ite_eq_left hblank]
          simpa [hblank] using
            writeAndMove_readBack_stay (show (work rhsIdx).read ≠ Γ.start from hrhs)
        · rw [ite_eq_right hblank, ite_eq_right hblank]
          exact writeAndMove_readBack_right hrhs
      · simp only [binaryRippleAddScanAdvanceWork, hresultIdx, ite_false,
          hlhsIdx, hrhsIdx]
        exact transitionTape_eq_self (hother i hlhsIdx hrhsIdx hresultIdx)

private theorem binaryRippleAddScanTM_step_terminal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (carry : Bool) (emitted : List Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hlhs : (work lhsIdx).read = Γ.blank)
    (hrhs : (work rhsIdx).read = Γ.blank)
    (hinput : inp.read ≠ Γ.start)
    (hresult : (work resultIdx).HasBinaryPrefix emitted)
    (hresultStart : (work resultIdx).cells 0 = Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    ∃ finalWork,
      (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).step
        { state := .scan carry, input := inp, work := work, output := out } =
        some { state := .done, input := inp, work := finalWork, output := out } ∧
      (finalWork lhsIdx).cells = (work lhsIdx).cells ∧
      (finalWork lhsIdx).head = (work lhsIdx).head ∧
      (finalWork rhsIdx).cells = (work rhsIdx).cells ∧
      (finalWork rhsIdx).head = (work rhsIdx).head ∧
      (finalWork resultIdx).HasBinaryPrefix
        (emitted ++ BinaryRippleAdd.ripple carry [] []) ∧
      (finalWork resultIdx).cells 0 = Γ.start ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        finalWork i = work i) := by
  cases carry with
  | false =>
      refine ⟨work, ?_, rfl, rfl, rfl, rfl, ?_, hresultStart, ?_⟩
      · rw [TM.step, ite_eq_right (by simp [binaryRippleAddScanTM])]
        simp only [binaryRippleAddScanTM, hlhs, hrhs, and_self, ite_eq_left,
          Bool.false_eq_true, ite_false, allReadBack]
        refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
          (transitionTape_eq_self houtput))
        funext i
        by_cases hil : i = lhsIdx
        · subst i
          exact transitionTape_eq_self (by rw [hlhs]; decide)
        · by_cases hir : i = rhsIdx
          · subst i
            exact transitionTape_eq_self (by rw [hrhs]; decide)
          · by_cases hires : i = resultIdx
            · subst i
              exact transitionTape_eq_self (by
                rw [hresult.read_blank]
                decide)
            · exact transitionTape_eq_self (hother i hil hir hires)
      · simpa [BinaryRippleAdd.ripple] using hresult
      · intro i _ _ _
        rfl
  | true =>
      let finalWork := Function.update work resultIdx
        ((work resultIdx).writeAndMove Γ.one Dir3.right)
      refine ⟨finalWork, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [TM.step, ite_eq_right (by simp [binaryRippleAddScanTM])]
        simp only [binaryRippleAddScanTM, hlhs, hrhs, and_self, ite_eq_left]
        refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
          (transitionTape_eq_self houtput))
        funext i
        by_cases hires : i = resultIdx
        · subst i
          simp [finalWork]
        · by_cases hil : i = lhsIdx
          · subst i
            simpa [finalWork, hdistinct.lhs_result] using
              transitionTape_eq_self (by rw [hlhs]; decide)
          · by_cases hir : i = rhsIdx
            · subst i
              simpa [finalWork, hdistinct.rhs_result] using
                transitionTape_eq_self (by rw [hrhs]; decide)
            · simpa [finalWork, hires] using
                transitionTape_eq_self (hother i hil hir hires)
      · simp [finalWork, hdistinct.lhs_result]
      · simp [finalWork, hdistinct.lhs_result]
      · simp [finalWork, hdistinct.rhs_result]
      · simp [finalWork, hdistinct.rhs_result]
      · simpa [finalWork, BinaryRippleAdd.ripple] using
          Tape.hasBinaryPrefix_write_bit true hresult
      · simpa [finalWork] using
          Tape.hasBinaryPrefix_write_bit_cell0 true hresult hresultStart
      · intro i _ _ hires
        simp [finalWork, hires]

private theorem binaryRippleAddScanTM_suffix_reachesIn {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (carry : Bool) (lhs rhs emitted : List Bool)
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
      (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).reachesIn
        (binaryRippleAddScanTime lhs rhs)
        { state := .scan carry, input := inp₀, work := work₀, output := out₀ } c' ∧
      (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work lhsIdx).cells = (work₀ lhsIdx).cells ∧
      (c'.work lhsIdx).head = (work₀ lhsIdx).head + lhs.length ∧
      (c'.work rhsIdx).cells = (work₀ rhsIdx).cells ∧
      (c'.work rhsIdx).head = (work₀ rhsIdx).head + rhs.length ∧
      (c'.work resultIdx).HasBinaryPrefix
        (emitted ++ BinaryRippleAdd.ripple carry lhs rhs) ∧
      (c'.work resultIdx).cells 0 = Γ.start ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  induction hlength : lhs.length + rhs.length using Nat.strong_induction_on
      generalizing lhs rhs carry emitted inp₀ work₀ out₀ with
  | h total ih =>
    cases lhs with
    | nil =>
      cases rhs with
      | nil =>
          obtain ⟨finalWork, hstep, hfinalLhs, hfinalLhsHead, hfinalRhs,
              hfinalRhsHead, hfinalResult, hfinalResultStart, hfinalOther⟩ :=
            binaryRippleAddScanTM_step_terminal lhsIdx rhsIdx resultIdx
              hdistinct carry emitted inp₀ work₀ out₀ hlhs.read_nil
              hrhs.read_nil hinput hresult hresultStart hother houtput
          let c' : Cfg n BinaryRippleAddPhase :=
            { state := .done, input := inp₀, work := finalWork, output := out₀ }
          refine ⟨c', ?_, rfl, rfl, hfinalLhs, ?_, hfinalRhs, ?_,
            hfinalResult, hfinalResultStart, hfinalOther, rfl⟩
          · have hreach :
                (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).reachesIn 1
                  { state := .scan carry, input := inp₀, work := work₀,
                    output := out₀ } c' :=
              .step hstep .zero
            simpa [binaryRippleAddScanTime] using hreach
          · simpa using hfinalLhsHead
          · simpa using hfinalRhsHead
      | cons rhsBit rhsTail =>
          have hlhsBit : decide ((work₀ lhsIdx).read = Γ.one) = false := by
            rw [hlhs.read_nil]
            decide
          have hrhsBit : decide ((work₀ rhsIdx).read = Γ.one) = rhsBit := by
            rw [hrhs.read_cons]
            cases rhsBit <;> rfl
          let sum := BinaryRippleAdd.sumBit carry false rhsBit
          let nextCarry := BinaryRippleAdd.carryBit carry false rhsBit
          let work₁ := binaryRippleAddScanAdvanceWork lhsIdx rhsIdx resultIdx
            sum work₀
          have hactive : ¬((work₀ lhsIdx).read = Γ.blank ∧
              (work₀ rhsIdx).read = Γ.blank) := by
            intro hblank
            rw [hrhs.read_cons] at hblank
            cases rhsBit <;> simp [Γ.ofBool] at hblank
          have hrhsNotBlank : (work₀ rhsIdx).read ≠ Γ.blank := by
            rw [hrhs.read_cons]
            cases rhsBit <;> decide
          have hstep :
              (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).step
                { state := .scan carry, input := inp₀, work := work₀,
                  output := out₀ } =
                some
                  { state := .scan nextCarry
                    input := inp₀
                    work := work₁
                    output := out₀ } := by
            simpa [hlhsBit, hrhsBit, sum, nextCarry, work₁] using
              binaryRippleAddScanTM_step_active lhsIdx rhsIdx resultIdx carry
                inp₀ work₀ out₀ hactive hinput hlhs.read_ne_start
                hrhs.read_ne_start hother houtput
          have hlhs₁ : (work₁ lhsIdx).HasBinarySuffix [] := by
            simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.lhs_result, hlhs.read_nil] using hlhs
          have hrhs₁ : (work₁ rhsIdx).HasBinarySuffix rhsTail := by
            simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhsNotBlank] using hrhs.move_right_cons
          have hresult₁ :
              (work₁ resultIdx).HasBinaryPrefix (emitted ++ [sum]) := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool sum).toΓ
                Dir3.right by
              simp [work₁, binaryRippleAddScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit sum hresult
          have hresultStart₁ : (work₁ resultIdx).cells 0 = Γ.start := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool sum).toΓ
                Dir3.right by
              simp [work₁, binaryRippleAddScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit_cell0 sum hresult hresultStart
          have hother₁ : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
              (work₁ i).read ≠ Γ.start := by
            intro i hil hir hires
            simpa [work₁, binaryRippleAddScanAdvanceWork, hil, hir, hires] using
              hother i hil hir hires
          have htailLength : rhsTail.length < total := by
            simp only [List.length_nil, zero_add, List.length_cons] at hlength
            omega
          obtain ⟨c', hreach, hhalt, hfinalInput, hfinalLhs,
              hfinalLhsHead, hfinalRhs, hfinalRhsHead, hfinalResult,
              hfinalResultStart, hfinalOther, hfinalOutput⟩ :=
            ih rhsTail.length htailLength nextCarry [] rhsTail
              (emitted ++ [sum]) inp₀ work₁ out₀ hlhs₁ hrhs₁ hresult₁
              hresultStart₁ hinput hother₁ houtput (by simp)
          refine ⟨c', ?_, hhalt, hfinalInput, ?_, ?_, ?_, ?_, ?_,
            hfinalResultStart, ?_, hfinalOutput⟩
          · simpa [binaryRippleAddScanTime] using
              TM.reachesIn.step hstep hreach
          · simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.lhs_result, hlhs.read_nil] using hfinalLhs
          · simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.lhs_result, hlhs.read_nil] using hfinalLhsHead
          · simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhsNotBlank, Tape.move_cells] using hfinalRhs
          · rw [hfinalRhsHead]
            simp only [work₁, binaryRippleAddScanAdvanceWork,
              ite_eq_right hdistinct.rhs_result,
              ite_eq_right (Ne.symm hdistinct.lhs_rhs), ite_eq_left,
              ite_eq_right hrhsNotBlank, Tape.move, List.length_cons]
            omega
          · simpa [BinaryRippleAdd.ripple, sum, nextCarry,
              List.append_assoc] using hfinalResult
          · intro i hil hir hires
            rw [hfinalOther i hil hir hires]
            simp [work₁, binaryRippleAddScanAdvanceWork, hil, hir, hires]
    | cons lhsBit lhsTail =>
      cases rhs with
      | nil =>
          have hlhsBit : decide ((work₀ lhsIdx).read = Γ.one) = lhsBit := by
            rw [hlhs.read_cons]
            cases lhsBit <;> rfl
          have hrhsBit : decide ((work₀ rhsIdx).read = Γ.one) = false := by
            rw [hrhs.read_nil]
            decide
          let sum := BinaryRippleAdd.sumBit carry lhsBit false
          let nextCarry := BinaryRippleAdd.carryBit carry lhsBit false
          let work₁ := binaryRippleAddScanAdvanceWork lhsIdx rhsIdx resultIdx
            sum work₀
          have hactive : ¬((work₀ lhsIdx).read = Γ.blank ∧
              (work₀ rhsIdx).read = Γ.blank) := by
            intro hblank
            rw [hlhs.read_cons] at hblank
            cases lhsBit <;> simp [Γ.ofBool] at hblank
          have hlhsNotBlank : (work₀ lhsIdx).read ≠ Γ.blank := by
            rw [hlhs.read_cons]
            cases lhsBit <;> decide
          have hstep :
              (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).step
                { state := .scan carry, input := inp₀, work := work₀,
                  output := out₀ } =
                some
                  { state := .scan nextCarry
                    input := inp₀
                    work := work₁
                    output := out₀ } := by
            simpa [hlhsBit, hrhsBit, sum, nextCarry, work₁] using
              binaryRippleAddScanTM_step_active lhsIdx rhsIdx resultIdx carry
                inp₀ work₀ out₀ hactive hinput hlhs.read_ne_start
                hrhs.read_ne_start hother houtput
          have hlhs₁ : (work₁ lhsIdx).HasBinarySuffix lhsTail := by
            simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.lhs_result, hlhsNotBlank] using hlhs.move_right_cons
          have hrhs₁ : (work₁ rhsIdx).HasBinarySuffix [] := by
            simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhs.read_nil] using hrhs
          have hresult₁ :
              (work₁ resultIdx).HasBinaryPrefix (emitted ++ [sum]) := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool sum).toΓ
                Dir3.right by
              simp [work₁, binaryRippleAddScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit sum hresult
          have hresultStart₁ : (work₁ resultIdx).cells 0 = Γ.start := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool sum).toΓ
                Dir3.right by
              simp [work₁, binaryRippleAddScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit_cell0 sum hresult hresultStart
          have hother₁ : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
              (work₁ i).read ≠ Γ.start := by
            intro i hil hir hires
            simpa [work₁, binaryRippleAddScanAdvanceWork, hil, hir, hires] using
              hother i hil hir hires
          have htailLength : lhsTail.length < total := by
            simp only [List.length_nil, Nat.add_zero, List.length_cons] at hlength
            omega
          obtain ⟨c', hreach, hhalt, hfinalInput, hfinalLhs,
              hfinalLhsHead, hfinalRhs, hfinalRhsHead, hfinalResult,
              hfinalResultStart, hfinalOther, hfinalOutput⟩ :=
            ih lhsTail.length htailLength nextCarry lhsTail []
              (emitted ++ [sum]) inp₀ work₁ out₀ hlhs₁ hrhs₁ hresult₁
              hresultStart₁ hinput hother₁ houtput (by simp)
          refine ⟨c', ?_, hhalt, hfinalInput, ?_, ?_, ?_, ?_, ?_,
            hfinalResultStart, ?_, hfinalOutput⟩
          · simpa [binaryRippleAddScanTime] using
              TM.reachesIn.step hstep hreach
          · simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.lhs_result, hlhsNotBlank, Tape.move_cells] using
              hfinalLhs
          · rw [hfinalLhsHead]
            simp only [work₁, binaryRippleAddScanAdvanceWork,
              ite_eq_right hdistinct.lhs_result, ite_eq_left, ite_eq_right hlhsNotBlank,
              Tape.move, List.length_cons]
            omega
          · simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhs.read_nil] using hfinalRhs
          · simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhs.read_nil] using hfinalRhsHead
          · simpa [BinaryRippleAdd.ripple, sum, nextCarry,
              List.append_assoc] using hfinalResult
          · intro i hil hir hires
            rw [hfinalOther i hil hir hires]
            simp [work₁, binaryRippleAddScanAdvanceWork, hil, hir, hires]
      | cons rhsBit rhsTail =>
          have hlhsBit : decide ((work₀ lhsIdx).read = Γ.one) = lhsBit := by
            rw [hlhs.read_cons]
            cases lhsBit <;> rfl
          have hrhsBit : decide ((work₀ rhsIdx).read = Γ.one) = rhsBit := by
            rw [hrhs.read_cons]
            cases rhsBit <;> rfl
          let sum := BinaryRippleAdd.sumBit carry lhsBit rhsBit
          let nextCarry := BinaryRippleAdd.carryBit carry lhsBit rhsBit
          let work₁ := binaryRippleAddScanAdvanceWork lhsIdx rhsIdx resultIdx
            sum work₀
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
              (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).step
                { state := .scan carry, input := inp₀, work := work₀,
                  output := out₀ } =
                some
                  { state := .scan nextCarry
                    input := inp₀
                    work := work₁
                    output := out₀ } := by
            simpa [hlhsBit, hrhsBit, sum, nextCarry, work₁] using
              binaryRippleAddScanTM_step_active lhsIdx rhsIdx resultIdx carry
                inp₀ work₀ out₀ hactive hinput hlhs.read_ne_start
                hrhs.read_ne_start hother houtput
          have hlhs₁ : (work₁ lhsIdx).HasBinarySuffix lhsTail := by
            simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.lhs_result, hlhsNotBlank] using hlhs.move_right_cons
          have hrhs₁ : (work₁ rhsIdx).HasBinarySuffix rhsTail := by
            simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhsNotBlank] using hrhs.move_right_cons
          have hresult₁ :
              (work₁ resultIdx).HasBinaryPrefix (emitted ++ [sum]) := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool sum).toΓ
                Dir3.right by
              simp [work₁, binaryRippleAddScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit sum hresult
          have hresultStart₁ : (work₁ resultIdx).cells 0 = Γ.start := by
            rw [show work₁ resultIdx =
              (work₀ resultIdx).writeAndMove (Γw.ofBool sum).toΓ
                Dir3.right by
              simp [work₁, binaryRippleAddScanAdvanceWork]]
            rw [Γw.ofBool_toΓ]
            exact Tape.hasBinaryPrefix_write_bit_cell0 sum hresult hresultStart
          have hother₁ : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
              (work₁ i).read ≠ Γ.start := by
            intro i hil hir hires
            simpa [work₁, binaryRippleAddScanAdvanceWork, hil, hir, hires] using
              hother i hil hir hires
          have htailLength : lhsTail.length + rhsTail.length < total := by
            simp only [List.length_cons] at hlength
            omega
          obtain ⟨c', hreach, hhalt, hfinalInput, hfinalLhs,
              hfinalLhsHead, hfinalRhs, hfinalRhsHead, hfinalResult,
              hfinalResultStart, hfinalOther, hfinalOutput⟩ :=
            ih (lhsTail.length + rhsTail.length) htailLength nextCarry lhsTail
              rhsTail (emitted ++ [sum]) inp₀ work₁ out₀ hlhs₁ hrhs₁
              hresult₁ hresultStart₁ hinput hother₁ houtput rfl
          refine ⟨c', ?_, hhalt, hfinalInput, ?_, ?_, ?_, ?_, ?_,
            hfinalResultStart, ?_, hfinalOutput⟩
          · simpa [binaryRippleAddScanTime, Nat.succ_max_succ] using
              TM.reachesIn.step hstep hreach
          · simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.lhs_result, hlhsNotBlank, Tape.move_cells] using
              hfinalLhs
          · rw [hfinalLhsHead]
            simp only [work₁, binaryRippleAddScanAdvanceWork,
              ite_eq_right hdistinct.lhs_result, ite_eq_left, ite_eq_right hlhsNotBlank,
              Tape.move, List.length_cons]
            omega
          · simpa [work₁, binaryRippleAddScanAdvanceWork,
              hdistinct.rhs_result, Ne.symm hdistinct.lhs_rhs,
              hrhsNotBlank, Tape.move_cells] using hfinalRhs
          · rw [hfinalRhsHead]
            simp only [work₁, binaryRippleAddScanAdvanceWork,
              ite_eq_right hdistinct.rhs_result,
              ite_eq_right (Ne.symm hdistinct.lhs_rhs), ite_eq_left,
              ite_eq_right hrhsNotBlank, Tape.move, List.length_cons]
            omega
          · simpa [BinaryRippleAdd.ripple, sum, nextCarry,
              List.append_assoc] using hfinalResult
          · intro i hil hir hires
            rw [hfinalOther i hil hir hires]
            simp [work₁, binaryRippleAddScanAdvanceWork, hil, hir, hires]

theorem binaryRippleAddScanTM_reachesIn_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
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
    ∃ c',
      (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).reachesIn
        (binaryRippleAddScanTime lhs rhs)
        { state := (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work lhsIdx).cells = (work₀ lhsIdx).cells ∧
      (c'.work lhsIdx).head = lhs.length + 1 ∧
      (c'.work rhsIdx).cells = (work₀ rhsIdx).cells ∧
      (c'.work rhsIdx).head = rhs.length + 1 ∧
      (c'.work resultIdx).HasBinaryPrefix
        (BinaryRippleAdd.ripple false lhs rhs) ∧
      (c'.work resultIdx).cells 0 = Γ.start ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  obtain ⟨c', hreach, hhalt, hfinalInput, hfinalLhs, hfinalLhsHead,
      hfinalRhs, hfinalRhsHead, hfinalResult, hfinalResultStart,
      hfinalOther, hfinalOutput⟩ :=
    binaryRippleAddScanTM_suffix_reachesIn lhsIdx rhsIdx resultIdx hdistinct
      false lhs rhs [] inp₀ work₀ out₀ hlhs.hasBinarySuffix
      hrhs.hasBinarySuffix hresult hresultStart hinput hother houtput
  refine ⟨c', hreach, hhalt, hfinalInput, hfinalLhs, ?_, hfinalRhs, ?_, ?_,
    hfinalResultStart, hfinalOther, hfinalOutput⟩
  · simpa [hlhs.1, Nat.add_comm] using hfinalLhsHead
  · simpa [hrhs.1, Nat.add_comm] using hfinalRhsHead
  · simpa using hfinalResult

end TM

end Complexity
