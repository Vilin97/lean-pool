/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryEq.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Binary work-tape equality — proof internals
-/


@[expose] public section

namespace Complexity

namespace TM

private def binaryEqResultWork {n : ℕ} (resultIdx : Fin n)
    (work : Fin n → Tape) (result : Bool) : Fin n → Tape :=
  Function.update work resultIdx
    ((work resultIdx).writeAndMove (Γw.ofBool result) Dir3.right)

private def binaryEqAdvanceWork {n : ℕ} (lhsIdx rhsIdx : Fin n)
    (work : Fin n → Tape) : Fin n → Tape :=
  fun i => if i = lhsIdx then (work i).move Dir3.right
    else if i = rhsIdx then (work i).move Dir3.right else work i

private def binaryEqResultCfg {n : ℕ} (resultIdx : Fin n)
    (result : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape) :
    Cfg n BinaryEqPhase where
  state := .done
  input := inp
  work := binaryEqResultWork resultIdx work result
  output := out

private def binaryEqAdvanceCfg {n : ℕ} (lhsIdx rhsIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) : Cfg n BinaryEqPhase where
  state := .scan
  input := inp
  work := binaryEqAdvanceWork lhsIdx rhsIdx work
  output := out

private theorem writeAndMove_readBack_right {tape : Tape}
    (hread : tape.read ≠ Γ.start) :
    tape.writeAndMove (readBackWrite tape.read) Dir3.right =
      tape.move Dir3.right := by
  cases tape with
  | mk head cells =>
      simp only [Tape.writeAndMove, Tape.read] at hread ⊢
      rw [toΓ_readBackWrite_of_ne_start hread]
      simp [Tape.write, Tape.move, Function.update_eq_self]

private theorem binaryEq_terminal_step {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) (result : Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hterminal : if result then
      (work lhsIdx).read = Γ.blank ∧ (work rhsIdx).read = Γ.blank
      else ¬((work lhsIdx).read = (work rhsIdx).read))
    (hinput : inp.read ≠ Γ.start)
    (hwork : ∀ i, i ≠ resultIdx → (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).step
      { state := .scan, input := inp, work := work, output := out } =
      some (binaryEqResultCfg resultIdx result inp work out) := by
  simp only [TM.step, binaryEqTM]
  cases result with
  | false =>
      simp only [Bool.false_eq_true, ite_false] at hterminal
      have hnotBlank : ¬((work lhsIdx).read = Γ.blank ∧
          (work rhsIdx).read = Γ.blank) := by
        intro hblank
        exact hterminal (hblank.1.trans hblank.2.symm)
      rw [ite_eq_right hnotBlank, ite_eq_right hterminal]
      simp only [show BinaryEqPhase.scan ≠ BinaryEqPhase.done by decide,
        ite_false]
      refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
        (transitionTape_eq_self houtput))
      funext i
      by_cases hi : i = resultIdx
      · subst i
        simp [binaryEqResultCfg, binaryEqResultWork, Γw.ofBool]
      · simpa [binaryEqResultCfg, binaryEqResultWork, hi] using!
          transitionTape_eq_self (hwork i hi)

  | true =>
      simp only [if_true] at hterminal
      rw [ite_eq_left hterminal]
      simp only [show BinaryEqPhase.scan ≠ BinaryEqPhase.done by decide,
        ite_false]
      refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
        (transitionTape_eq_self houtput))
      funext i
      by_cases hi : i = resultIdx
      · subst i
        simp [binaryEqResultCfg, binaryEqResultWork, Γw.ofBool]
      · simpa [binaryEqResultCfg, binaryEqResultWork, hi] using!
          transitionTape_eq_self (hwork i hi)

private theorem binaryEq_scan_step {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hreadEq : (work lhsIdx).read = (work rhsIdx).read)
    (hnotBlank : ¬((work lhsIdx).read = Γ.blank ∧
      (work rhsIdx).read = Γ.blank))
    (hinput : inp.read ≠ Γ.start)
    (hwork : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).step
      { state := .scan, input := inp, work := work, output := out } =
    some (binaryEqAdvanceCfg lhsIdx rhsIdx inp work out) := by
  simp only [TM.step, binaryEqTM]
  rw [ite_eq_right hnotBlank, ite_eq_left hreadEq]
  simp only [show BinaryEqPhase.scan ≠ BinaryEqPhase.done by decide, ite_false]
  refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
    (transitionTape_eq_self houtput))
  funext i
  by_cases hil : i = lhsIdx
  · subst i
    simp only [binaryEqAdvanceCfg, binaryEqAdvanceWork, ite_eq_left]
    exact writeAndMove_readBack_right (hwork lhsIdx)
  · by_cases hir : i = rhsIdx
    · subst i
      simp only [binaryEqAdvanceCfg, binaryEqAdvanceWork, ite_eq_right hil, ite_eq_left]
      exact writeAndMove_readBack_right (hwork rhsIdx)
    · simpa [binaryEqAdvanceCfg, binaryEqAdvanceWork, hil, hir] using!
        transitionTape_eq_self (hwork i)

private theorem binaryEq_terminal_reachesIn {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool) (result : Bool)
    (hdecision : decide (lhs = rhs) = result)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinarySuffix lhs)
    (hrhs : (work₀ rhsIdx).HasBinarySuffix rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hterminal : if result then
      (work₀ lhsIdx).read = Γ.blank ∧ (work₀ rhsIdx).read = Γ.blank
      else ¬((work₀ lhsIdx).read = (work₀ rhsIdx).read))
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c' t,
      t ≤ binaryEqTime lhs rhs ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).reachesIn t
        { state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
      (c'.work lhsIdx).cells = (work₀ lhsIdx).cells ∧
      (c'.work rhsIdx).cells = (work₀ rhsIdx).cells ∧
      1 ≤ (c'.work lhsIdx).head ∧
      1 ≤ (c'.work rhsIdx).head ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  have hwork : ∀ i, i ≠ resultIdx → (work₀ i).read ≠ Γ.start := by
    intro i hir
    by_cases hil : i = lhsIdx
    · subst i
      exact hlhs.read_ne_start
    · by_cases hirhs : i = rhsIdx
      · subst i
        exact hrhs.read_ne_start
      · exact hother i hil hirhs hir
  have hstep := binaryEq_terminal_step lhsIdx rhsIdx resultIdx result
    inp₀ work₀ out₀ hterminal hinput hwork houtput
  let c' := binaryEqResultCfg resultIdx result inp₀ work₀ out₀
  refine ⟨c', 1, by simp [binaryEqTime], .step hstep .zero, rfl, rfl, ?_, ?_,
    ?_, ?_, ?_, ?_, rfl⟩
  · rw [hdecision]
    cases result with
    | false =>
        simpa [Γ.ofBool, transitionTape, Γw.toΓ, c', binaryEqResultCfg, binaryEqResultWork, Γw.ofBool] using
          Tape.hasBinaryPrefix_write_bit false hresult
    | true =>
        simpa [Γ.ofBool, transitionTape, Γw.toΓ, c', binaryEqResultCfg, binaryEqResultWork, Γw.ofBool] using
          Tape.hasBinaryPrefix_write_bit true hresult
  · change (Function.update work₀ resultIdx _ lhsIdx).cells = _
    rw [Function.update_of_ne hdistinct.lhs_result]
  · change (Function.update work₀ resultIdx _ rhsIdx).cells = _
    rw [Function.update_of_ne hdistinct.rhs_result]
  · change 1 ≤ (Function.update work₀ resultIdx _ lhsIdx).head
    rw [Function.update_of_ne hdistinct.lhs_result]
    exact hlhs.1
  · change 1 ≤ (Function.update work₀ resultIdx _ rhsIdx).head
    rw [Function.update_of_ne hdistinct.rhs_result]
    exact hrhs.1
  · intro i hil hirhs hir
    simp [c', binaryEqResultCfg, binaryEqResultWork, hir]

private theorem binaryEq_suffix_reachesIn {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinarySuffix lhs)
    (hrhs : (work₀ rhsIdx).HasBinarySuffix rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c' t,
      t ≤ binaryEqTime lhs rhs ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).reachesIn t
        { state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
      (c'.work lhsIdx).cells = (work₀ lhsIdx).cells ∧
      (c'.work rhsIdx).cells = (work₀ rhsIdx).cells ∧
      1 ≤ (c'.work lhsIdx).head ∧
      1 ≤ (c'.work rhsIdx).head ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  induction lhs generalizing rhs inp₀ work₀ out₀ with
  | nil =>
      cases rhs with
      | nil =>
          apply binaryEq_terminal_reachesIn lhsIdx rhsIdx resultIdx hdistinct
            [] [] true (by simp) inp₀ work₀ out₀ hlhs hrhs hresult
          · simp [hlhs.read_nil, hrhs.read_nil]
          · exact hinput
          · exact hother
          · exact houtput
      | cons rhsBit rhsTail =>
          apply binaryEq_terminal_reachesIn lhsIdx rhsIdx resultIdx hdistinct
            [] (rhsBit :: rhsTail) false (by simp) inp₀ work₀ out₀ hlhs hrhs
            hresult
          · rw [hlhs.read_nil, hrhs.read_cons]
            cases rhsBit <;> decide
          · exact hinput
          · exact hother
          · exact houtput
  | cons lhsBit lhsTail ih =>
      cases rhs with
      | nil =>
          apply binaryEq_terminal_reachesIn lhsIdx rhsIdx resultIdx hdistinct
            (lhsBit :: lhsTail) [] false (by simp) inp₀ work₀ out₀ hlhs hrhs
            hresult
          · rw [hlhs.read_cons, hrhs.read_nil]
            cases lhsBit <;> decide
          · exact hinput
          · exact hother
          · exact houtput
      | cons rhsBit rhsTail =>
          by_cases hbit : lhsBit = rhsBit
          · subst rhsBit
            have hworkRead : ∀ i, (work₀ i).read ≠ Γ.start := by
              intro i
              by_cases hil : i = lhsIdx
              · subst i
                exact hlhs.read_ne_start
              · by_cases hir : i = rhsIdx
                · subst i
                  exact hrhs.read_ne_start
                · by_cases hires : i = resultIdx
                  · subst i
                    rw [hresult.read_blank]
                    decide
                  · exact hother i hil hir hires
            have hreadEq : (work₀ lhsIdx).read = (work₀ rhsIdx).read := by
              rw [hlhs.read_cons, hrhs.read_cons]
            have hnotBlank : ¬((work₀ lhsIdx).read = Γ.blank ∧
                (work₀ rhsIdx).read = Γ.blank) := by
              intro hblank
              rw [hlhs.read_cons] at hblank
              cases lhsBit <;> simp [Γ.ofBool] at hblank
            have hstep := binaryEq_scan_step lhsIdx rhsIdx resultIdx inp₀ work₀
              out₀ hreadEq hnotBlank hinput hworkRead houtput
            let work₁ := binaryEqAdvanceWork lhsIdx rhsIdx work₀
            have hlhs₁ : (work₁ lhsIdx).HasBinarySuffix lhsTail := by
              simpa [work₁, binaryEqAdvanceWork] using hlhs.move_right_cons
            have hrhs₁ : (work₁ rhsIdx).HasBinarySuffix rhsTail := by
              simp only [work₁, binaryEqAdvanceWork,
                ite_eq_right (Ne.symm hdistinct.lhs_rhs), ite_eq_left]
              exact hrhs.move_right_cons
            have hresult₁ : (work₁ resultIdx).HasBinaryPrefix [] := by
              simpa [work₁, binaryEqAdvanceWork,
                Ne.symm hdistinct.lhs_result,
                Ne.symm hdistinct.rhs_result] using hresult
            have hother₁ : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
                (work₁ i).read ≠ Γ.start := by
              intro i hil hir hires
              simpa [work₁, binaryEqAdvanceWork, hil, hir] using
                hother i hil hir hires
            obtain ⟨c', t, htime, hreach, hhalt, hfinalInput, hfinalResult,
                hfinalLhs, hfinalRhs, hfinalLhsHead, hfinalRhsHead,
                hfinalOther, hfinalOutput⟩ :=
              ih rhsTail inp₀ work₁ out₀ hlhs₁ hrhs₁ hresult₁ hinput hother₁
                houtput
            have hreach' : (binaryEqTM lhsIdx rhsIdx resultIdx).reachesIn (t + 1)
                { state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart
                  input := inp₀
                  work := work₀
                  output := out₀ } c' := by
              exact .step hstep (by
                simpa [Γ.ofBool, transitionTape, Γw.toΓ, work₁, binaryEqAdvanceCfg] using! hreach)
            refine ⟨c', t + 1, ?_, hreach', hhalt, hfinalInput, ?_, ?_, ?_,
              hfinalLhsHead, hfinalRhsHead, ?_, hfinalOutput⟩
            · simp only [binaryEqTime, List.length_cons] at htime ⊢
              omega
            · simpa using hfinalResult
            · simpa [work₁, binaryEqAdvanceWork, Tape.move_cells] using hfinalLhs
            · simpa [work₁, binaryEqAdvanceWork, Tape.move_cells,
                Ne.symm hdistinct.lhs_rhs] using hfinalRhs
            · intro i hil hir hires
              simpa [work₁, binaryEqAdvanceWork, hil, hir] using
                hfinalOther i hil hir hires
          · apply binaryEq_terminal_reachesIn lhsIdx rhsIdx resultIdx hdistinct
              (lhsBit :: lhsTail) (rhsBit :: rhsTail) false (by simp [hbit])
              inp₀ work₀ out₀ hlhs hrhs hresult
            · rw [hlhs.read_cons, hrhs.read_cons]
              intro heq
              cases lhsBit <;> cases rhsBit <;> simp_all [Γ.ofBool]
            · exact hinput
            · exact hother
            · exact houtput

theorem binaryEqTM_reachesIn_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c' t,
      t ≤ binaryEqTime lhs rhs ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).reachesIn t
        { state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
      (c'.work lhsIdx).HasBinaryContent lhs ∧
      1 ≤ (c'.work lhsIdx).head ∧
      (c'.work rhsIdx).HasBinaryContent rhs ∧
      1 ≤ (c'.work rhsIdx).head ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  obtain ⟨c', t, htime, hreach, hhalt, hfinalInput, hfinalResult,
      hfinalLhs, hfinalRhs, hfinalLhsHead, hfinalRhsHead, hfinalOther,
      hfinalOutput⟩ :=
    binaryEq_suffix_reachesIn lhsIdx rhsIdx resultIdx hdistinct lhs rhs
      inp₀ work₀ out₀ hlhs.hasBinarySuffix hrhs.hasBinarySuffix hresult
      hinput hother houtput
  refine ⟨c', t, htime, hreach, hhalt, hfinalInput, hfinalResult, ?_,
    hfinalLhsHead, ?_, hfinalRhsHead, hfinalOther, hfinalOutput⟩
  · simpa only [Tape.HasBinaryContent, hfinalLhs] using hlhs.hasBinaryContent
  · simpa only [Tape.HasBinaryContent, hfinalRhs] using hrhs.hasBinaryContent

theorem binaryEqTM_isTransducer_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | scan =>
      simp only [binaryEqTM]
      split
      · simp only
        simp only [idleDir]
        split <;> decide
      · split
        · simp only
          simp only [idleDir]
          split <;> decide
        · simp only
          simp only [idleDir]
          split <;> decide
  | done =>
      simp only [binaryEqTM, allIdle, idleDir]
      split <;> decide

end TM

end Complexity
