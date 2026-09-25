/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# Structured logarithmic-cost RAM programs — proof internals

This file proves that absolute-jump lowering preserves the independent source
semantics exactly: final registers, logarithmic cost, and peak register space.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace Cmd

theorem length_compileAt (cmd : Cmd) (start : ℕ) :
    (cmd.compileAt start).length = cmd.codeSize := by
  induction cmd generalizing start with
  | skip => rfl
  | basic op => rfl
  | seq first second ihFirst ihSecond =>
      simp only [compileAt, List.length_append, ihFirst, ihSecond, codeSize]
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      simp only [compileAt, List.length_append, List.length_cons, List.length_nil,
        ihZero, ihNonzero, codeSize]
      omega
  | whileNonzero test body ih =>
      simp only [compileAt, List.length_append, List.length_cons, List.length_nil,
        ih, codeSize]
      omega

end Cmd

private theorem curInstr_append_head (pre suffix : Program) (instr : Instr)
    (regs : Store) :
    curInstr (pre ++ instr :: suffix) { pc := pre.length, regs := regs } = instr := by
  simp [curInstr]

private theorem not_halted_append_head (pre suffix : Program) (op : Basic)
    (regs : Store) :
    ¬Halted (pre ++ op.instr :: suffix) { pc := pre.length, regs := regs } := by
  simp [Halted, curInstr_append_head]
  cases op <;> simp [Basic.instr]

private theorem not_halted_jz (pre suffix : Program) (test target : ℕ)
    (regs : Store) :
    ¬Halted (pre ++ Instr.jz test target :: suffix)
      { pc := pre.length, regs := regs } := by
  simp [Halted, curInstr_append_head]

private theorem not_halted_jmp (pre suffix : Program) (target : ℕ)
    (regs : Store) :
    ¬Halted (pre ++ Instr.jmp target :: suffix)
      { pc := pre.length, regs := regs } := by
  simp [Halted, curInstr_append_head]

private theorem cfg_space_eq_store_space (pc : ℕ) (regs : Store) :
    (Cfg.mk pc regs).space = regs.space := rfl

private theorem step_basic (pre suffix : Program) (op : Basic) (regs : Store) :
    step (pre ++ op.instr :: suffix) { pc := pre.length, regs := regs } =
      { pc := pre.length + 1, regs := op.exec regs } := by
  unfold step
  rw [curInstr_append_head]
  cases op <;> simp [Basic.instr, Basic.exec, stepInstr]

private theorem step_jz_zero (pre suffix : Program) (test target : ℕ)
    (regs : Store) (htest : regs test = 0) :
    step (pre ++ Instr.jz test target :: suffix)
        { pc := pre.length, regs := regs } =
      { pc := target, regs := regs } := by
  unfold step
  rw [curInstr_append_head]
  simp [stepInstr, htest]

private theorem step_jz_nonzero (pre suffix : Program) (test target : ℕ)
    (regs : Store) (htest : regs test ≠ 0) :
    step (pre ++ Instr.jz test target :: suffix)
        { pc := pre.length, regs := regs } =
      { pc := pre.length + 1, regs := regs } := by
  unfold step
  rw [curInstr_append_head]
  simp [stepInstr, htest]

private theorem step_jmp (pre suffix : Program) (target : ℕ) (regs : Store) :
    step (pre ++ Instr.jmp target :: suffix)
        { pc := pre.length, regs := regs } =
      { pc := target, regs := regs } := by
  unfold step
  rw [curInstr_append_head]
  rfl

private theorem space_le_spaceUpto (P : Program) (fuel : ℕ) (cfg : Cfg) :
    cfg.space ≤ spaceUpto P fuel cfg := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [spaceUpto]
      split
      · rfl
      · exact le_max_left _ _

private theorem spaceUpto_halted (P : Program) {cfg : Cfg}
    (hhalt : Halted P cfg) (fuel : ℕ) : spaceUpto P fuel cfg = cfg.space := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [spaceUpto, hhalt]

private theorem spaceUpto_add (P : Program) (first second : ℕ) (cfg : Cfg) :
    spaceUpto P (first + second) cfg =
      max (spaceUpto P first cfg) (spaceUpto P second (run P first cfg)) := by
  induction first generalizing cfg with
  | zero =>
      simp only [Nat.zero_add, spaceUpto, run_zero]
      exact (max_eq_right (space_le_spaceUpto P second cfg)).symm
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [spaceUpto, run_succ]
      by_cases hhalt : Halted P cfg
      · simp [hhalt, spaceUpto_halted P hhalt]
      · simp only [ite_eq_right hhalt, ih]
        omega

private theorem run_space_le_spaceUpto (P : Program) (fuel : ℕ) (cfg : Cfg) :
    (run P fuel cfg).space ≤ spaceUpto P fuel cfg := by
  have hsplit := spaceUpto_add P fuel 0 cfg
  simp only [Nat.add_zero, spaceUpto] at hsplit
  calc
    (run P fuel cfg).space ≤
        max (spaceUpto P fuel cfg) (run P fuel cfg).space := le_max_right _ _
    _ = spaceUpto P fuel cfg := hsplit.symm

/-- Compilation preserves the nonzero conditional branch, including its exit jump cost. -/
private theorem compileAt_ifNonzero_correct
    {test : ℕ} {onZero onNonzero : Cmd} {store final : Store}
    {branchSteps branchCost branchSpace : ℕ}
    (htest : store test ≠ 0)
    (ih : ∀ (pre suffix : Program),
      let P := pre ++ onNonzero.compileAt pre.length ++ suffix
      let start : Cfg := { pc := pre.length, regs := store }
      run P branchSteps start =
          { pc := pre.length + onNonzero.codeSize, regs := final } ∧
        logTimeUpto P branchSteps start = branchCost ∧
        spaceUpto P branchSteps start = branchSpace)
    (pre suffix : Program) :
    let cmd := Cmd.ifZero test onZero onNonzero
    let P := pre ++ cmd.compileAt pre.length ++ suffix
    let start : Cfg := { pc := pre.length, regs := store }
    run P (branchSteps + 2) start =
        { pc := pre.length + cmd.codeSize, regs := final } ∧
      logTimeUpto P (branchSteps + 2) start =
        bitlen (store test) + 1 + branchCost + 1 ∧
      spaceUpto P (branchSteps + 2) start = max store.space branchSpace := by
  dsimp only
  simp only [Cmd.compileAt, Cmd.codeSize]
  let zeroStart := pre.length + 1 + onNonzero.codeSize + 1
  let done := pre.length + (2 + onZero.codeSize + onNonzero.codeSize)
  let nonzeroPre := pre ++ [Instr.jz test zeroStart]
  have hNonzeroPre : nonzeroPre.length = pre.length + 1 := by
    simp [nonzeroPre]
  have hbranchRun := ih nonzeroPre
    (Instr.jmp done :: onZero.compileAt zeroStart ++ suffix)
  simp only [hNonzeroPre] at hbranchRun
  dsimp only [nonzeroPre, zeroStart, done] at hbranchRun ⊢
  simp only [List.nil_append, List.cons_append, List.append_assoc]
    at hbranchRun ⊢
  let jmpPre := pre ++
    [Instr.jz test (pre.length + 1 + onNonzero.codeSize + 1)] ++
    onNonzero.compileAt (pre.length + 1)
  have hjmp := step_jmp jmpPre
    (onZero.compileAt (pre.length + 1 + onNonzero.codeSize + 1) ++ suffix)
    (pre.length + (2 + onZero.codeSize + onNonzero.codeSize)) final
  dsimp only [jmpPre] at hjmp
  have hjmp' :
      step
          (pre ++ Instr.jz test (pre.length + 1 + onNonzero.codeSize + 1) ::
            (onNonzero.compileAt (pre.length + 1) ++
              Instr.jmp (pre.length + (2 + onZero.codeSize + onNonzero.codeSize)) ::
                (onZero.compileAt (pre.length + 1 + onNonzero.codeSize + 1) ++ suffix)))
          { pc := pre.length + 1 + onNonzero.codeSize, regs := final } =
        { pc := pre.length + (2 + onZero.codeSize + onNonzero.codeSize),
          regs := final } := by
    simpa [Cmd.length_compileAt, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hjmp
  have hjmpInstr := curInstr_append_head jmpPre
    (onZero.compileAt (pre.length + 1 + onNonzero.codeSize + 1) ++ suffix)
    (Instr.jmp (pre.length + (2 + onZero.codeSize + onNonzero.codeSize))) final
  dsimp only [jmpPre] at hjmpInstr
  have hjmpInstr' :
      curInstr
          (pre ++ Instr.jz test (pre.length + 1 + onNonzero.codeSize + 1) ::
            (onNonzero.compileAt (pre.length + 1) ++
              Instr.jmp (pre.length + (2 + onZero.codeSize + onNonzero.codeSize)) ::
                (onZero.compileAt (pre.length + 1 + onNonzero.codeSize + 1) ++ suffix)))
          { pc := pre.length + 1 + onNonzero.codeSize, regs := final } =
        Instr.jmp (pre.length + (2 + onZero.codeSize + onNonzero.codeSize)) := by
    simpa [Cmd.length_compileAt, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hjmpInstr
  have hjmpHalt :
      ¬Halted
          (pre ++ Instr.jz test (pre.length + 1 + onNonzero.codeSize + 1) ::
            (onNonzero.compileAt (pre.length + 1) ++
              Instr.jmp (pre.length + (2 + onZero.codeSize + onNonzero.codeSize)) ::
                (onZero.compileAt (pre.length + 1 + onNonzero.codeSize + 1) ++ suffix)))
          { pc := pre.length + 1 + onNonzero.codeSize, regs := final } := by
    simp [Halted, hjmpInstr']
  rw [run_succ, logTimeUpto_succ]
  simp [Halted, curInstr]
  rw [step_jz_nonzero pre _ test _ store htest]
  rw [run_succ_step, hbranchRun.1]
  rw [hjmp']
  rw [logTimeUpto_add _ branchSteps 1]
  rw [hbranchRun.2.1, hbranchRun.1]
  rw [show (1 : ℕ) = 0 + 1 from rfl, logTimeUpto_succ]
  rw [ite_eq_right hjmpHalt]
  simp [stepLogCost, hjmpInstr', Instr.logCost]
  rw [spaceUpto]
  simp [Halted, curInstr]
  rw [step_jz_nonzero pre _ test _ store htest]
  rw [spaceUpto_add _ branchSteps 1, hbranchRun.2.2, hbranchRun.1]
  rw [show (1 : ℕ) = 0 + 1 from rfl, spaceUpto]
  rw [ite_eq_right hjmpHalt, hjmp']
  simp only [spaceUpto]
  have hfinalSpace : final.space ≤ branchSpace := by
    have hrunSpace := run_space_le_spaceUpto
      (pre ++ Instr.jz test (pre.length + 1 + onNonzero.codeSize + 1) ::
        (onNonzero.compileAt (pre.length + 1) ++
          Instr.jmp (pre.length + (2 + onZero.codeSize + onNonzero.codeSize)) ::
            (onZero.compileAt (pre.length + 1 + onNonzero.codeSize + 1) ++ suffix)))
      branchSteps { pc := pre.length + 1, regs := store }
    rw [hbranchRun.1, hbranchRun.2.2] at hrunSpace
    simpa [Store.space, Cfg.space] using hrunSpace
  constructor
  · omega
  · change max store.space (max branchSpace (max final.space final.space)) =
      max store.space branchSpace
    rw [max_self, max_eq_left hfinalSpace]

theorem compileAt_correct_internal
    {cmd : Cmd} {initial final : Store} {steps cost space : ℕ}
    (hexec : Exec cmd initial final steps cost space)
    (pre suffix : Program) :
    let P := pre ++ cmd.compileAt pre.length ++ suffix
    let start : Cfg := { pc := pre.length, regs := initial }
    run P steps start =
        { pc := pre.length + cmd.codeSize, regs := final } ∧
      logTimeUpto P steps start = cost ∧
      spaceUpto P steps start = space := by
  dsimp only
  induction hexec generalizing pre suffix with
  | skip store =>
      simp [Cmd.compileAt, Cmd.codeSize, spaceUpto, Store.space, Cfg.space]
  | basic op store =>
      simp only [Cmd.compileAt, Cmd.codeSize, List.singleton_append,
        List.append_assoc]
      have hhalt := not_halted_append_head pre suffix op store
      rw [run_one, step_basic]
      constructor
      · rfl
      constructor
      · simp [logTimeUpto, hhalt, Basic.logCost, stepLogCost,
          curInstr_append_head]
        cases op <;> rfl
      · simp [spaceUpto, hhalt, step_basic, Store.space, Cfg.space]
  | seq hfirst hsecond ihFirst ihSecond =>
      rename_i firstCmd secondCmd store middle final firstSteps secondSteps firstCost
        secondCost firstSpace secondSpace
      simp only [Cmd.compileAt, Cmd.codeSize]
      let secondPre := pre ++ Cmd.compileAt pre.length firstCmd
      have hSecondPre : secondPre.length = pre.length + firstCmd.codeSize := by
        simp [secondPre, Cmd.length_compileAt]
      have hfirstRun :=
        ihFirst pre (Cmd.compileAt (pre.length + firstCmd.codeSize) secondCmd ++ suffix)
      have hsecondRun := ihSecond secondPre suffix
      simp only [secondPre, hSecondPre] at hsecondRun
      simp only [List.append_assoc] at hfirstRun hsecondRun ⊢
      rw [run_add, logTimeUpto_add, spaceUpto_add]
      rw [hfirstRun.1, hfirstRun.2.1, hfirstRun.2.2]
      rw [hsecondRun.1, hsecondRun.2.1, hsecondRun.2.2]
      simp [Nat.add_assoc]
  | ifZero htest hbranch ih =>
      rename_i test onZero onNonzero store final branchSteps branchCost branchSpace
      simp only [Cmd.compileAt, Cmd.codeSize]
      let zeroStart := pre.length + 1 + onNonzero.codeSize + 1
      let done := pre.length + (2 + onZero.codeSize + onNonzero.codeSize)
      let zeroPre := pre ++ [Instr.jz test zeroStart] ++
        onNonzero.compileAt (pre.length + 1) ++ [Instr.jmp done]
      have hZeroPre : zeroPre.length = zeroStart := by
        simp [zeroPre, zeroStart, Cmd.length_compileAt]
        omega
      have hbranchRun := ih zeroPre suffix
      simp only [hZeroPre] at hbranchRun
      dsimp only [zeroPre, zeroStart, done] at hbranchRun ⊢
      simp only [List.nil_append, List.cons_append, List.append_assoc]
        at hbranchRun ⊢
      rw [run_succ, logTimeUpto_succ]
      simp [Halted, curInstr]
      rw [step_jz_zero pre _ test _ store htest]
      rw [spaceUpto]
      simp [Halted, curInstr]
      rw [step_jz_zero pre _ test _ store htest]
      rw [hbranchRun.1, hbranchRun.2.1, hbranchRun.2.2]
      simp [stepLogCost, curInstr_append_head, Instr.logCost, Store.space,
        Cfg.space, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega
  | ifNonzero htest hbranch ih =>
      exact compileAt_ifNonzero_correct htest ih pre suffix
  | whileZero htest =>
      rename_i test body store
      simp only [Cmd.compileAt, Cmd.codeSize, List.cons_append, List.append_assoc]
      rw [run_one]
      rw [step_jz_zero pre _ test _ store htest]
      constructor
      · rfl
      constructor
      · simp [logTimeUpto, Halted, curInstr, stepLogCost, Instr.logCost,
          Nat.add_comm]
      · simp [spaceUpto, Halted, curInstr,
          step_jz_zero pre _ test _ store htest, Store.space, Cfg.space]
  | whileNonzero htest hbody hloop ihBody ihLoop =>
      rename_i test body store middle final bodySteps loopSteps bodyCost loopCost
        bodySpace loopSpace
      simp only [Cmd.compileAt, Cmd.codeSize]
      let done := pre.length + (body.codeSize + 2)
      let bodyPre := pre ++ [Instr.jz test done]
      have hBodyPre : bodyPre.length = pre.length + 1 := by
        simp [bodyPre]
      have hbodyRun := ihBody bodyPre (Instr.jmp pre.length :: suffix)
      simp only [hBodyPre] at hbodyRun
      have hloopRun := ihLoop pre suffix
      simp only [Cmd.compileAt, Cmd.codeSize] at hloopRun
      dsimp only [bodyPre, done] at hbodyRun hloopRun ⊢
      simp only [List.nil_append, List.cons_append, List.append_assoc]
        at hbodyRun hloopRun ⊢
      let jmpPre := pre ++ [Instr.jz test (pre.length + (body.codeSize + 2))] ++
        body.compileAt (pre.length + 1)
      have hjmp := step_jmp jmpPre suffix pre.length middle
      dsimp only [jmpPre] at hjmp
      have hjmp' :
          step
              (pre ++ Instr.jz test (pre.length + (body.codeSize + 2)) ::
                (body.compileAt (pre.length + 1) ++ Instr.jmp pre.length :: suffix))
              { pc := pre.length + 1 + body.codeSize, regs := middle } =
            { pc := pre.length, regs := middle } := by
        simpa [Cmd.length_compileAt, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hjmp
      have hjmpInstr := curInstr_append_head jmpPre suffix
        (Instr.jmp pre.length) middle
      dsimp only [jmpPre] at hjmpInstr
      have hjmpInstr' :
          curInstr
              (pre ++ Instr.jz test (pre.length + (body.codeSize + 2)) ::
                (body.compileAt (pre.length + 1) ++ Instr.jmp pre.length :: suffix))
              { pc := pre.length + 1 + body.codeSize, regs := middle } =
            Instr.jmp pre.length := by
        simpa [Cmd.length_compileAt, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hjmpInstr
      have hjmpHalt :
          ¬Halted
              (pre ++ Instr.jz test (pre.length + (body.codeSize + 2)) ::
                (body.compileAt (pre.length + 1) ++ Instr.jmp pre.length :: suffix))
              { pc := pre.length + 1 + body.codeSize, regs := middle } := by
        simp [Halted, hjmpInstr']
      rw [run_succ, logTimeUpto_succ]
      simp [Halted, curInstr]
      rw [step_jz_nonzero pre _ test _ store htest]
      rw [show bodySteps + loopSteps + 1 = bodySteps + (loopSteps + 1) by omega]
      rw [run_add, hbodyRun.1]
      rw [run_succ]
      simp only [ite_eq_right hjmpHalt]
      rw [hjmp', hloopRun.1]
      rw [logTimeUpto_add _ bodySteps (loopSteps + 1)]
      rw [hbodyRun.2.1, hbodyRun.1]
      rw [logTimeUpto_succ, ite_eq_right hjmpHalt]
      rw [hjmp', hloopRun.2.1]
      simp [stepLogCost, hjmpInstr', Instr.logCost]
      rw [spaceUpto]
      simp [Halted, curInstr]
      rw [step_jz_nonzero pre _ test _ store htest]
      rw [show bodySteps + loopSteps + 1 = bodySteps + (loopSteps + 1) by omega]
      rw [spaceUpto_add _ bodySteps (loopSteps + 1)]
      rw [hbodyRun.2.2, hbodyRun.1]
      rw [spaceUpto, ite_eq_right hjmpHalt, hjmp', hloopRun.2.2]
      have hinitialSpace : store.space ≤ bodySpace := by
        have hstart := space_le_spaceUpto
          (pre ++ Instr.jz test (pre.length + (body.codeSize + 2)) ::
            (body.compileAt (pre.length + 1) ++ Instr.jmp pre.length :: suffix))
          bodySteps { pc := pre.length + 1, regs := store }
        rw [hbodyRun.2.2] at hstart
        simpa [Store.space, Cfg.space] using hstart
      have hmiddleSpace : middle.space ≤ bodySpace := by
        have hend := run_space_le_spaceUpto
          (pre ++ Instr.jz test (pre.length + (body.codeSize + 2)) ::
            (body.compileAt (pre.length + 1) ++ Instr.jmp pre.length :: suffix))
          bodySteps { pc := pre.length + 1, regs := store }
        rw [hbodyRun.1, hbodyRun.2.2] at hend
        simpa [Store.space, Cfg.space] using hend
      constructor
      · omega
      · change max store.space (max bodySpace (max middle.space loopSpace)) =
          max bodySpace loopSpace
        rw [max_eq_right (hinitialSpace.trans (le_max_left _ _)), ← max_assoc,
          max_eq_left hmiddleSpace]

end Structured

end RAM

end Complexity
