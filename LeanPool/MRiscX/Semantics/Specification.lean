/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Semantics.MsTheory
import LeanPool.MRiscX.Tactics.SpecificationTactics
import LeanPool.MRiscX.Elab.HoareElaborator
import LeanPool.MRiscX.Elab.CodeElaborator
import LeanPool.MRiscX.Delab.DelabHoare

/-!
# Specification

This module provides the per-instruction Hoare specifications.
-/
open Lean Elab Tactic

/-
Specifications
-/
/-
This file holds the specifications of each instruction introduced
in Instr.lean (excluding the panic instruction).
Additionally, its using the syntax defined in Syntax.lean.
Moreover, the Notation for the Hoare logic from the
file HoareElaborator.lean is used.

With the knowledge of this file it is clear, that the intereprete function
runOneStep works as intended. Because of this, this assembly language can be
used to write algorithms and prove their correctness.

For certifying the instruction, the rule of assignment (P ⟦x[dst] ← val; pc++⟧) is used.
The hoare triples state that if you start in a state where the precondition P holds,
and you execute the instruction, the precondition P will still
hold after the execution. The precondition is applied after simulating the
effects of the instruction.
-/
theorem specification_LoadAddress (P : Assertion) (pc dst addr : UInt64) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪la x dst, addr;⟫
    ⦃P ⟦x[dst] ← addr; pc++⟧ ∧ ¬⸨terminated⸩⦄ pc ↦ ⟨{pc+1} | L⟩ ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification

/--
Specification for `Instr.LoadImmediate`.

For certifying the instruction, the `rule of assignment` (P ⟦x[dst] ← val; pc++⟧) is used.
The hoare triples state that if you start in a state where the precondition P holds,
and you execute the instruction, the precondition P will still
hold after the execution. The precondition is applied after simulating the
effects of the instruction.
-/
theorem specification_LoadImmediate (P : Assertion) (pc dst val : UInt64) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪li x dst, val;⟫
    ⦃P ⟦x[dst] ← val; pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
    hoareSimpSpecification



theorem specification_CopyRegister (P : Assertion) (pc dst src : UInt64) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪mv x dst, x src;⟫
    ⦃P ⟦x[dst] ← x[src]; pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification

theorem specification_AddImmediate (P : Assertion) (pc dst regAddend val : UInt64)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪addi x dst, x regAddend, val;⟫
    ⦃P ⟦x[dst] ← (x[regAddend] + val); pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification

theorem specification_Increment (P : Assertion) (pc dst : UInt64) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪inc x dst;⟫
    ⦃P ⟦x[dst] ← (x[dst] + 1); pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification

theorem specification_AddRegister (P : Assertion) (pc dst regAddend1 regAddend2 : UInt64)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪add x dst, x regAddend1, x regAddend2;⟫
    ⦃P ⟦x[dst] ← (x[regAddend1] + x[regAddend2]); pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification

theorem specification_SubImmediate (P : Assertion) (pc dst regMinuend subtrahend : UInt64)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪subi x dst, x regMinuend, subtrahend;⟫
    ⦃P ⟦x[dst] ← (x[regMinuend] - subtrahend); pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification

theorem specification_Decrement (P : Assertion) (pc dst : UInt64) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪dec x dst;⟫
    ⦃P ⟦x[dst] ← (x[dst] - 1); pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification

theorem specification_SubRegister (P : Assertion) (pc dst regMinuend regSubtrahend : UInt64)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪sub x dst, x regMinuend, x regSubtrahend;⟫
    ⦃P ⟦x[dst] ← (x[regMinuend] - x[regSubtrahend]); pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification


theorem specification_XorImmediate (P : Assertion) (pc dst reg val : UInt64) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪xori x dst, x reg, val;⟫
    ⦃P ⟦x[dst] ← (x[reg] ^^^ val); pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification

theorem specification_XOR (P : Assertion) (pc dst reg1 reg2 : UInt64) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪xor x dst, x reg1, x reg2;⟫
    ⦃P ⟦x[dst] ← (x[reg1] ^^^ x[reg2]); pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification

theorem specification_LoadWordImmediate (P : Assertion) (pc dst addr : UInt64) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪lw x dst, addr;⟫
    ⦃P ⟦x[dst] ← mem[addr]; pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification


theorem specification_LoadWordReg (P : Assertion) (pc dst regWithAddr : UInt64) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪lw x dst, x regWithAddr;⟫
    ⦃P ⟦x[dst] ← mem[x[regWithAddr]]; pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification


theorem specification_StoreWordImmediate (P : Assertion) (pc regWithAddr regWithValue : UInt64)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪sw x regWithValue, x regWithAddr;⟫
    ⦃P ⟦mem[x[regWithAddr]] ← x[regWithValue]; pc++⟧ ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc+1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  hoareSimpSpecification

theorem specification_Jump (P : Assertion) (pc newPc : UInt64) (label : String) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ newPc} →
  hoare
    ⟪j label;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[label] = some newPc ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{newPc} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  intro HL
  rw [HL]
  unfold hoare_triple_up_1
  rintro _ _ state h_curr h_pc ⟨pre, h_label, h_terminated⟩
  simp only [
    Bool.not_eq_true] at h_terminated
  simp only [
    MState.get_label_from_code] at h_label
  unfold MState.currInstruction at h_curr
  exists state.runOneStep
  unfold weak
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro
    · simp
    · constructor
      · simp
      · simp only [MState.run_one_step_eq_run_n_1, Set.mem_singleton_iff, Nat.lt_one_iff, ne_eq,
          Set.singleton_union, Set.mem_insert_iff, Set.mem_setOf_eq, not_or, Decidable.not_not,
          not_and_self, imp_false, not_and]
        simp only [← MState.run_one_step_eq_run_n_1]
        unfold MState.runOneStep MState.jump
        rw [h_terminated]
        simp only [Bool.false_eq_true, ↓reduceIte, MState.currInstruction_unfold, h_curr,
          h_label, true_and]
        zeroLtNeZero
  case right =>
    simp only [Bool.not_eq_true, ne_eq, Set.mem_setOf_eq, Decidable.not_not]
    unfold MState.runOneStep MState.jump
    unfold MState.setPc at pre
    rw [h_terminated]
    rw [h_terminated] at pre
    simp [h_curr, h_label, pre]


theorem specification_Jump' (P : Assertion) (pc newPc : UInt64) (label : String) (L : Set UInt64) :
  L = {n : UInt64 | n ≠ newPc} →
  hoare
    ⟪j label;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[label] = some newPc ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{newPc} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩ ∧ ⸨pc⸩ = newPc⦄
  end := by
  intro HL
  rw [HL]
  unfold hoare_triple_up_1
  rintro h_inter h_empty state h_curr h_pc ⟨pre, h_label, h_terminated⟩
  simp only [
    Bool.not_eq_true] at h_terminated
  simp only [
    MState.get_label_from_code] at h_label
  simp only [MState.currInstruction_unfold] at h_curr
  exists state.runOneStep
  unfold weak
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro
    · simp
    · constructor
      · simp
      · simp only [MState.run_one_step_eq_run_n_1, Set.mem_singleton_iff, Nat.lt_one_iff, ne_eq,
          Set.singleton_union, Set.mem_insert_iff, Set.mem_setOf_eq, not_or, Decidable.not_not,
          not_and_self, imp_false, not_and]
        simp only [← MState.run_one_step_eq_run_n_1]
        unfold MState.runOneStep MState.jump
        rw [h_terminated]
        simp only [Bool.false_eq_true, ↓reduceIte, MState.currInstruction_unfold, h_curr,
          h_label, true_and]
        zeroLtNeZero
  case right =>
    simp only [Bool.not_eq_true, ne_eq, Set.mem_setOf_eq, Decidable.not_not]
    unfold MState.runOneStep MState.jump
    unfold MState.setPc at pre
    rw [h_terminated]
    rw [h_terminated] at pre
    simp [h_curr, h_label, pre]


theorem specification_JumpEq_true (P : Assertion) (pc newPc reg1 reg2 : UInt64) (s : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ newPc} →
  hoare
    ⟪beq x reg1, x reg2, s;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[s] = newPc ∧ x[reg1] = x[reg2] ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{newPc} | L⟩
    ⦃P ⟦⟧ ∧ labels[s] = newPc ∧ ¬⸨terminated⸩⦄
  end
  := by
  simpJumpSpec


theorem specification_JumpEq_false (P : Assertion) (pc reg1 reg2 : UInt64) (s : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪beq x reg1, x reg2, s;⟫
    ⦃P ⟦pc++⟧ ∧ x[reg1] ≠ x[reg2] ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc + 1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  simpJumpSpec


theorem specification_JumpNeq_true (P : Assertion) (pc newPc reg1 reg2 : UInt64) (s : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ newPc} →
  hoare
    ⟪bne x reg1, x reg2, s;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[s] = newPc ∧ x[reg1] ≠ x[reg2] ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{newPc} | L⟩
    ⦃P ⟦⟧ ∧ labels[s] = newPc ∧ ¬⸨terminated⸩⦄
  end
  := by
  simpJumpSpec

theorem specification_JumpNeq_false (P : Assertion) (pc reg1 reg2 : UInt64) (s : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪bne x reg1, x reg2, s;⟫
    ⦃P ⟦pc++⟧ ∧ x[reg1] = x[reg2] ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc + 1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  simpJumpSpec



theorem specification_JumpGt_true (P : Assertion) (pc newPc reg1 reg2 : UInt64) (s : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ newPc} →
  hoare
    ⟪bgt x reg1, x reg2, s;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[s] = newPc ∧ x[reg1] > x[reg2] ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{newPc} | L⟩
    ⦃P ⟦⟧ ∧ labels[s] = newPc ∧ ¬⸨terminated⸩⦄
  end
  := by
  simpJumpSpec



theorem specification_JumpGt_false (P : Assertion) (pc reg1 reg2 : UInt64) (s : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪bgt x reg1, x reg2, s;⟫
    ⦃P ⟦pc++⟧ ∧ x[reg1] ≤ x[reg2] ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc + 1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  intro HL
  rw [HL]
  unfold hoare_triple_up_1
  rintro _ _ state h_curr h_pc ⟨pre, h_cond, h_terminated⟩
  simp only [
    Bool.not_eq_true] at h_terminated
  simp only [
    MState.getRegisterAt_def] at h_cond
  simp only [MState.currInstruction_unfold] at h_curr
  have h_cond_false: (TMap.get state.registers reg2 < TMap.get state.registers reg1) ↔ false := by
    simpa only [Bool.false_eq_true, iff_false, UInt64.not_lt] using h_cond
  exists state.runOneStep
  unfold weak
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro
    · simp
    · repeat (constructor <;> try
        (simp only [MState.run_one_step_eq_run_n_1, Set.mem_singleton_iff, Nat.lt_one_iff,
          ne_eq, Set.singleton_union, Set.mem_insert_iff, Set.mem_setOf_eq, not_or,
          Decidable.not_not, not_and_self, imp_false, not_and]))
    -- . constructor; simp
      · simp only [← MState.run_one_step_eq_run_n_1]
        unfold MState.runOneStep  MState.jif' MState.jump
        rw [h_terminated, ← h_pc]
        simp [h_curr]
        simp only [h_cond_false]
        simp
      · zeroLtNeZero
  case right =>
    simp only [Bool.not_eq_true, ne_eq, Set.mem_setOf_eq, Decidable.not_not]
    unfold MState.runOneStep MState.jif' MState.jump
    rw [h_terminated]
    simp only [Bool.false_eq_true, ↓reduceIte, MState.currInstruction_unfold,
      MState.incPc_increments_pc, MState.getRegisterAt_def, gt_iff_lt, decide_eq_true_eq, h_curr]
    rw [← h_pc, h_terminated]
    simp only [h_cond_false]
    simp only [Bool.false_eq_true, ↓reduceIte, and_true]
    simp only [MState.incPc_increments_pc, h_terminated] at pre
    exact pre


theorem specification_JumpLe_true (P : Assertion) (pc newPc reg1 reg2 : UInt64) (s : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ newPc} →
  hoare
    ⟪ble x reg1, x reg2, s;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[s] = newPc ∧ x[reg1] ≤ x[reg2] ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{newPc} | L⟩
    ⦃P ⟦⟧ ∧ labels[s] = newPc ∧ ¬⸨terminated⸩⦄
  end
  := by
  simpJumpSpec


theorem specification_JumpLe_false (P : Assertion) (pc reg1 reg2 : UInt64) (s : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪ble x reg1, x reg2, s;⟫
    ⦃P ⟦pc++⟧ ∧ x[reg1] > x[reg2] ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc + 1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  intros HL
  rw [HL]
  unfold hoare_triple_up_1
  rintro _ _ state h_curr h_pc ⟨pre, h_cond, h_terminated⟩
  simp only [
    Bool.not_eq_true] at h_terminated
  simp only [
    MState.getRegisterAt_def,
    gt_iff_lt] at h_cond
  simp only [MState.currInstruction_unfold] at h_curr
  simp only [
    MState.incPc_increments_pc] at pre
  rw [← UInt64.not_le] at h_cond
  exists state.runOneStep
  unfold weak
  apply And.intro
  case left =>
    intros _
    exists 1
    apply And.intro
    · simp
    · repeat (constructor <;> try
        (simp only [MState.run_one_step_eq_run_n_1, Set.mem_singleton_iff, Nat.lt_one_iff,
          ne_eq, Set.singleton_union, Set.mem_insert_iff, Set.mem_setOf_eq, not_or,
          Decidable.not_not, not_and_self, imp_false, not_and]))
      · simp only [← MState.run_one_step_eq_run_n_1]
        unfold MState.runOneStep MState.jif' MState.jump
        rw [h_terminated, ←h_pc]
        simp [h_curr, h_cond]
      · zeroLtNeZero
  case right =>
    simp only [Bool.not_eq_true, ne_eq, Set.mem_setOf_eq, Decidable.not_not]
    unfold MState.runOneStep MState.jif' MState.jump
    rw [h_terminated, ← h_pc]
    simp only [Bool.false_eq_true, ↓reduceIte, MState.currInstruction_unfold,
      MState.incPc_increments_pc, MState.getRegisterAt_def, decide_eq_true_eq, h_curr, h_cond]
    exact ⟨⟨pre, h_terminated⟩, trivial⟩


theorem specification_JumpEqZero_true (P : Assertion) (pc newPc reg : UInt64) (label : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ newPc} →
  hoare
    ⟪beqz x reg, label;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[label] = some newPc ∧ x[reg] = 0 ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{newPc} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  simpJumpSpec




theorem specification_JumpEqZero_false (P : Assertion) (pc reg : UInt64) (label : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪beqz x reg, label;⟫
    ⦃P ⟦pc++⟧ ∧ x[reg] ≠ 0 ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc + 1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  simpJumpSpec




theorem specification_JumpNeqZero_true (P : Assertion) (pc newPc reg : UInt64) (s : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ newPc} →
  hoare
    ⟪bnez x reg, s;⟫
    ⦃P ⟦pc ← newPc⟧ ∧ labels[s] = some newPc ∧ x[reg] ≠ 0 ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{newPc} | L⟩
    ⦃P ⟦⟧⦄
  end
  := by
  simpJumpSpec



theorem specification_JumpNeqZero_false (P : Assertion) (pc reg : UInt64) (s : String)
    (L : Set UInt64) :
  L = {n : UInt64 | n ≠ pc + 1} →
  hoare
    ⟪bnez x reg, s;⟫
    ⦃P ⟦pc++⟧ ∧ x[reg] = 0 ∧ ¬⸨terminated⸩⦄
    pc ↦ ⟨{pc + 1} | L⟩
    ⦃P ⟦⟧ ∧ ¬⸨terminated⸩⦄
  end
  := by
  simpJumpSpec
