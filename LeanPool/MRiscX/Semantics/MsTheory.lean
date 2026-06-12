/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax
import LeanPool.MRiscX.AbstractSyntax.MState
import LeanPool.MRiscX.Semantics.Run
import LeanPool.MRiscX.Util.BasicTheorems

import Mathlib.Data.Set.Basic
import Lean

/-!
Basic theorems

This file contains many small lemmata about the built machine model.
These lemmata help proving
statements about the MRiscX language by simplifying terms.
All these lemmata are added to the simp command with
the `@[simp]`. This can shorten proofs because lean
can apply these theorems with simp automatically.
-/


namespace MState

@[simp] theorem incPc_increments_pc : ∀ (ms:MState),
  ms.incPc = {ms with pc := ms.pc + 1} := by
  intros ms
  unfold MState.incPc
  simp

theorem setReg_incPc_symm : ∀(ms:MState) (r:Registers),
  (ms.setRegister r).incPc = ms.incPc.setRegister r := by
  intros ms r
  unfold MState.setRegister MState.incPc
  simp

theorem addReg_incPc_comm : ∀(ms:MState) (r v: UInt64),
  (ms.addRegister r v).incPc = ms.incPc.addRegister r v:= by
  intros ms r
  unfold MState.addRegister MState.incPc
  simp

theorem addMem_incPc_comm : ∀(ms:MState) (r v: UInt64),
  (ms.addMemory r v).incPc = ms.incPc.addMemory r v:= by
  intros ms r
  unfold MState.addMemory MState.incPc
  simp

theorem incPc_terminated : ∀(ms:MState),
  ms.incPc.terminated = ms.terminated := by
  intros ms
  unfold MState.incPc
  simp


@[simp] theorem setPc_terminated : ∀(ms:MState) (p:UInt64),
  (ms.setPc p).terminated = ms.terminated := by
  intros ms p
  unfold MState.setPc
  simp

theorem addReg_terminated : ∀(ms:MState) (r v: UInt64),
  (ms.addRegister r v).terminated = ms.terminated := by
  intros ms r v
  unfold MState.addRegister
  simp

theorem addMem_terminated : ∀(ms:MState) (r v: UInt64),
  (ms.addMemory r v).terminated = ms.terminated := by
  intros ms r v
  unfold MState.addMemory
  simp


-- @[simp] theorem setReg_setMem_symm: ∀(ms:MState) (r:Registers) (m:Memory),
--  ((ms.setRegister r).setMemory m).incPc = (ms.setRegister r).incPc.setMemory m ∧
--   (ms.setRegister r).incPc.setMemory m = (ms.incPc.setRegister r).setMemory m ∧
--   (ms.incPc.setRegister r).setMemory m = (ms.incPc.setMemory m).setRegister r ∧
--   (ms.incPc.setMemory m).setRegister r = ((ms.setMemory m).setRegister r).incPc ∧
--   ((ms.setMemory m).setRegister r).incPc = (ms.setMemory m).incPc.setRegister r := by
--   intros ms r m
--   unfold MState.setMemory MState.setRegister MState.incPc
--   simp

theorem addRegister_getRegister_neq :
  ∀(ms:MState) (r1 r2 v : UInt64),
  r1 ≠ r2 →
  ((ms.addRegister r1 v).getRegisterAt r2) = (ms.getRegisterAt r2)
  := by
  intros ms r1 r2 v H
  unfold MState.addRegister MState.getRegisterAt
  rw [t_update_neq]; simp at H
  simp [H]

theorem addRegister_getRegister_eq :
  ∀(ms:MState) (r1 r2 v : UInt64),
  r1 = r2 →
  ((ms.addRegister r1 v).getRegisterAt r2) = v
  := by
  intros ms r1 r2 v H
  unfold MState.addRegister MState.getRegisterAt
  rw [H, t_update_eq]


theorem setPc_getRegister_indep :
  ∀(ms:MState) (i : UInt64) (r : UInt64),
  ((ms.setPc i).getRegisterAt r) = (ms.getRegisterAt r)
  := by
  intros ms i r
  unfold MState.setPc MState.getRegisterAt
  simp

theorem setPc_getRegisterAt_def_indep :
  ∀(ms:MState) (r l: UInt64),
  TMap.get ms.registers r = TMap.get (ms.setPc l).registers r
  := by
  intros ms r l
  unfold MState.setPc
  simp

theorem setPc_getMemory_indep :
  ∀(ms:MState) (i : UInt64) (r : UInt64),
  ((ms.setPc i).getMemoryAt r) = (ms.getMemoryAt r)
  := by
  intros ms i r
  unfold MState.setPc MState.getMemoryAt
  simp

theorem setPc_getMemoryAt_def_indep :
  ∀(ms:MState) (m l: UInt64),
  TMap.get ms.memory m = TMap.get (ms.setPc l).memory m
  := by
  intros ms i r
  unfold MState.setPc
  simp


@[simp] theorem set_pc :
  ∀(ms:MState) (i : UInt64) ,
  (ms.setPc i).pc = i
  := by
  intros ms i
  unfold MState.setPc
  simp

theorem incPc_getRegister_indep :
  ∀(ms:MState) (r : UInt64),
  ((ms.incPc).getRegisterAt r) = (ms.getRegisterAt r)
  := by
  intros ms r
  unfold MState.incPc MState.getRegisterAt
  simp


@[simp] theorem jump_set_pc : ∀ (ms:MState) (s:String) (i:UInt64),
  (ms.code.labels.get s) = i ->
  (ms.jump s) = {ms with pc := i} := by
  intros ms s i H
  unfold MState.jump
  rw [H]

@[simp] theorem currInstruction_unfold : ∀ (ms:MState),
  ms.currInstruction = ms.code.instructionMap.get (ms.pc) := by
  intros ms
  unfold MState.currInstruction
  simp

theorem runNSteps_currInstruction : ∀ (ms:MState) (n:Nat),
  (ms.runNSteps n).currInstruction = (ms.runNSteps n).code.instructionMap.get ((ms.runNSteps n).pc)
  := by
  intros ms n
  unfold MState.runNSteps
  simp




@[simp] theorem addRegister_unfold (ms : MState) : ∀ (i1 i2:UInt64),
  ms.addRegister i1 i2 = {ms with registers :=
    ((i1) ↦ i2; ms.registers)} := by
  intros i1 i2
  unfold MState.addRegister
  simp

@[simp] theorem addMemory_unfold (ms : MState) : ∀ (i1 i2:UInt64),
  ms.addMemory i1 i2 = {ms with memory :=
    ((i1) ↦ i2; ms.memory)} := by
  intros i1 i2
  unfold MState.addMemory
  simp

@[simp] theorem run_zero_steps (ms : MState) :
  ms.runNSteps 0 = ms := by
  unfold MState.runNSteps
  rfl

theorem run_n_run_one : ∀ (ms:MState) (n:Nat),
  (ms.runNSteps n).runOneStep = ms.runNSteps (n+1) := by
  intros ms n
  revert ms
  induction n
  case zero =>
    intros ms
    rw [MState.run_zero_steps]
    unfold MState.runNSteps
    rw [MState.run_zero_steps]
  case succ n' IHN' =>
    intros ms
    unfold MState.runNSteps
    rw [IHN']

theorem run_n_run_one_comm : ∀ (ms:MState) (n:Nat),
  (ms.runNSteps n).runOneStep = ms.runOneStep.runNSteps n := by
  intros ms n
  revert ms
  induction n
  case zero =>
    intros ms
    rw [MState.run_zero_steps]
    unfold MState.runNSteps
    rfl
  case succ n' IHN' =>
    intros ms
    unfold MState.runNSteps
    rw [IHN']

@[simp] theorem run_one_step_eq_run_n_1 : ∀ (ms:MState),
  ms.runOneStep = ms.runNSteps 1 := by
  intros ms
  unfold MState.runNSteps
  simp

theorem run_N_comm : ∀ (ms:MState) (n m:Nat),
  (ms.runNSteps n).runNSteps m = (ms.runNSteps m).runNSteps n := by
  intros ms n
  revert ms
  induction n
  case zero =>
    intro ms m
    rw [MState.run_zero_steps, MState.run_zero_steps]
  case succ n IHN' =>
    intros ms m
    rw [<- MState.run_n_run_one, <- MState.run_n_run_one]
    rw [<- IHN']
    rw [<- MState.run_n_run_one_comm]

@[simp] theorem run_n_m_steps_comp : ∀ (ms:MState) (n m:Nat),
  (ms.runNSteps n).runNSteps m = ms.runNSteps (n + m) := by
  intros ms n
  revert ms
  induction n
  case zero =>
    intros m
    rw [MState.run_zero_steps]
    simp
  case succ n' IHN' =>
    intros ms m
    rw [<- MState.run_n_run_one, Nat.add_assoc, <- IHN', Nat.add_comm,
      <- MState.run_n_run_one, <- MState.run_n_run_one_comm]

theorem add_reg_code_no_change : ∀ (ms:MState) (r v:UInt64),
  (ms.addRegister r v).code = ms.code := by
  intros ms r v
  unfold MState.addRegister
  simp

theorem add_mem_code_no_change : ∀ (ms:MState) (r v:UInt64),
  (ms.addMemory r v).code = ms.code := by
  intros ms r v
  unfold MState.addMemory
  simp

@[simp] theorem set_pc_code_no_change : ∀ (ms:MState) (v:UInt64),
  (ms.setPc v).code = ms.code := by
  intros ms v
  unfold MState.setPc
  simp

@[simp] theorem set_termianted_code_no_change : ∀ (ms:MState) (v:Bool),
  (ms.setTerminated v).code = ms.code := by
  intros ms v
  unfold MState.setTerminated
  simp

@[simp] theorem jump_register_indep : ∀ (ms:MState) (m:Memory) (r:Registers) (c:Code) (s:String),
  ({ms with registers := r, memory := m, code := c}.jump s).pc
    = ({ms with code := c}.jump s).pc := by
  intros ms m r c s
  unfold MState.jump
  simp
  cases PMap.get c.labels s
  · dsimp
  · simp

theorem get_register_only_register :
    ∀ (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {registers := r, memory := m, code := c, pc := p,
    terminated := terminated : MState}.getRegisterAt i =
  TMap.get r i := by
  intros r m _ terminated i p
  unfold MState.getRegisterAt
  simp

theorem get_register_only_register' :
    ∀ (ms:MState) (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {ms with memory := m, registers := r, pc := p, code := c, terminated := terminated }.getRegisterAt
    i =
  {ms with registers := r}.getRegisterAt i := by
  intros ms r m _ terminated i p
  unfold MState.getRegisterAt
  simp

theorem get_register_only_memory :
    ∀ (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {registers := r, memory := m, code := c, pc := p,
    terminated := terminated : MState}.getMemoryAt i =
  TMap.get m i := by
  intros r m _ terminated i p
  unfold MState.getMemoryAt
  simp

theorem get_register_only_memory' :
    ∀ (ms:MState) (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {ms with memory := m, registers := r, pc := p, code := c, terminated := terminated }.getMemoryAt
    i =
  {ms with memory := m}.getMemoryAt i := by
  intros ms r m _ terminated i p
  unfold MState.getMemoryAt
  simp


@[simp] theorem get_label_from_code : ∀(ms : MState) (s : String) (l : UInt64),
  (ms.getLabelAt s = l) = (PMap.get ms.code.labels s = l)
  := by
  intros ms s l
  unfold MState.getLabelAt
  simp

@[simp] theorem getRegisterAt_def : ∀ (ms : MState) (l : UInt64),
  ms.getRegisterAt l = TMap.get ms.registers l := by
  intros ms l
  unfold MState.getRegisterAt
  simp

@[simp] theorem getMemoryAt_def : ∀ (ms : MState) (l : UInt64),
  ms.getMemoryAt l = TMap.get ms.memory l := by
  intros ms l
  unfold MState.getMemoryAt
  simp

theorem TMap_register_le_zero_eq_zero : ∀(ms:MState) (l : UInt64),
    (TMap.get ms.registers l ≤ 0) = (TMap.get ms.registers l = 0) := by
  simp

theorem register_le_zero_eq_zero : ∀(ms:MState) (l : UInt64),
    (ms.getRegisterAt l ≤ 0) = (ms.getRegisterAt l = 0) := by
  simp

theorem runOneSteps_code_remains : ∀ (ms:MState),
  (ms.runOneStep).code = ms.code
  := by
  intros ms
  unfold MState.runOneStep
  cases ms.terminated
  case true => simp
  case false =>
    simp only [Bool.false_eq_true, ↓reduceIte, currInstruction_unfold, addRegister_unfold,
      incPc_increments_pc, getRegisterAt_def, getMemoryAt_def, addMemory_unfold, gt_iff_lt, ne_eq,
      decide_not]
    cases TMap.get ms.code.instructionMap ms.pc <;> simp only [set_termianted_code_no_change]
    case Jump s =>
      unfold MState.jump
      cases PMap.get ms.code.labels s <;> simp
    case JumpEq reg1 reg2 lbl | JumpNeq reg1 reg2 lbl
      | JumpGt reg1 reg2 lbl | JumpLe reg1 reg2 lbl =>
      unfold MState.jif' MState.getRegisterAt MState.jump
      simp
      split_ifs with h
      all_goals cases PMap.get ms.code.labels lbl <;> simp
    case JumpEqZero reg lbl | JumpNeqZero reg lbl =>
      unfold MState.jif MState.jump
      simp
      split_ifs with h
      all_goals cases PMap.get ms.code.labels lbl <;> simp


@[simp] theorem runNSteps_code_remains : ∀ (ms:MState) (n:Nat),
  (ms.runNSteps n).code = ms.code
  := by
  intros ms n
  unfold MState.runNSteps
  induction n with
  | zero =>
    simp
  | succ n' IHn' =>
    dsimp
    rw [<- run_n_run_one_comm, runOneSteps_code_remains]
    unfold MState.runNSteps
    exact IHn'

theorem code_remains_same : ∀ (ms ms' : MState) (code : Code) (n : ℕ),
  ms.code = code →
  ms.runNSteps n = ms' →
  ms'.code = code
  := by
  intros ms ms' code n h_code h_run
  rw [←h_run]
  simp [h_code]

theorem runNSteps_diff : ∀ (s : MState) (n : Nat) (L1 L2 : Set UInt64),
  L2 ⊆ L1 →
  (s.runNSteps n).pc ∉ L1 →
  (s.runNSteps n).pc ∉ L2
  := by
  intros s n L1 L2 HSub H
  apply Set.notMem_subset (t := L1) <;> try assumption

theorem runNSteps_pc_in_superset : ∀ (s : MState) (n : Nat) (L1 L2 : Set UInt64),
  L2 ⊆ L1 →
  (s.runNSteps n).pc ∈ L2 →
  (s.runNSteps n).pc ∈ L1
  := by
  intros s n L1 L2 HSub H
  apply Set.mem_of_subset_of_mem <;> try assumption

theorem runNSteps_add : ∀ (s s' s'':MState) (n n' : Nat),
  s.runNSteps n = s' →
  s'.runNSteps n' = s'' →
  s.runNSteps (n + n') = s'' := by
  intros s s' s'' n n' HRun HRun'
  rw [← run_n_m_steps_comp, HRun]
  exact HRun'

theorem runNSteps_pc_nin : ∀ (s s' s'': MState) (n n' : Nat) (L : Set UInt64),
  s.runNSteps n = s' →
  s'.runNSteps n' = s'' →
  (s.runNSteps n).pc ∉ L →
  (s'.runNSteps n').pc ∉ L →
  (s.runNSteps (n + n')).pc ∉ L
  := by
  intros s s' s'' n n' L HRun HRun' _ HNin'
  rw [runNSteps_add s s' s'' n n', ← HRun']
  repeat assumption

-- theorem runNSteps_min_1_pc_nin_extra_plus_one : ∀ (s s' : MState) (n n': Nat) (L : Set UInt64),
--   s.runNSteps n = s' →
--   s'.pc ∉ L →
--   0 < n' ∧ n' = n - 1 →
--   (s.runNSteps n').pc ∉ L →
--   (s.runNSteps n').runOneStep.pc ∉ L
--   := by
--   intros s s' n n' L HRun HPc HN' HRunLTNin
--   rcases HN' with ⟨HnGtZ, HnMinusOne⟩



theorem runNSteps_pc_nin_extra_step : ∀ (s s' : MState) (n : Nat) (L : Set UInt64),
  s.runNSteps n = s' →
  s'.pc ∉ L →
  (∀ (n' : Nat), 0 < n' ∧ n' < n → (s.runNSteps n').pc ∉ L) →
  ∀ (n'' : Nat), 0 < n'' ∧ n'' <= n → (s.runNSteps n'').pc ∉ L
  := by
  intros s s' n L HRun HPc HRunLTNin n'' Hn''
  rcases Hn'' with ⟨HN''GtZ, HN''LeN'⟩
  rw [← HRun] at HPc
  cases Nat.lt_or_eq_of_le HN''LeN' with
  | inl hlt =>
    apply HRunLTNin
    constructor <;> assumption
  | inr heq =>
    rw [heq]
    exact HPc



theorem run_n_plus_m_pc_not_in_set :
  ∀ (s s' : MState) (m m' : Nat) (set : Set UInt64),
  s.runNSteps m = s' →
  (∀ (n : ℕ), 0 < n ∧ n ≤ m → (s.runNSteps n).pc ∉ set) →
  (∀ (n' : ℕ), 0 < n' ∧ n' < m' → (s'.runNSteps n').pc ∉ set) →
  ∀ (n'' : ℕ), 0 < n'' ∧ n'' < m + m' → (s.runNSteps n'').pc ∉ set := by
  intros s s' m m' set h_eq hL_b hL_b' n'' hn
  rcases hn with ⟨hn0, hnlt⟩
  by_cases h : n'' ≤ m
  · have hcond : 0 < n'' ∧ n'' ≤ m := ⟨hn0, h⟩
    specialize hL_b n'' hcond
    exact hL_b
  -- m < n'' < m + m' → n'' = m + n' for some 0 < n' < m'
  · push Not at h
    -- n'' > m ⇒ ∃ n' such that n'' = m + n'
    let n' := n'' - m
    have h_pos : 0 < n' := by
      apply Nat.sub_pos_of_lt h
    have hn'_lt : n' < m' := by
      -- n'' < m + m' ⇒ n' = n'' - m < m'
      dsimp only [n']
      apply Nat.lt_sub_left <;> try assumption
    have h_run_eq : s.runNSteps n'' = s'.runNSteps n' := by
      dsimp only [n']
      rw [← h_eq]
      simp only [run_n_m_steps_comp]
      rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
      apply Nat.le_of_lt h
    rw [h_run_eq]
    have hn'_pre : 0 < n' ∧ n' < m' := by
      constructor <;> try assumption
    specialize hL_b' n' hn'_pre
    exact hL_b'

theorem run_n_plus_m_diff_set :
  ∀ (s s' : MState) (m m' : Nat) (L_b L_b' : Set UInt64),
  s.runNSteps m = s' →
  (∀ (n : ℕ), 0 < n ∧ n ≤ m → (s.runNSteps n).pc ∉ L_b) →
  (∀ (n' : ℕ), 0 < n' ∧ n' < m' → (s'.runNSteps n').pc ∉ L_b') →
  ∀ (n'' : ℕ), 0 < n'' ∧ n'' < m + m' → (s.runNSteps n'').pc ∉ L_b ∩ L_b'
:= by
  intros s s' m m' L_b L_b' h_eq hL_b hL_b' n'' hn
  rcases hn with ⟨hn0, hnlt⟩
  by_cases h : n'' ≤ m
  · have hcond : 0 < n'' ∧ n'' ≤ m := ⟨hn0, h⟩
    specialize hL_b n'' hcond
    intro h_in
    exact hL_b (Set.mem_of_mem_inter_left h_in)
  -- m < n'' < m + m' → n'' = m + n' for some 0 < n' < m'
  · push Not at h
    -- n'' > m ⇒ ∃ n' such that n'' = m + n'
    let n' := n'' - m
    have h_pos : 0 < n' := by
      apply Nat.sub_pos_of_lt h
    have hn'_lt : n' < m' := by
      -- n'' < m + m' ⇒ n' = n'' - m < m'
      dsimp only [n']
      apply Nat.lt_sub_left <;> try assumption
    have h_run_eq : s.runNSteps n'' = s'.runNSteps n' := by
      dsimp only [n']
      rw [← h_eq]
      simp only [run_n_m_steps_comp]
      rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
      apply Nat.le_of_lt h
    rw [h_run_eq]
    have hn'_pre : 0 < n' ∧ n' < m' := by
      constructor <;> try assumption
    specialize hL_b' n' hn'_pre
    intro h_in
    exact hL_b' (Set.mem_of_mem_inter_right h_in)


theorem run_n_plus_m_intersect : ∀ (s s' : MState) (m m' : Nat) (L_w L_b L_w' L_b' : Set UInt64),
  (L_w' ⊆ L_b ∧ L_w ∩ L_w' = ∅) →
  s.runNSteps m = s' →
  s'.pc ∈ L_w →
  s'.pc ∉ L_b →
  (∀ (n : ℕ), 0 < n ∧ n < m → (s.runNSteps n).pc ∉ L_w ∪ L_b) →
  (∀ (n' : ℕ), 0 < n' ∧ n' < m' → (s'.runNSteps n').pc ∉ L_w' ∪ L_b') →
  ∀ (n'' : ℕ), 0 < n'' ∧ n'' < m + m' → (s.runNSteps n'').pc ∉ L_w' ∪ L_b ∩ L_b'
:= by
  intros s s' m m' L_w L_b L_w' L_b' h_sets h_run1 h_pc_w h_pc_not_b h_safe1 h_safe2 n'' HN''
  rcases HN'' with ⟨h_pos, h_lt⟩
  rcases h_sets with ⟨h_Lw'SubL_b, h_LwInterLw'⟩
  -- n'' ≤ m → s.runNSteps n'' ∉ L_b ∧ s.runNSteps n'' ∈ L_w
  -- → s.runNSteps n'' ∉ (L_w' ∪ L_b), da L_w ∩ L_w' = ∅
  -- n'' > m → s.runNSteps n'' ∉ L_w' ∪ L_b'
  rw [Set.union_inter_distrib_left]
  by_cases h: n'' ≤ m
  · cases Nat.lt_or_eq_of_le h with
    | inl hlt =>
      have h_n'': 0 < n'' ∧ n'' < m := And.intro h_pos hlt
      specialize h_safe1 n'' h_n''
      have h_safe1_NinLw': (s.runNSteps n'').pc ∉ L_w' ∪ L_b:= by
        rw [Set.mem_union]
        simp only [not_or]
        rw [Set.mem_union] at h_safe1
        simp only [
          not_or] at h_safe1
        rcases h_safe1 with ⟨_, h_safe1_r⟩
        constructor
        · apply Set.notMem_subset (a:= (s.runNSteps n'').pc) (s := L_w') (t := L_b)
          repeat assumption
        · exact h_safe1_r
      intros h_in
      exact h_safe1_NinLw' (Set.mem_of_mem_inter_left h_in)
    | inr heq =>
      have h_safe1_m: (s.runNSteps n'').pc ∉ L_w' ∪ L_b := by
        rw [heq]
        rw [Set.mem_union]
        simp only [not_or]
        constructor
        · apply Set.notMem_subset (a:= (s.runNSteps m).pc) (s := L_w') (t := L_b)
          · exact h_Lw'SubL_b
          · rw [h_run1]
            exact h_pc_not_b
        · rw [h_run1]
          exact h_pc_not_b
      intros h_in
      exact h_safe1_m (Set.mem_of_mem_inter_left h_in)
  · push Not at h
    -- n'' > m ⇒ ∃ n' such that n'' = m + n'
    let n' := n'' - m
    have h_pos : 0 < n' := by
      apply Nat.sub_pos_of_lt h
    have hn'_lt : n' < m' := by
      -- n'' < m + m' ⇒ n' = n'' - m < m'
      dsimp only [n']
      apply Nat.lt_sub_left <;> try assumption
    have h_run_eq : s.runNSteps n'' = s'.runNSteps n' := by
      dsimp only [n']
      rw [← h_run1]
      simp only [run_n_m_steps_comp]
      rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
      apply Nat.le_of_lt h
    rw [h_run_eq]
    have hn'_pre : 0 < n' ∧ n' < m' := by
      constructor <;> try assumption
    specialize h_safe2 n' hn'_pre
    intro h_in
    exact h_safe2 (Set.mem_of_mem_inter_right h_in)

end MState
