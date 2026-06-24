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
import Lean.Elab.Command

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
  simp [MState.incPc]

theorem setReg_incPc_symm : ∀(ms:MState) (r:Registers),
  (ms.setRegister r).incPc = ms.incPc.setRegister r := by
  simp [MState.setRegister, MState.incPc]

theorem addReg_incPc_comm : ∀(ms:MState) (r v: UInt64),
  (ms.addRegister r v).incPc = ms.incPc.addRegister r v:= by
  simp [MState.addRegister, MState.incPc]

theorem addMem_incPc_comm : ∀(ms:MState) (r v: UInt64),
  (ms.addMemory r v).incPc = ms.incPc.addMemory r v:= by
  simp [MState.addMemory, MState.incPc]

theorem incPc_terminated : ∀(ms:MState),
  ms.incPc.terminated = ms.terminated := by
  simp [MState.incPc]


@[simp] theorem setPc_terminated : ∀(ms:MState) (p:UInt64),
  (ms.setPc p).terminated = ms.terminated := by
  simp [MState.setPc]

theorem addReg_terminated : ∀(ms:MState) (r v: UInt64),
  (ms.addRegister r v).terminated = ms.terminated := by
  simp [MState.addRegister]

theorem addMem_terminated : ∀(ms:MState) (r v: UInt64),
  (ms.addMemory r v).terminated = ms.terminated := by
  simp [MState.addMemory]


theorem addRegister_getRegister_neq :
  ∀(ms:MState) (r1 r2 v : UInt64),
  r1 ≠ r2 →
  ((ms.addRegister r1 v).getRegisterAt r2) = (ms.getRegisterAt r2)
  := by
  intros ms r1 r2 v H
  unfold MState.addRegister MState.getRegisterAt
  rw [t_update_neq]
  simp at H
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
  simp [MState.setPc, MState.getRegisterAt]

theorem setPc_getRegisterAt_def_indep :
  ∀(ms:MState) (r l: UInt64),
  TMap.get ms.registers r = TMap.get (ms.setPc l).registers r
  := by
  simp [MState.setPc]

theorem setPc_getMemory_indep :
  ∀(ms:MState) (i : UInt64) (r : UInt64),
  ((ms.setPc i).getMemoryAt r) = (ms.getMemoryAt r)
  := by
  simp [MState.setPc, MState.getMemoryAt]

theorem setPc_getMemoryAt_def_indep :
  ∀(ms:MState) (m l: UInt64),
  TMap.get ms.memory m = TMap.get (ms.setPc l).memory m
  := by
  simp [MState.setPc]


@[simp] theorem set_pc :
  ∀(ms:MState) (i : UInt64) ,
  (ms.setPc i).pc = i
  := by
  simp [MState.setPc]

theorem incPc_getRegister_indep :
  ∀(ms:MState) (r : UInt64),
  ((ms.incPc).getRegisterAt r) = (ms.getRegisterAt r)
  := by
  simp [MState.incPc, MState.getRegisterAt]


@[simp] theorem jump_set_pc : ∀ (ms:MState) (s:String) (i:UInt64),
  (ms.code.labels.get s) = i ->
  (ms.jump s) = {ms with pc := i} := by
  intros ms s i H
  unfold MState.jump
  rw [H]

@[simp] theorem currInstruction_unfold : ∀ (ms:MState),
  ms.currInstruction = ms.code.instructionMap.get (ms.pc) := by
  simp [MState.currInstruction]

theorem runNSteps_currInstruction : ∀ (ms:MState) (n:Nat),
  (ms.runNSteps n).currInstruction = (ms.runNSteps n).code.instructionMap.get ((ms.runNSteps n).pc)
  := by
  simp




@[simp] theorem addRegister_unfold (ms : MState) : ∀ (i1 i2:UInt64),
  ms.addRegister i1 i2 = {ms with registers :=
    ((i1) ↦ i2; ms.registers)} := by
  simp [MState.addRegister]

@[simp] theorem addMemory_unfold (ms : MState) : ∀ (i1 i2:UInt64),
  ms.addMemory i1 i2 = {ms with memory :=
    ((i1) ↦ i2; ms.memory)} := by
  simp [MState.addMemory]

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
  simp [MState.addRegister]

theorem add_mem_code_no_change : ∀ (ms:MState) (r v:UInt64),
  (ms.addMemory r v).code = ms.code := by
  simp [MState.addMemory]

@[simp] theorem set_pc_code_no_change : ∀ (ms:MState) (v:UInt64),
  (ms.setPc v).code = ms.code := by
  simp [MState.setPc]

@[simp] theorem set_termianted_code_no_change : ∀ (ms:MState) (v:Bool),
  (ms.setTerminated v).code = ms.code := by
  simp [MState.setTerminated]

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
  simp [MState.getRegisterAt]

theorem get_register_only_register' :
    ∀ (ms:MState) (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {ms with memory := m, registers := r, pc := p, code := c, terminated := terminated }.getRegisterAt
    i =
  {ms with registers := r}.getRegisterAt i := by
  simp [MState.getRegisterAt]

theorem get_register_only_memory :
    ∀ (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {registers := r, memory := m, code := c, pc := p,
    terminated := terminated : MState}.getMemoryAt i =
  TMap.get m i := by
  simp [MState.getMemoryAt]

theorem get_register_only_memory' :
    ∀ (ms:MState) (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {ms with memory := m, registers := r, pc := p, code := c, terminated := terminated }.getMemoryAt
    i =
  {ms with memory := m}.getMemoryAt i := by
  simp [MState.getMemoryAt]


@[simp] theorem get_label_from_code : ∀(ms : MState) (s : String) (l : UInt64),
  (ms.getLabelAt s = l) = (PMap.get ms.code.labels s = l)
  := by
  simp [MState.getLabelAt]

@[simp] theorem getRegisterAt_def : ∀ (ms : MState) (l : UInt64),
  ms.getRegisterAt l = TMap.get ms.registers l := by
  simp [MState.getRegisterAt]

@[simp] theorem getMemoryAt_def : ∀ (ms : MState) (l : UInt64),
  ms.getMemoryAt l = TMap.get ms.memory l := by
  simp [MState.getMemoryAt]

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
  exact Set.notMem_subset HSub H

theorem runNSteps_pc_in_superset : ∀ (s : MState) (n : Nat) (L1 L2 : Set UInt64),
  L2 ⊆ L1 →
  (s.runNSteps n).pc ∈ L2 →
  (s.runNSteps n).pc ∈ L1
  := by
  intros s n L1 L2 HSub H
  exact Set.mem_of_subset_of_mem HSub H

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
  rw [runNSteps_add s s' s'' n n' HRun HRun', ← HRun']
  exact HNin'

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



/-- For `m < n'' < m + m'` and `s.runNSteps m = s'`, the `n''`-step run of `s`
equals an `n'`-step run of `s'` for some `0 < n' < m'`. -/
private theorem exists_tail_run (s s' : MState) (m m' n'' : Nat)
    (h_eq : s.runNSteps m = s') (h : m < n'') (hnlt : n'' < m + m') :
    ∃ n', (0 < n' ∧ n' < m') ∧ s.runNSteps n'' = s'.runNSteps n' := by
  refine ⟨n'' - m, ⟨Nat.sub_pos_of_lt h, ?_⟩, ?_⟩
  · exact Nat.lt_sub_left _ _ _ h hnlt
  · rw [← h_eq]
    simp only [run_n_m_steps_comp]
    rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
    apply Nat.le_of_lt h

theorem run_n_plus_m_pc_not_in_set :
  ∀ (s s' : MState) (m m' : Nat) (set : Set UInt64),
  s.runNSteps m = s' →
  (∀ (n : ℕ), 0 < n ∧ n ≤ m → (s.runNSteps n).pc ∉ set) →
  (∀ (n' : ℕ), 0 < n' ∧ n' < m' → (s'.runNSteps n').pc ∉ set) →
  ∀ (n'' : ℕ), 0 < n'' ∧ n'' < m + m' → (s.runNSteps n'').pc ∉ set := by
  intros s s' m m' set h_eq hL_b hL_b' n'' hn
  rcases hn with ⟨hn0, hnlt⟩
  by_cases h : n'' ≤ m
  · exact hL_b n'' ⟨hn0, h⟩
  · push Not at h
    obtain ⟨n', hn'_pre, h_run_eq⟩ := exists_tail_run s s' m m' n'' h_eq h hnlt
    rw [h_run_eq]
    exact hL_b' n' hn'_pre

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
  · intro h_in
    exact hL_b n'' ⟨hn0, h⟩ (Set.mem_of_mem_inter_left h_in)
  · push Not at h
    obtain ⟨n', hn'_pre, h_run_eq⟩ := exists_tail_run s s' m m' n'' h_eq h hnlt
    rw [h_run_eq]
    intro h_in
    exact hL_b' n' hn'_pre (Set.mem_of_mem_inter_right h_in)


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
        simp only [not_or] at h_safe1
        rcases h_safe1 with ⟨_, h_safe1_r⟩
        exact ⟨Set.notMem_subset h_Lw'SubL_b h_safe1_r, h_safe1_r⟩
      intros h_in
      exact h_safe1_NinLw' (Set.mem_of_mem_inter_left h_in)
    | inr heq =>
      have h_pc_not_b' : (s.runNSteps m).pc ∉ L_b := h_run1 ▸ h_pc_not_b
      have h_safe1_m: (s.runNSteps n'').pc ∉ L_w' ∪ L_b := by
        rw [heq, Set.mem_union]
        simpa only [not_or]
          using ⟨Set.notMem_subset h_Lw'SubL_b h_pc_not_b', h_pc_not_b'⟩
      intros h_in
      exact h_safe1_m (Set.mem_of_mem_inter_left h_in)
  · push Not at h
    obtain ⟨n', hn'_pre, h_run_eq⟩ := exists_tail_run s s' m m' n'' h_run1 h h_lt
    rw [h_run_eq]
    specialize h_safe2 n' hn'_pre
    intro h_in
    exact h_safe2 (Set.mem_of_mem_inter_right h_in)

end MState
