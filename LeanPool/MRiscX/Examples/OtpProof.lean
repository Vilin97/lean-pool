/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Elab.CodeElaborator
import LeanPool.MRiscX.Semantics.Specification
import LeanPool.MRiscX.Delab.DelabCode
import LeanPool.MRiscX.Elab.HoareElaborator
import LeanPool.MRiscX.Hoare.HoareRules
import LeanPool.MRiscX.Util.BasicTheorems
import LeanPool.MRiscX.Examples.SingleProofsOTP
import Mathlib.Tactic.NthRewrite

/-!
# OtpProof

This module provides the end-to-end One-Time-Pad correctness proof.
-/



def I_pre (p k c l : UInt64) :=
  p < k ∧ k < c ∧
  c.toNat + l.toNat < UInt64.size ∧
  (p + l - 1 < k ∧ k + l - 1 < c)




theorem proof_otp : ∀ (p k c l: UInt64),
  mriscx
    main: la x 0, p
          la x 1, k
          la x 2, c
          li x 3, l
    .loop: beqz x 3, finish
          lw x 5, x 0
          lw x 6, x 1
          xor x 7, x 5, x 6
          sw x 7, x 2
          inc x 0
          inc x 1
          inc x 2
          dec x 3
          j .loop
    finish:
  end
  ⦃
    (p < k ∧ k < c
    ∧ c.toNat + l.toNat < UInt64.size
    ∧ (p + l - 1 < k ∧ k + l - 1 < c))
    ∧ ¬⸨terminated⸩
  ⦄
  "main" ↦ ⟨{"finish"} | ({n:UInt64 | n > "finish"} ∪ {"main"})⟩
  ⦃
    ∀ (i:UInt64), i < l → mem[c + i] = mem[p + i] ^^^ mem[k + i]
    ∧ ¬⸨terminated⸩
  ⦄
  := by
  intros p k c l
  -- cut at loop
  sapply_s_seq''
    ⦃(x[0] = p ∧ x[1] = k ∧ x[2] = c ∧ x[3] = l ∧ (I_pre p k c l)) ∧ ¬⸨terminated⸩⦄ ,
    {4} ,
    {14},
    ({n:UInt64| n > 4} ∪ {0}),
    ({n | n ≠ 14} \ ({n:UInt64 | n ≥ 4} ∩ {n:UInt64 | n < 14}))
  · -- cut into 0 -> 3, 3 -> 4
    -- L_b ∩ L_b' = {n | n > 4} ∪ {0} -> {n | n≠ 3} ∩ {n | n > 4} ∪ {0}
    sapply_s_seq''  P := ⦃
                            (p < k ∧ k < c
                            ∧ c.toNat + l.toNat < UInt64.size
                            ∧ (p + l - 1 < k ∧ k + l - 1 < c))
                            ∧ ¬⸨terminated⸩
                          ⦄,
                    R := ⦃(x[0] = p ∧ x[1] = k ∧ x[2] = c ∧ ((p < k ∧ k < c
                          ∧ c.toNat + l.toNat < UInt64.size
                          ∧ (p + l - 1 < k ∧ k + l - 1 < c)))) ∧ ¬⸨terminated⸩⦄,
                    L_W := {3},
                    L_W' := {4},
                    L_B := {n | n > 3} ∪ {0},
                    L_B' := {n:UInt64 | n ≠ 4}
    -- cut into 0 -> 2, 2 -> 3
    · sapply_s_seq''
        ⦃(x[0] = p ∧ x[1] = k ∧ (I_pre p k c l)) ∧ ¬⸨terminated⸩ ⦄ , {2} , {3},
        ({n:UInt64 | n > 2} ∪ {0}),
        {n:UInt64 | n ≠ 3}
      -- cut into 0 -> 1, 1 -> 2
      · sapply_s_seq''
        ⦃(x[0] = p ∧ (I_pre p k c l)) ∧ ¬⸨terminated⸩⦄ , {1} , {2},
        {n:UInt64 | n ≠ 1},
        {n:UInt64 | n ≠ 2}
        · apply_spec specification_LoadAddress (s := s) (pc := 0) (dst := 0) (addr := p)
        · apply_spec specification_LoadAddress (s := s) (pc := 1) (dst := 1) (addr := k)
        · simp_set_eq
      · apply_spec specification_LoadAddress (s := s) (pc := 2) (dst := 2) (addr := c)
      · simp_set_eq
    · apply_spec specification_LoadImmediate (s := s) (pc := 3) (dst := 3) (val := l)
    · simp_set_eq
    -- end 0 → 4 proof
    -- start 4 → 14 proof
  · intros l' h_l'
    rw [h_l']
    unfold hoare_triple_up
    intros h_inter h_empty s s_code h_pc pre
    apply S_LOOP
      (C := ⦃x[3] > 0⦄)
      (I := ⦃((∀(i : UInt64), i < l - x[3] -> mem[c + i] = mem[p + i] ^^^ mem[k + i])
              ∧ x[0] = (p + (l - x[3]))
              ∧ x[1] = (k + (l - x[3]))
              ∧ x[2] = (c + (l - x[3]))
              ∧ x[3] ≤ l ∧ I_pre p k c l)
              ∧ ¬⸨terminated⸩ ⦄)
      (V := ⦃x[3]⦄)
      (l := 4)
      (L_w := {14})
      (L_b := {n | n ≠ 14} \ ({n:UInt64 | n ≥ 4} ∩ {n:UInt64 | n < 14}) )
    · simp
    · simp
    · unfold hoare_triple_up
      rintro x h_inter h_empty s' h_code' h_pc ⟨h_condition, ⟨h_terminated, h_I⟩, h_var⟩
      -- cut after dec
      apply S_SEQ (P := ⦃(x[3] > 0 ∧ (∀ (i:UInt64),
                          i < l - x[3] → mem[c + i] = mem[p + i] ^^^ mem[k + i])
                        ∧ x[0] = (p + (l - x[3]))
                        ∧ x[1] = (k + (l - x[3]))
                        ∧ x[2] = (c + (l - x[3]))
                        ∧ x[3] ≤ l
                        ∧ x[3] = x
                        ∧ I_pre p k c l) ∧ ¬⸨terminated⸩ = true⦄)
        (R := ⦃
          ((∀ (i : UInt64), i < l - x[3] → mem[c + i] = mem[p + i] ^^^ mem[k + i])
            ∧ x[0] = (p + (l - (x[3])))
            ∧ x[1] = (k + (l - (x[3])))
            ∧ x[2] = (c + (l - (x[3])))
            ∧ x[3] ≤ l
            ∧ x[5] = mem[x[0] - 1]
            ∧ x[6] = mem[x[1] - 1]
            ∧ x[7] = x[5] ^^^ x[6]
            ∧ x[3] < x
            ∧ I_pre p k c l) ∧ ¬⸨terminated⸩ = true ⦄)
        (L_w := {13})
        (L_w' := {4} ∪ {14})
        (L_b := {n : UInt64 | n ≤ 4} ∪ {n | n > 13})
        (L_b' :=  {n:UInt64 | n ≠ 4} \ {14})
        (l := 4)
      simp;
      · simp
      · simp_set_eq
      · rw [Set.subset_def]
        simp
      · -- cut after inc x2
        sapply_s_seq''
        ⦃(x[3] > 0 ∧ (∀ (i : UInt64), i ≤ l - x[3] → mem[c + i] = mem[p + i] ^^^ mem[k + i])
            ∧ x[0] = (p + (l - (x[3] - 1)))
            ∧ x[1] = (k + (l - (x[3] - 1)))
            ∧ x[2] = (c + (l - (x[3] - 1)))
            ∧ x[3] ≤ l
            ∧ x[5] = mem[x[0] - 1]
            ∧ x[6] = mem[x[1] - 1]
            ∧ x[7] = x[5] ^^^ x[6]
            ∧ x[3] = x
            ∧ I_pre p k c l) ∧ ¬⸨terminated⸩ = true ⦄ , {12} , {13} ,
            ({n:UInt64 | n ≤ 4} ∪ {n:UInt64 | n > 12}),
            ({n:UInt64 | n ≠ 12 + 1})
        · -- cut after inc x1
          sapply_s_seq''
          ⦃(x[3] > 0 ∧ (∀ (i : UInt64), i ≤ l - x[3] → mem[c + i] = mem[p + i] ^^^ mem[k + i])
              ∧ x[0] = (p + (l - (x[3] - 1)))
              ∧ x[1] = (k + (l - (x[3] - 1)))
              ∧ x[2] = (c + (l - (x[3])))
              ∧ x[3] ≤ l
              ∧ x[5] = mem[x[0] - 1]
              ∧ x[6] = mem[x[1] - 1]
              ∧ x[7] = x[5] ^^^ x[6]
              ∧ x[3] = x
              ∧ I_pre p k c l) ∧ ¬⸨terminated⸩ = true ⦄ , {11} , {12},
              ({n:UInt64 | n ≤ 4} ∪ {n:UInt64 | n > 11}),
              ({n:UInt64 | n ≠ 11 + 1})
          · -- cut after inc x0
            -- rw [←s_code]
            sapply_s_seq''
            ⦃(x[3] > 0
              ∧ (∀ (i : UInt64), i ≤ l - x[3] → mem[c + i] = mem[p + i] ^^^ mem[k + i])
              ∧ x[0] = (p + (l - (x[3] - 1)))
              ∧ x[1] = (k + (l - (x[3])))
              ∧ x[2] = (c + (l - (x[3])))
              ∧ x[3] ≤ l
              ∧ x[5] = mem[x[0] - 1]
              ∧ x[6] = mem[x[1]]
              ∧ x[7] = x[5] ^^^ x[6]
              ∧ x[3] = x
              ∧ I_pre p k c l
              ) ∧ ¬⸨terminated⸩ = true ⦄, {10} , {11},
              ({n:UInt64 | n ≤ 4} ∪ {n:UInt64 | n > 10}),
              ({n:UInt64 | n ≠ 11})
            · -- cut after sw
              sapply_s_seq''
              ⦃(x[3] > 0 ∧ (∀ (i : UInt64), i ≤ l - x[3] →
                  mem[c + i] = mem[p + i] ^^^ mem[k + i])
                  ∧ x[0] = (p + (l - (x[3])))
                  ∧ x[1] = (k + (l - (x[3])))
                  ∧ x[2] = (c + (l - x[3]))
                  ∧ x[3] ≤ l
                  ∧ x[5] = mem[x[0]] ∧ x[6] = mem[x[1]] ∧ x[7] = x[5] ^^^ x[6]
                  ∧ x[3] = x
                  ∧ I_pre p k c l)
                  ∧ ¬⸨terminated⸩ = true ⦄ , {9} , {10},
                  ({n:UInt64 | n ≤ 4} ∪ {n:UInt64 | n > 9}),
                  ({n:UInt64 | n ≠ 10})
              · -- cut after xor
                sapply_s_seq''
                ⦃(x[3] > 0 ∧ (∀ (i : UInt64), i < l - x[3] →
                    mem[c + i] = mem[p + i] ^^^ mem[k + i])
                    ∧ x[0] = (p + (l - (x[3]))) ∧ x[1] = (k + (l - (x[3]))) ∧
                      x[2] = (c + (l - x[3]))
                    ∧ x[3] ≤ l
                    ∧ x[5] = mem[x[0]] ∧ x[6] = mem[x[1]] ∧ x[7] = x[5] ^^^ x[6]
                    ∧ x[3] = x
                    ∧ I_pre p k c l)
                    ∧ ¬⸨terminated⸩ = true ⦄ , {8} , {9},
                    ({n:UInt64 | n ≤ 4} ∪ {n:UInt64 | n > 8}),
                    ({n:UInt64 | n ≠ 9})
                · -- cut after lw6
                  sapply_s_seq''
                  ⦃(x[3] > 0 ∧ (∀ (i : UInt64), i < l - x[3] →
                    mem[c + i] = mem[p + i] ^^^ mem[k + i])
                    ∧ x[0] = (p + (l - (x[3]))) ∧ x[1] = (k + (l - (x[3]))) ∧
                      x[2] = (c + (l - x[3]))
                    ∧ x[3] ≤ l
                    ∧ x[5] = mem[x[0]] ∧ x[6] = mem[x[1]]
                    ∧ x[3] = x
                    ∧ I_pre p k c l) ∧ ¬⸨terminated⸩ = true ⦄ , {7} , {8},
                    ({n:UInt64 | n ≤ 4} ∪ {n:UInt64 | n > 7}),
                    ({n:UInt64 | n ≠ 8})
                  ·  -- cut after lw5
                    sapply_s_seq''
                    ⦃(x[3] > 0 ∧ (∀ (i : UInt64), i < l - x[3] →
                      mem[c + i] = mem[p + i] ^^^ mem[k + i])
                      ∧ x[0] = (p + (l - (x[3]))) ∧ x[1] = (k + (l - (x[3]))) ∧
                        x[2] = (c + (l - x[3]))
                      ∧ x[3] ≤ l
                      ∧ x[5] = mem[x[0]]
                      ∧ x[3] = x
                      ∧ I_pre p k c l) ∧ ¬⸨terminated⸩ = true ⦄ , {6} , {7},
                      ({n:UInt64 | n ≤ 4} ∪ {n:UInt64 | n > 6}),
                      ({n:UInt64 | n ≠ 7})
                    ·  -- cut after beqz
                      sapply_s_seq''
                      ⦃(x[3] > 0 ∧ (∀ (i : UInt64), i < l - x[3] →
                        mem[c + i] = mem[p + i] ^^^ mem[k + i])
                        ∧ x[0] = (p + (l - (x[3]))) ∧ x[1] = (k + (l - (x[3]))) ∧
                          x[2] = (c + (l - x[3]))
                        ∧ x[3] ≤ l
                        ∧ x[3] = x
                        ∧ I_pre p k c l) ∧ ¬⸨terminated⸩ = true ⦄ , {5} , {6},
                        ({n:UInt64 | n ≤ 4} ∪ {n:UInt64 | n > 5}),
                        ({n:UInt64 | n ≠ 6})
                      · apply beqz_otp
                      · apply_spec specification_LoadWordReg (pc := 5) (dst := 5) (regWithAddr := 0)
                      · simp_set_eq
                    · apply_spec specification_LoadWordReg (pc := 6) (dst := 6) (regWithAddr := 1)
                    · simp_set_eq
                  · have : @singleton UInt64 (Set UInt64) Set.instSingletonSet 8
                        = @singleton UInt64 (Set UInt64) Set.instSingletonSet (7 + 1) := by
                      simp
                    rw [this]
                    apply_spec specification_XOR (dst := 7) (reg1 := 5) (reg2 := 6)
                  · simp_set_eq
                · intros l' h_l'
                  rw [h_l']
                  apply sw_otp
                · simp_set_eq
              · intros l' h_l'
                rw [h_l']
                apply inc_otp_0
              · simp_set_eq
            · intros l h_l'
              rw [h_l']
              apply inc_otp_1
            · simp_set_eq
          · intros l h_l'
            rw [h_l']
            apply inc_otp_2
          · simp_set_eq
        · intros l' h_l'
          rw [h_l']
          -- rw [←s_code]
          apply dec_otp
        · simp_set_eq
      · intros l' h_l'
        rw [h_l']
        apply j_otp
      · simp only [ne_eq, ge_iff_le, gt_iff_lt]
        simp_set_eq
      · simp_set_eq
      · intro neq
        have hmem : (4 : UInt64) ∈ (({4} ∪ {14}): Set UInt64) := by
          left
          rfl
        rw [neq] at hmem
        contradiction
      · exact h_code'
      · exact h_pc
      · rcases h_terminated with ⟨h_i, h_x0, h_x1, h_x2, h_x3, h_I_pre⟩
        exact ⟨⟨h_condition, h_i, h_x0, h_x1, h_x2, h_x3, h_var, h_I_pre⟩, h_I⟩
    · --unfold hoare_triple_up
      intros h_inter h_empty s h_code' h_pc pre
      -- L_b := {n | n > 14} ∪ {n | n < 4}, but should be {n|n≠14} -> maybe some rule that allows
      -- adding to L_b? -> BL-SUBSET
      apply BL_SUBSET (L := ({n | n ≥ 4} ∩ {n | n < 14})) (L_b := {n | (n ≠ 14)}) (L_w := {14})
        (s := s) (l := 4)
        (P := ⦃¬x[3] > 0 ∧ ¬⸨terminated⸩ ∧
        ∀(i : UInt64), i < l - x[3] -> mem[c + i] = mem[p + i] ^^^ mem[k + i] ⦄)
      · simp
      · -- apply_spec specification_JumpEqZero_true (s := "finish") (newPc := 14)
        --   (pc := 4) (r := 3)
        intros h_inter h_empty s h_code' h_pc pre'
        rw [←h_code']
        have:
            (∃ s',
              weak s s' {14} {n | n ≠ 14} s.code ∧
                (fun st =>
                      (∀ i < l,
                        st.getMemoryAt (c + i) = st.getMemoryAt (p + i)
                          ^^^ st.getMemoryAt (k + i)) ∧
                          ¬st.terminated = true)
                    s' ∧
                  s'.pc ∉ {n | n ≠ 14})
              →
              ∃ s',
                weak s s' {14} {n | n ≠ 14} s.code ∧
                  (fun st =>
                        ∀ i < l,
                          st.getMemoryAt (c + i) = st.getMemoryAt (p + i)
                            ^^^ st.getMemoryAt (k + i) ∧
                            ¬st.terminated = true)
                      s' ∧
                    s'.pc ∉ {n | n ≠ 14} := by
              simp only [ne_eq, MState.getMemoryAt_def, Bool.not_eq_true, Set.mem_setOf_eq,
                Decidable.not_not, forall_exists_index, and_imp]
              intros s' h_ex h_fo h_ter h_pc
              exists s'
              repeat constructor -- <;> try assumption
              exact h_ex
              constructor
              intros i h_i
              specialize h_fo i h_i
              exact ⟨h_fo, h_ter⟩
              exact h_pc
        apply this
        clear this
        apply specification_JumpEqZero_true (label := "finish") (newPc := 14)
          (pc := 4) (reg := 3)
          -- (P := ⦃∀ i < l,
          --   mem[c+i] = mem[p + i] ^^^ mem[k + i]⦄)
        · simp
        · simp
        · simp
        · unfold MState.currInstruction
          rw [h_code', h_pc]
          simp
        · exact h_pc
        · rcases pre' with ⟨h_reg_3, h_term, h⟩
          simp only [gt_iff_lt, UInt64.not_lt, MState.getRegisterAt_def,
            UInt64.le_zero_iff] at h_reg_3
          constructor
          · intros i h_i
            specialize h i
            apply h
            simp only [MState.getRegisterAt_def]
            rw [h_reg_3]
            simp only [UInt64.sub_zero]
            exact h_i
          · simp only [MState.get_label_from_code, MState.getRegisterAt_def, Bool.not_eq_true]
            constructor
            · rw [h_code']
              simp [p_update_eq]
            · simp at h_term
              exact ⟨h_reg_3, h_term⟩
      · ext a
        simp
      · simp
      · exact h_code'
      · exact h_pc
      · rcases pre with ⟨h_cond, h_temp, h_terminated⟩
        constructor
        exact h_cond
        · constructor
          · exact h_terminated
          · rcases h_temp with ⟨h_I, _⟩
            exact h_I
    · ext a
      simp
    · simp
    · exact s_code
    · exact h_pc
    -- x[3] = l so this is the beginning
    · unfold I_pre at pre
      rcases pre with ⟨⟨h_x0, h_x1, h_x2, h_x3, h_noOverlap⟩, h_terminated⟩
      rw [h_x3]
      constructor
      · constructor
        · intros i h_i'
          simp at h_i'
        · unfold I_pre
          simp only [MState.getRegisterAt_def, UInt64.sub_self, UInt64.add_zero, Std.le_refl,
            true_and]
          have : l ≤ l := by
            simp
          exact ⟨h_x0, h_x1, h_x2, h_noOverlap⟩
      · exact h_terminated
  · simp_set_eq
