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
import LeanPool.MRiscX.Tactics.CodeProofTactics

/-!
# SingleProofsOTP

This module provides the per-instruction lemmas of the One-Time-Pad proof.
-/
-- import Mathlib.Algebra.Order.Sub.Unbundled.Basic

open Lean Elab Parser Meta Tactic

/-
This file contains some individual proof-steps of the verification of
the implementation in `OtpProof.lean`. This was done because the compiler
in the very long proof took quite a while on every change.
-/

/-- The precondition shared by the per-instruction One-Time-Pad proofs,
constraining the plaintext `p`, key `k`, ciphertext `c`, and length `l` addresses. -/
def iPre' (p k c l : UInt64) :=
  p < k ∧ k < c ∧
  c.toNat + l.toNat < UInt64.size ∧
  (p + l - 1 < k ∧ k + l - 1 < c)




/-
Some reasoning about iPre
-/
theorem help_I_pre' : ∀ (p k c l: UInt64),
  iPre' p k c l →
  -- (h_x : 0 < x),
  c + (l - x) ≠ p + (l - x) := by
  intros p k c l h_I
  unfold iPre' at h_I
  rcases h_I with ⟨h_pk, h_kc, h_noOverfl, h_klc, h_plk⟩
  by_contra heq
  rw [UInt64.add_cancel_right_iff] at heq
  rw [heq] at h_kc
  apply UInt64.lt_asymm (a := p) (b := k)
  · exact h_pk
  · exact h_kc

theorem help_I_pre'' : ∀ (p k c l: UInt64),
  iPre' p k c l →
  -- (h_x : 0 < x),
  c + (l - x) ≠ k + (l - x) := by
  intros p k c l h_I
  unfold iPre' at h_I
  rcases h_I with ⟨h_pk, h_kc, h_noOverfl, h_klc, h_plk⟩
  by_contra heq
  rw [UInt64.add_cancel_right_iff] at heq
  rw [heq] at h_kc
  apply UInt64.lt_irrefl (a := k)
  exact h_kc


theorem help_I_pre''' : ∀ (p k c l i x: UInt64),
  iPre' p k c l →
  i < (l - x) →
  x ≤ l →
  -- (h_x : 0 < x),
  (c + (l - x) ≠ k + i) := by
  intros p k c l i x h_I hlx hxLeL
  unfold iPre' at h_I
  rcases h_I with ⟨h_pk, h_kc, h_noOverfl, h_klc, h_plk⟩
  simp only [ne_eq]
  by_contra neq
  have : k + i < c + (l - x) := by
      apply UInt64.add_lt_add
      · exact ⟨h_kc, hlx⟩
      · apply Nat.lt_of_le_of_lt (m := c.toNat + l.toNat)
        · simp only [Nat.add_le_add_iff_left]
          rw [UInt64.toNat_sub_of_le]
          · rw [←Nat.add_le_add_iff_right (n := x.toNat)]
            simp
          · exact hxLeL
        · exact h_noOverfl
  · rw [neq] at this
    apply UInt64.lt_asymm <;> try assumption


theorem help_I_pre'''' : ∀ (p k c l i x: UInt64),
  iPre' p k c l →
  i < (l - x) →
  x ≤ l →
  -- (h_x : 0 < x),
  (c + (l - x) ≠ p + i) := by
  intros p k c l i x h_I hlx hxLeL
  unfold iPre' at h_I
  rcases h_I with ⟨h_pk, h_kc, h_noOverfl, h_klc, h_plk⟩
  simp only [ne_eq]
  by_contra neq
  have h_pc : p < c := by
    apply UInt64.lt_trans (b := k)
    · exact h_pk
    · exact h_kc
  have : p + i < c + (l - x) := by
    apply UInt64.add_lt_add
    · exact ⟨h_pc, hlx⟩
    · apply Nat.lt_of_le_of_lt (m := c.toNat + l.toNat)
      · simp only [Nat.add_le_add_iff_left]
        rw [UInt64.toNat_sub_of_le]
        · rw [←Nat.add_le_add_iff_right (n := x.toNat)]
          simp
        · exact hxLeL
      · exact h_noOverfl
  · rw [neq] at this
    apply UInt64.lt_irrefl (a := p+i)
    exact this



theorem help_I_pre''''' : ∀ (p k c l i x: UInt64),
  iPre' p k c l →
  i.toNat < (l - x).toNat →
  x ≤ l →
  (c + (l - x) ≠ c + i) := by
  intros p k c l i x h_I hlx hxLeL
  unfold iPre' at h_I
  rcases h_I with ⟨h_pk, h_kc, h_noOverfl, h_klc, h_plk⟩
  simp only [ne_eq, UInt64.add_right_inj]
  push Not
  grind only


/-- The One-Time-Pad program, parameterised by the plaintext `p`, key `k`,
ciphertext `c`, and length `l` memory addresses. -/
def otpCode (p k c l : UInt64) :=
    mriscx
      main:
          la x 0, p
          la x 1, k
          la x 2, c
          li x 3, l
      .loop:
          beqz x 3, finish
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


theorem sw_otp : ∀ (p k c l : UInt64),
  (otpCode p k c l)
  ⦃(x[3] > 0
    ∧ (∀ i < l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i])
    ∧ x[0] = p + (l - x[3])
    ∧ x[1] = k + (l - x[3])
    ∧ x[2] = c + (l - x[3])
    ∧ x[3] ≤ l
    ∧ x[5] = mem[x[0]]
    ∧ x[6] = mem[x[1]]
    ∧ x[7] = x[5] ^^^ x[6]
    ∧ x[3] = x
    ∧ iPre' p k c l)
    ∧ ¬⸨terminated⸩ = true⦄
  8 ↦ ⟨{9} | {n | (n ≠ 9)}⟩
  ⦃(x[3] > 0 ∧
      (∀ i ≤ l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
        x[0] = p + (l - (x[3])) ∧
          x[1] = k + (l - x[3]) ∧
            x[2] = c + (l - x[3]) ∧
             x[3] ≤ l ∧
              x[5] = mem[x[0]] ∧ x[6] = mem[x[1]] ∧ x[7] = x[5] ^^^ x[6] ∧ x[3] = x
              ∧ iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄ := by
    unfold otpCode
    intros p k c l
    rintro h_inter h_empty s h_code' h_pc ⟨⟨h_cond, h_I, h_x0, h_x1, h_x2, h_x3LtL, h_x5, h_x6,
      h_x7, h_x3, h_I_pre'⟩, h_terminated⟩
    have: ({9} : Set UInt64)  = {8 + 1}  := by
      simp
    rw [this]
    rw [←h_code']
    apply specification_StoreWordImmediate (regWithAddr := 2) (regWithValue := 7)
    · simp
    · simp
    · simp
    · simpCurrInstr
    · assumption
    · simp only [MState.incPc_increments_pc, MState.getRegisterAt_def, MState.addMemory_unfold,
      gt_iff_lt, MState.getMemoryAt_def, Bool.not_eq_true]
      simp only [
        MState.getMemoryAt_def, MState.getRegisterAt_def,
        ne_eq, Bool.not_eq_true,
        gt_iff_lt] at *
      repeat (constructor <;> try assumption)
      · rw [h_x7, h_x5, h_x6, h_x0, h_x2, h_x1, h_x3]
        intros i h_i
        cases UInt64.lt_or_eq_of_le h_i with
        | inl v =>
          rw [t_update_neq]
          · rw [t_update_neq]
            · rw [t_update_neq]
              · rw [←h_x3] at h_i
                rw [←h_x3] at v
                apply h_I
                exact v
              · apply help_I_pre''' (p := p)
                · exact h_I_pre'
                · exact v
                · rw [←h_x3]
                  exact h_x3LtL
            · apply help_I_pre'''' p k c l i x
              · exact h_I_pre'
              · exact v
              · rw [←h_x3]
                exact h_x3LtL
          · apply help_I_pre''''' (p:=p) (k:=k) <;> try assumption
            rw [←h_x3]
            exact h_x3LtL
        | inr v =>
          rw [h_x3] at h_x0 h_x1 h_x2
          rw [v]
          rw [←h_x0, ←h_x1, ←h_x2, ←h_x5, ←h_x6]
          simp only [t_update_eq]
          rw [←h_x7]
          rw [t_update_neq]
          · rw [t_update_neq]
            · rw [←h_x5, ←h_x6]
              exact h_x7
            · rw [h_x2, h_x1]
              simp only [ne_eq, UInt64.add_left_inj]
              intros neq
              unfold iPre' at h_I_pre'
              rcases h_I_pre' with ⟨_, h_kc, _⟩
              rw [←neq] at h_kc
              apply UInt64.lt_irrefl c
              exact h_kc
          · rw [h_x0, h_x2]
            unfold iPre' at h_I_pre'
            rcases h_I_pre' with ⟨h_pk, h_kc, _⟩
            simp only [ne_eq, UInt64.add_left_inj]
            intros neq
            rw [←neq] at h_pk
            apply UInt64.lt_irrefl c
            have: c < c := by
              apply UInt64.lt_trans (b := k)
              · exact h_pk
              · exact h_kc
            exact this
      · repeat (constructor; try assumption)
        · rw [h_x0, h_x5, h_x0]
          rw [t_update_neq]
          rw [h_x2, h_x3]
          intros neq
          simp only [UInt64.add_left_inj] at neq
          unfold iPre' at h_I_pre'
          rcases h_I_pre' with ⟨pk, kc, _⟩
          rw [neq] at kc
          apply UInt64.lt_asymm (pk)
          exact kc
        · constructor
          · rw [h_x2, h_x3]
            rw [t_update_neq]
            · exact h_x6
            · rw [h_x1, h_x3]
              simp only [ne_eq, UInt64.add_left_inj]
              intros neq
              unfold iPre' at h_I_pre'
              rcases h_I_pre' with ⟨pk, kc, _⟩
              rw [←neq] at kc
              apply UInt64.lt_irrefl c kc
          · repeat (constructor <;> try assumption)




theorem inc_otp_0 : ∀ (p k c l : UInt64),
  (otpCode p k c l)
  ⦃(x[3] > 0 ∧
    (∀ i ≤ l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
      x[0] = p + (l - x[3]) ∧
        x[1] = k + (l - x[3]) ∧
          x[2] = c + (l - x[3]) ∧
            x[3] ≤ l ∧
              x[5] = mem[x[0]] ∧
                x[6] = mem[x[1]] ∧ x[7] = x[5] ^^^ x[6] ∧ x[3] = x ∧ iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄
  9 ↦ ⟨{10} | {n | (n ≠ 10)}⟩
  ⦃(x[3] > 0 ∧
    (∀ i ≤ l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
      x[0] = p + (l - (x[3] - 1)) ∧
        x[1] = k + (l - x[3]) ∧
          x[2] = c + (l - x[3]) ∧
            x[3] ≤ l ∧
              x[5] = mem[x[0] - 1] ∧
                x[6] = mem[x[1]] ∧ x[7] = x[5] ^^^ x[6] ∧ x[3] = x ∧
                iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄ := by
    unfold otpCode
    intros p k c l
    unfold hoareTripleUp
    rintro h_inter h_empty s h_code' h_pc ⟨⟨h_cond, h_I, h_x0, h_x1, h_x2, h_x3LtL, h_x5, h_x6,
      h_x7, h_x3, h_I_pre'⟩, h_terminated⟩
    rw [←h_code']
    have: ({10} : Set UInt64)  = {9 + 1}  := by
      simp
    rw [this]
    apply specification_Increment (dst := 0)
    · simp
    · simp
    · simp
    · simpCurrInstr
    · exact h_pc
    · repeat (constructor <;> try assumption)
      · simp at *
        grind
      · repeat (constructor <;> try assumption)
        · simp only [MState.incPc_increments_pc, MState.getRegisterAt_def,
            MState.addRegister_unfold, t_update_eq, UInt64.add_sub_cancel, MState.getMemoryAt_def]
          exact h_x5
        · repeat (constructor <;> try assumption)



theorem inc_otp_1 : ∀ (p k c l : UInt64),
  (otpCode p k c l)
  ⦃(x[3] > 0 ∧
      (∀ i ≤ l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
        x[0] = p + (l - (x[3] - 1)) ∧
          x[1] = k + (l - x[3]) ∧
            x[2] = c + (l - x[3]) ∧
              x[3] ≤ l ∧
                x[5] = mem[x[0] - 1] ∧
                  x[6] = mem[x[1]] ∧
                  x[7] = x[5] ^^^ x[6] ∧ x[3] = x ∧ iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄
  10 ↦ ⟨{11} | {n | (n ≠ 11)}⟩
  ⦃(x[3] > 0 ∧
      (∀ i ≤ l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
        x[0] = p + (l - (x[3] - 1)) ∧
          x[1] = k + (l - (x[3] - 1)) ∧
            x[2] = c + (l - x[3]) ∧
              x[3] ≤ l ∧
                x[5] = mem[x[0] - 1] ∧
                  x[6] = mem[x[1] - 1] ∧
                  x[7] = x[5] ^^^ x[6] ∧ x[3] = x ∧
                  iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄
    := by
    intros p k c l
    have: ({11}: Set UInt64)  = {10 + 1}  := by
      simp
    rw [this]
    unfold hoareTripleUp
    rintro h_inter h_empty s h_code' h_pc ⟨⟨h_cond, h_I, h_x0, h_x1, h_x2, h_x3LtL, h_x5, h_x6,
      h_x7, h_x3, h_I_pre'⟩, h_terminated⟩
    rw [←h_code']
    apply specification_Increment (dst := 1)
    · simp
    · simp
    · simp
    · simp only [MState.currInstruction_unfold]
      rw [h_code', h_pc]
      unfold otpCode
      simp
    · exact h_pc
    · simp only [MState.incPc_increments_pc, MState.getRegisterAt_def,
        MState.addRegister_unfold, ne_eq, not_false_eq_true, t_update_neq, gt_iff_lt,
        MState.getMemoryAt_def, t_update_eq, UInt64.add_sub_cancel, Bool.not_eq_true,
        show (1 : UInt64) ≠ 0 by decide, show (1 : UInt64) ≠ 2 by decide,
        show (1 : UInt64) ≠ 3 by decide, show (1 : UInt64) ≠ 5 by decide,
        show (1 : UInt64) ≠ 6 by decide, show (1 : UInt64) ≠ 7 by decide] at *
      repeat (constructor <;> try assumption)
      · rw [h_x1, h_x3]
        apply UInt64.add_sub_assoc
        · rw [←h_x3]
          exact h_x3LtL
        · rw [←h_x3]
          simp only [gt_iff_lt]
          exact h_cond
      · repeat (constructor <;> try assumption)

theorem inc_otp_2 {x} : ∀ (p k c l : UInt64),
(otpCode p k c l)
⦃(x[3] > 0 ∧
      (∀ i ≤ l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
        x[0] = p + (l - (x[3] - 1)) ∧
          x[1] = k + (l - (x[3] - 1)) ∧
            x[2] = c + (l - x[3]) ∧
              x[3] ≤ l ∧
                x[5] = mem[x[0] - 1] ∧
                  x[6] = mem[x[1] - 1] ∧
                  x[7] = x[5] ^^^ x[6] ∧ x[3] = x ∧ iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄
  11 ↦ ⟨{12} | {n | (n ≠ 12)}⟩
  ⦃(x[3] > 0 ∧
      (∀ i ≤ l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
        x[0] = p + (l - (x[3] - 1)) ∧
          x[1] = k + (l - (x[3] - 1)) ∧
            x[2] = c + (l - (x[3] - 1)) ∧
              x[3] ≤ l ∧
                x[5] = mem[x[0] - 1] ∧
                  x[6] = mem[x[1] - 1] ∧
                  x[7] = x[5] ^^^ x[6] ∧ x[3] = x ∧
                  iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄
    := by
    unfold otpCode
    intros p k c l
    unfold hoareTripleUp
    rintro h_inter h_empty s h_code' h_pc
      ⟨⟨h_cond, h_I, h_x0, h_x1, h_x2, h_x3LtL, h_x5, h_x6, h_x7, h_x3, h_I_pre'⟩, h_terminated⟩
    rw [←h_code']
    have: ({12}: Set UInt64) = {11 + 1}  := by
      simp
    rw [this]
    apply specification_Increment (dst := 2)
    · simp
    · simp
    · simp
    · simpCurrInstr
    · exact h_pc
    · simp only [MState.incPc_increments_pc, MState.getRegisterAt_def,
        MState.addRegister_unfold, ne_eq, not_false_eq_true, t_update_neq, gt_iff_lt,
        MState.getMemoryAt_def, t_update_eq, Bool.not_eq_true,
        show (2 : UInt64) ≠ 0 by decide, show (2 : UInt64) ≠ 1 by decide,
        show (2 : UInt64) ≠ 3 by decide, show (2 : UInt64) ≠ 5 by decide,
        show (2 : UInt64) ≠ 6 by decide, show (2 : UInt64) ≠ 7 by decide] at *
      repeat (constructor <;> try assumption)
      · rw [h_x2, h_x3]
        apply UInt64.add_sub_assoc
        · rw [←h_x3]
          exact h_x3LtL
        · rw [←h_x3]
          simp only [gt_iff_lt]
          exact h_cond
      · repeat (constructor <;> try assumption)


theorem dec_otp : ∀ (p k c l : UInt64),
  (otpCode p k c l)
  ⦃(x[3] > 0 ∧
      (∀ i ≤ l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
        x[0] = p + (l - (x[3] - 1)) ∧
          x[1] = k + (l - (x[3] - 1)) ∧
            x[2] = c + (l - (x[3] - 1)) ∧
              x[3] ≤ l ∧
                x[5] = mem[x[0] - 1] ∧
                  x[6] = mem[x[1] - 1] ∧ x[7] = x[5] ^^^ x[6] ∧ x[3] = x ∧ iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄
  12 ↦ ⟨{13} | {n | (n ≠ 12 + 1)}⟩
  ⦃((∀ i < l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
      x[0] = p + (l - x[3]) ∧
        x[1] = k + (l - x[3]) ∧
          x[2] = c + (l - x[3]) ∧
            x[3] ≤ l ∧
              x[5] = mem[x[0] - 1] ∧
                x[6] = mem[x[1] - 1] ∧ x[7] = x[5] ^^^ x[6] ∧ x[3] < x ∧ iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄ := by
    unfold otpCode
    intros p k c l
    unfold hoareTripleUp
    rintro h_inter h_empty s h_code' h_pc
      ⟨⟨h_cond, h_I, h_x0, h_x1, h_x2, h_x3LtL, h_x5, h_x6, h_x7, h_x3, h_I_pre'⟩, h_terminated⟩
    rw [←h_code']
    have: ({13} : Set UInt64) = {12 + 1}  := by
      simp
    rw [this]
    apply specification_Decrement (dst := 3)
    · simp
    · simp
    · simp
    · simpCurrInstr
    · exact h_pc
    · simp only [MState.incPc_increments_pc, MState.getRegisterAt_def,
        MState.addRegister_unfold, t_update_eq, MState.getMemoryAt_def, ne_eq, not_false_eq_true,
        t_update_neq, Bool.not_eq_true, show (3 : UInt64) ≠ 0 by decide,
        show (3 : UInt64) ≠ 1 by decide, show (3 : UInt64) ≠ 2 by decide,
        show (3 : UInt64) ≠ 5 by decide, show (3 : UInt64) ≠ 6 by decide,
        show (3 : UInt64) ≠ 7 by decide] at *
      repeat (constructor <;> try assumption)
      · intros i h_I'
        have: i ≤ l - TMap.get s.registers 3  := by
          grind
        specialize h_I i this
        exact h_I
      · repeat (constructor <;> try assumption)
        · grind only
        · repeat (constructor <;> try assumption)
          rw [←h_x3]
          grind



theorem j_otp : ∀ (p k c l : UInt64),
(otpCode p k c l)
⦃((∀ i < l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
      x[0] = p + (l - x[3]) ∧
        x[1] = k + (l - x[3]) ∧
          x[2] = c + (l - x[3]) ∧
            x[3] ≤ l ∧
              x[5] = mem[x[0] - 1] ∧
                x[6] = mem[x[1] - 1] ∧ x[7] = x[5] ^^^ x[6] ∧ x[3] < x ∧ iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄
  13 ↦ ⟨{4} ∪ {14} |
  {n | (n ≠ 4)} \ {14}⟩
  ⦃x[3] < x ∧
      (((∀ i < l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
            x[0] = p + (l - x[3]) ∧ x[1] = k + (l - x[3]) ∧ x[2] = c + (l - x[3]) ∧ x[3] ≤ l ∧
              iPre' p k c l) ∧
          ¬⸨terminated⸩ = true) ∧
        ⸨pc⸩ = 4⦄ := by
  unfold otpCode
  intros p k c l
  unfold hoareTripleUp
  rintro h_inter h_empty s h_code h_pc ⟨⟨h_cond, h_I, h_x0, h_x1, h_x2, h_x3LtL, h_x5, h_x6, h_x7,
    h_x3, h_I_pre'⟩, h_terminated⟩
  -- rw [← s_code]
  apply BL_TO_WL (L_w := {4}) (l := 13) (P := ⦃((∀ i < l - x[3],
    mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
      x[0] = p + (l - x[3]) ∧
        x[1] = k + (l - x[3]) ∧
          x[2] = c + (l - x[3]) ∧
            x[3] ≤ l ∧
              x[5] = mem[x[0] - 1] ∧
                x[6] = mem[x[1] - 1] ∧ x[7] = x[5] ^^^ x[6] ∧ x[3] < x ∧ iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄)
    <;> try assumption
  · simp
  · simp
  · simp
  · unfold hoareTripleUp
    rintro h_inter h_empty s h_code' h_pc ⟨⟨h_I, h_x0, h_x1, h_x2, h_x3LtL, h_x5, h_x6, h_x7,
      h_x3, h_I_pre'⟩, h_terminated⟩
    rw [←h_code']
    have: (∃ s',
        weak s s' {4} {n | (n ≠ 4)} s.code ∧
          (fun st ↦
                (st.getRegisterAt 3 < x ∧
                      (∀ i < l - st.getRegisterAt 3,
                        st.getMemoryAt (c + i) = st.getMemoryAt (p + i)
                          ^^^ st.getMemoryAt (k + i)) ∧
                          st.getRegisterAt 0 = p + (l - st.getRegisterAt 3) ∧
                            st.getRegisterAt 1 = k + (l - st.getRegisterAt 3) ∧
                              st.getRegisterAt 2 = c + (l - st.getRegisterAt 3) ∧
                                st.getRegisterAt 3 ≤ l ∧ iPre' p k c l) ∧
                    ¬st.terminated = true ∧ st.pc = 4)
              s' ∧
            s'.pc ∉ {n | (n ≠ 4)}) →
        (∃ s',
        weak s s' {4} {n | (n ≠ 4)} s.code ∧
          (fun st ↦
                st.getRegisterAt 3 < x ∧
                  (((∀ i < l - st.getRegisterAt 3,
                          st.getMemoryAt (c + i) = st.getMemoryAt (p + i)
                            ^^^ st.getMemoryAt (k + i)) ∧
                        st.getRegisterAt 0 = p + (l - st.getRegisterAt 3) ∧
                          st.getRegisterAt 1 = k + (l - st.getRegisterAt 3) ∧
                            st.getRegisterAt 2 = c + (l - st.getRegisterAt 3) ∧
                              st.getRegisterAt 3 ≤ l ∧ iPre' p k c l) ∧
                      ¬st.terminated = true) ∧
                    st.pc = 4)
              s' ∧
            s'.pc ∉ {n | (n ≠ 4)}) := by
            intros h
            rcases h with ⟨s', ⟨h_weak, pre⟩⟩
            simp only [
              MState.getMemoryAt_def, MState.getRegisterAt_def,
              ne_eq,
              Bool.not_eq_true, Set.mem_setOf_eq, Decidable.not_not] at pre
            rcases pre with ⟨⟨⟨h_var, h_I⟩, h_terminated, _⟩, _⟩
            simp only [ne_eq, MState.getRegisterAt_def, MState.getMemoryAt_def, Bool.not_eq_true,
              Set.mem_setOf_eq, Decidable.not_not]
            simp at h_weak
            exists s'
    apply this
    clear this
    apply specification_Jump' (pc := 13) (newPc := 4) (label := ".loop")
    · simp
    · simp
    · simp
    · simpCurrInstr
    · assumption
    · repeat (constructor <;> try assumption)
      unfold MState.getLabelAt
      rw [h_code']
      simp
  · (repeat constructor <;> try assumption)


theorem beqz_otp : ∀ (p k c l : UInt64),
  (otpCode p k c l)
  ⦃(x[3] > 0 ∧
      (∀ i < l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
        x[0] = p + (l - x[3]) ∧ x[1] = k + (l - x[3]) ∧
          x[2] = c + (l - x[3]) ∧ x[3] ≤ l ∧ x[3] = x ∧
            iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄
  4 ↦ ⟨{5} | {n | n ≤ 4} ∪ {n | n > 5}⟩
  ⦃(x[3] > 0 ∧
      (∀ i < l - x[3], mem[c + i] = mem[p + i] ^^^ mem[k + i]) ∧
        x[0] = p + (l - x[3]) ∧
          x[1] = k + (l - x[3]) ∧
            x[2] = c + (l - x[3]) ∧ x[3] ≤ l ∧ x[3] = x ∧ iPre' p k c l) ∧
    ¬⸨terminated⸩ = true⦄ := by
  unfold otpCode
  intros p k c l
  -- applySpec specification_JumpEqZero_false (l := 4) (r := 3) (label := "finish")
  unfold hoareTripleUp
  rintro h_inter h_empty s h_code' h_pc ⟨⟨h_cond, h_I, h_x0, h_x1, h_x2, h_x3LeL, h_x3, h_I_pre'⟩,
    h_terminated⟩
  rw [←h_code']
  have: ({n | n ≤ 4} ∪ {n | n > 5}) = {n:UInt64| n ≠ 4 + 1} := by
    ext a
    simp only [gt_iff_lt, Set.mem_union, Set.mem_setOf_eq, UInt64.reduceAdd, ne_eq]
    apply Iff.intro
    · intros h
      cases h with
      | inl v =>
        intros neq
        rw [neq] at v
        contradiction
      | inr v =>
        intros neq
        rw [neq] at v
        contradiction
    · intros h
      push Not at h
      -- rw [←UInt64.lt_toNat_iff]
      by_contra h'
      push Not at h'
      simp only [UInt64.not_le, UInt64.not_lt] at h'
      rcases h' with ⟨h_1, h_2⟩
      have h_eq : a = 5 := by
        -- rw [UInt64.ext_iff]
        apply UInt64.le_antisymm
        · exact h_2
        · grind
      rw [h_eq] at h
      contradiction
  rw [this]
  apply specification_JumpEqZero_false (pc := 4) (reg := 3) (label := "finish")
  · simp
  · simp
  · simp
  · simpCurrInstr
  · assumption
  · repeat (constructor <;> try assumption)
    apply UInt64.gt_zero_neq_zero
    exact h_cond
