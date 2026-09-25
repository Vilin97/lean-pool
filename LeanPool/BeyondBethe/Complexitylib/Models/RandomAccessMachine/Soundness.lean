/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Internal
public import Mathlib.Data.Nat.Size

/-!
# Why the RAM must use logarithmic cost: a formal soundness theorem

This module turns the model's central design decision into a theorem. A RAM
stores unbounded natural numbers in each register. Under the **unit-cost**
measure (one time unit per instruction, `RAM.unitTimeUpto`) a program can
repeatedly *square* a register, reaching `2 ^ (2 ^ k)` in `k + 1` steps. That
number has `2 ^ k + 1` binary digits, so any Turing machine needs at least
`2 ^ k` steps merely to write it: unit-cost RAM time is super-polynomially
stronger than Turing time, and the two models are **not** polynomially
equivalent.

`RAM.logGap_squaring` proves exactly this gap for the squaring program family
`RAM.sqProg`: on the same run, the unit time is `k + 1` while the logarithmic
time (`RAM.logTimeUpto`, which charges each instruction the bit-length of the
numbers it manipulates) is at least `2 ^ k`. This is why the library adopts the
logarithmic cost measure and never the unit-cost one — the difference is not a
convention but the boundary between a sound Turing-equivalent model and a
"reward-hacked" one that decides more than it should in polynomial time.
-/


@[expose] public section

namespace Complexity

namespace RAM

/-- The `k`-fold squaring program: load `2` into register `1`, then square
    register `1` a total of `k` times. After `j + 1` steps register `1` holds
    `2 ^ (2 ^ j)`. -/
def sqProg (k : ℕ) : Program :=
  Instr.imm 1 2 :: List.replicate k (Instr.mul 1 1 1)

/-- The start configuration for the squaring family: program counter `0`, all
    registers `0`. -/
def sqStart : Cfg := ⟨0, fun _ => 0⟩

/-- The configuration after `j + 1` steps of `sqProg`: program counter `j + 1`,
    register `1` holding `2 ^ (2 ^ j)`, all other registers `0`. -/
private def sqCfg (j : ℕ) : Cfg := ⟨j + 1, fun i => if i = 1 then 2 ^ (2 ^ j) else 0⟩

private theorem sqProg_length (k : ℕ) : (sqProg k).length = k + 1 := by
  simp [sqProg]

private theorem sqProg_getElem_zero (k : ℕ) :
    (sqProg k)[(0 : ℕ)]? = some (Instr.imm 1 2) := rfl

private theorem sqProg_getElem_succ {k j : ℕ} (hj : j < k) :
    (sqProg k)[j + 1]? = some (Instr.mul 1 1 1) := by
  simp only [sqProg, List.getElem?_cons_succ, List.getElem?_replicate, ite_eq_left hj]

/-- Squaring `2 ^ (2 ^ j)` yields `2 ^ (2 ^ (j + 1))`. -/
private theorem sq_pow (j : ℕ) : 2 ^ 2 ^ j * 2 ^ 2 ^ j = 2 ^ 2 ^ (j + 1) := by
  rw [← pow_add]
  congr 1
  rw [pow_succ]
  ring

/-- One step from the start runs the `imm` instruction, reaching `sqCfg 0`. -/
private theorem step_sqStart (k : ℕ) : step (sqProg k) sqStart = sqCfg 0 := by
  have hcur : curInstr (sqProg k) sqStart = Instr.imm 1 2 := by
    unfold curInstr; rw [show sqStart.pc = 0 from rfl, sqProg_getElem_zero]; rfl
  unfold step
  rw [hcur]
  ext i
  · rfl
  · show Function.update sqStart.regs 1 2 i = (sqCfg 0).regs i
    by_cases hi : i = 1
    · subst hi; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hi]
      simp only [sqStart, sqCfg, ite_eq_right hi]

/-- One squaring step from `sqCfg j` reaches `sqCfg (j + 1)`, provided the
    `(j + 1)`-th instruction is a `mul` (i.e. `j < k`). -/
private theorem step_sqCfg {k j : ℕ} (hj : j < k) :
    step (sqProg k) (sqCfg j) = sqCfg (j + 1) := by
  have hcur : curInstr (sqProg k) (sqCfg j) = Instr.mul 1 1 1 := by
    unfold curInstr
    rw [show (sqCfg j).pc = j + 1 from rfl, sqProg_getElem_succ hj]; rfl
  unfold step
  rw [hcur]
  ext i
  · rfl
  · show Function.update (sqCfg j).regs 1 ((sqCfg j).regs 1 * (sqCfg j).regs 1) i
        = (sqCfg (j + 1)).regs i
    by_cases hi : i = 1
    · subst hi; rw [Function.update_self]; exact sq_pow j
    · rw [Function.update_of_ne hi]
      simp only [sqCfg, ite_eq_right hi]

/-- The run invariant: `j + 1` steps of `sqProg k` from the start reach
    `sqCfg j`, for every `j ≤ k`. -/
private theorem sqRun {k : ℕ} : ∀ j, j ≤ k → run (sqProg k) (j + 1) sqStart = sqCfg j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [run_one, step_sqStart]
  | succ j ih =>
    intro hj
    rw [run_succ_step, ih (by omega), step_sqCfg (by omega)]

/-- The program counter after `j` steps is exactly `j`, for `j ≤ k`. -/
private theorem sqRun_pc {k : ℕ} {j : ℕ} (hj : j ≤ k) :
    (run (sqProg k) j sqStart).pc = j := by
  cases j with
  | zero => rfl
  | succ j => rw [sqRun j (by omega)]; rfl

/-- No halt occurs during the first `k + 1` steps: every visited program counter
    `≤ k` points at an `imm` or `mul` instruction. -/
private theorem sqRun_not_halted {k : ℕ} {j : ℕ} (hj : j ≤ k) :
    ¬ Halted (sqProg k) (run (sqProg k) j sqStart) := by
  unfold Halted curInstr
  rw [sqRun_pc hj]
  cases j with
  | zero => rw [sqProg_getElem_zero]; decide
  | succ j => rw [sqProg_getElem_succ (by omega)]; decide

/-- The **unit-vs-logarithmic gap** for the squaring family. On the run of the
    `k`-fold squaring program `sqProg k` for `k + 1` steps:

    * the machine halts;
    * the **unit** time is `k + 1` (linear in `k`);
    * the **logarithmic** time is at least `2 ^ k` (exponential in `k`).

    Hence any complexity measure based on unit cost differs super-polynomially
    from logarithmic cost, and only the logarithmic measure is polynomially
    related to Turing-machine time. This is the formal justification for the
    library's cost convention. -/
theorem logGap_squaring {k : ℕ} (hk : 1 ≤ k) :
    ∃ (P : Program) (c : Cfg),
      Halted P (run P (k + 1) c) ∧
      unitTimeUpto P (k + 1) c = k + 1 ∧
      2 ^ k ≤ logTimeUpto P (k + 1) c := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨sqProg (m + 1), sqStart, ?_, ?_, ?_⟩
  · -- Halted after m + 2 steps: program counter reaches the end.
    rw [sqRun (m + 1) (le_refl _)]
    show curInstr (sqProg (m + 1)) (sqCfg (m + 1)) = Instr.halt
    unfold curInstr
    have hlen : (sqProg (m + 1)).length ≤ m + 2 := by rw [sqProg_length]
    rw [show (sqCfg (m + 1)).pc = m + 2 from rfl, List.getElem?_eq_none hlen]
    rfl
  · -- Unit time is exactly the fuel: no halt in the first m + 2 steps.
    exact unitTimeUpto_eq_of_not_halted _ _ _ (fun j hj => sqRun_not_halted (by omega))
  · -- Logarithmic time is at least 2 ^ (m + 1): the final squaring step alone
    -- costs at least the bit-length of 2 ^ (2 ^ (m + 1)) = 2 ^ (m + 1) + 1.
    have hsplit : logTimeUpto (sqProg (m + 1)) (m + 1 + 1) sqStart =
        logTimeUpto (sqProg (m + 1)) (m + 1) sqStart +
          logTimeUpto (sqProg (m + 1)) 1 (run (sqProg (m + 1)) (m + 1) sqStart) :=
      logTimeUpto_add _ (m + 1) 1 sqStart
    have hcfg : run (sqProg (m + 1)) (m + 1) sqStart = sqCfg m := sqRun m (by omega)
    have hnh : ¬ Halted (sqProg (m + 1)) (sqCfg m) := by
      rw [← hcfg]; exact sqRun_not_halted (by omega)
    have hcur : curInstr (sqProg (m + 1)) (sqCfg m) = Instr.mul 1 1 1 := by
      unfold curInstr
      rw [show (sqCfg m).pc = m + 1 from rfl, sqProg_getElem_succ (by omega)]; rfl
    -- Evaluate the one-step logarithmic cost of the final `mul`.
    have hstep1 : logTimeUpto (sqProg (m + 1)) 1 (sqCfg m) =
        stepLogCost (sqProg (m + 1)) (sqCfg m) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, logTimeUpto_succ, ite_eq_right hnh, logTimeUpto_zero,
        Nat.add_zero]
    have hval : (sqCfg m).regs 1 = 2 ^ 2 ^ m := by simp [sqCfg]
    have hcost : stepLogCost (sqProg (m + 1)) (sqCfg m) =
        bitlen (2 ^ 2 ^ m) + bitlen (2 ^ 2 ^ m) + bitlen (2 ^ 2 ^ (m + 1)) + 1 := by
      unfold stepLogCost
      rw [hcur]
      simp only [Instr.logCost, hval, sq_pow]
    have hbit : bitlen (2 ^ 2 ^ (m + 1)) = 2 ^ (m + 1) + 1 := by
      unfold bitlen; rw [Nat.size_pow]
    rw [hsplit, hcfg, hstep1, hcost, hbit]
    omega

end RAM

end Complexity
