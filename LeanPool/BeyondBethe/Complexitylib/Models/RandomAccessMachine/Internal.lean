/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Defs
public import Mathlib.Tactic.Ring.RingNF

/-!
# Random access machines: operational metatheory (proof internals)

This module proves the structural facts about `RAM.run`, `RAM.logTimeUpto`,
`RAM.unitTimeUpto`, and register support that the surface theorems rely on:

* **Unfolding lemmas** and the fixed-point behaviour of a halted configuration
  (`step_halted`, `run_halted`, `logTimeUpto_halted`, `unitTimeUpto_halted`).
* **Run/cost algebra**: `run_one`, `run_succ_step`, and the additive
  decompositions `run_add`, `logTimeUpto_add`, `unitTimeUpto_add`, giving
  stationarity of the run and cost once halted, and monotonicity of the cost
  in the fuel.
* **Cost lower bounds**: every executed step costs at least one time unit
  (`Instr.one_le_logCost`), so the step count never exceeds the logarithmic
  time (`unitTimeUpto_le_logTimeUpto`).
* **Finite support**: the register file has finite support along any run from
  a finitely-supported start (`run_finiteSupport`), which is what makes the
  `finsum`-based space measure `RAM.Cfg.space` a genuine finite sum.

Not intended for human audit: the definitions in `Defs.lean` and the theorem
statements in the surface module carry the mathematical content.
-/


public section

namespace Complexity

namespace RAM

variable (P : Program)

/-! ### Unfolding lemmas -/

@[simp] theorem run_zero (c : Cfg) : run P 0 c = c := rfl

@[simp] theorem logTimeUpto_zero (c : Cfg) : logTimeUpto P 0 c = 0 := rfl

@[simp] theorem unitTimeUpto_zero (c : Cfg) : unitTimeUpto P 0 c = 0 := rfl

theorem run_succ (fuel : ℕ) (c : Cfg) :
    run P (fuel + 1) c = if Halted P c then c else run P fuel (step P c) := rfl

theorem logTimeUpto_succ (fuel : ℕ) (c : Cfg) :
    logTimeUpto P (fuel + 1) c =
      if Halted P c then 0 else stepLogCost P c + logTimeUpto P fuel (step P c) := rfl

theorem unitTimeUpto_succ (fuel : ℕ) (c : Cfg) :
    unitTimeUpto P (fuel + 1) c =
      if Halted P c then 0 else 1 + unitTimeUpto P fuel (step P c) := rfl

/-! ### Halted configurations are fixed points -/

/-- Stepping a halted configuration is a no-op: `halt` leaves everything fixed. -/
theorem step_halted {c : Cfg} (h : Halted P c) : step P c = c := by
  unfold step
  rw [show curInstr P c = Instr.halt from h]
  rfl

/-- Running a halted configuration for any amount of fuel leaves it fixed. -/
theorem run_halted {c : Cfg} (h : Halted P c) (fuel : ℕ) : run P fuel c = c := by
  cases fuel with
  | zero => rfl
  | succ f => rw [run_succ, ite_eq_left h]

/-- A halted configuration accumulates no logarithmic time. -/
theorem logTimeUpto_halted {c : Cfg} (h : Halted P c) (fuel : ℕ) :
    logTimeUpto P fuel c = 0 := by
  cases fuel with
  | zero => rfl
  | succ f => rw [logTimeUpto_succ, ite_eq_left h]

/-- A halted configuration accumulates no unit time. -/
theorem unitTimeUpto_halted {c : Cfg} (h : Halted P c) (fuel : ℕ) :
    unitTimeUpto P fuel c = 0 := by
  cases fuel with
  | zero => rfl
  | succ f => rw [unitTimeUpto_succ, ite_eq_left h]

/-! ### Run/cost algebra -/

/-- One unit of fuel performs exactly one step (a no-op if already halted). -/
theorem run_one (c : Cfg) : run P 1 c = step P c := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ]
  by_cases h : Halted P c
  · rw [ite_eq_left h, step_halted P h]
  · rw [ite_eq_right h, run_zero]

/-- The run decomposes additively: `a + b` steps is `b` steps after `a` steps. -/
theorem run_add (a b : ℕ) (c : Cfg) : run P (a + b) c = run P b (run P a c) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, run_succ, run_succ]
    by_cases h : Halted P c
    · rw [ite_eq_left h, ite_eq_left h]
      exact (run_halted P h b).symm
    · rw [ite_eq_right h, ite_eq_right h]
      exact ih (step P c)

/-- Running `n + 1` steps is one step after running `n` steps. -/
theorem run_succ_step (n : ℕ) (c : Cfg) : run P (n + 1) c = step P (run P n c) := by
  rw [run_add P n 1, run_one]

/-- Logarithmic time decomposes additively along the run. -/
theorem logTimeUpto_add (a b : ℕ) (c : Cfg) :
    logTimeUpto P (a + b) c =
      logTimeUpto P a c + logTimeUpto P b (run P a c) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, logTimeUpto_succ, logTimeUpto_succ, run_succ]
    by_cases h : Halted P c
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, logTimeUpto_halted P h b]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, ih (step P c)]
      ring

/-- Unit time decomposes additively along the run. -/
theorem unitTimeUpto_add (a b : ℕ) (c : Cfg) :
    unitTimeUpto P (a + b) c =
      unitTimeUpto P a c + unitTimeUpto P b (run P a c) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, unitTimeUpto_succ, unitTimeUpto_succ, run_succ]
    by_cases h : Halted P c
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, unitTimeUpto_halted P h b]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, ih (step P c)]
      ring

/-- Once halted after `f` steps, extra fuel does not change the configuration. -/
theorem run_eq_of_halted_le {c : Cfg} {f f' : ℕ} (hle : f ≤ f')
    (h : Halted P (run P f c)) : run P f' c = run P f c := by
  obtain ⟨g, rfl⟩ := Nat.le.dest hle
  rw [run_add]
  exact run_halted P h g

/-- Once halted after `f` steps, extra fuel does not change the logarithmic time. -/
theorem logTimeUpto_eq_of_halted_le {c : Cfg} {f f' : ℕ} (hle : f ≤ f')
    (h : Halted P (run P f c)) : logTimeUpto P f' c = logTimeUpto P f c := by
  obtain ⟨g, rfl⟩ := Nat.le.dest hle
  rw [logTimeUpto_add, logTimeUpto_halted P h g, Nat.add_zero]

/-- Logarithmic time is monotone in the fuel. -/
theorem logTimeUpto_mono {c : Cfg} {f f' : ℕ} (hle : f ≤ f') :
    logTimeUpto P f c ≤ logTimeUpto P f' c := by
  obtain ⟨g, rfl⟩ := Nat.le.dest hle
  rw [logTimeUpto_add]
  exact Nat.le_add_right _ _

/-- Unit time is monotone in the fuel. -/
theorem unitTimeUpto_mono {c : Cfg} {f f' : ℕ} (hle : f ≤ f') :
    unitTimeUpto P f c ≤ unitTimeUpto P f' c := by
  obtain ⟨g, rfl⟩ := Nat.le.dest hle
  rw [unitTimeUpto_add]
  exact Nat.le_add_right _ _

/-! ### Cost lower bounds -/

/-- Every instruction costs at least one time unit under the logarithmic
    measure (the base cost). -/
theorem Instr.one_le_logCost (i : Instr) (c : Cfg) : 1 ≤ i.logCost c := by
  cases i <;> simp only [Instr.logCost] <;> omega

/-- Every executed step costs at least one time unit. -/
theorem one_le_stepLogCost (c : Cfg) : 1 ≤ stepLogCost P c :=
  Instr.one_le_logCost _ _

/-- The number of steps taken never exceeds the logarithmic time: each step
    costs at least one time unit, so log-time dominates the step count. -/
theorem unitTimeUpto_le_logTimeUpto (fuel : ℕ) (c : Cfg) :
    unitTimeUpto P fuel c ≤ logTimeUpto P fuel c := by
  induction fuel generalizing c with
  | zero => simp
  | succ f ih =>
    rw [unitTimeUpto_succ, logTimeUpto_succ]
    by_cases h : Halted P c
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      have h1 : 1 ≤ stepLogCost P c := one_le_stepLogCost P c
      have h2 := ih (step P c)
      omega

/-- If no halt occurs in the first `fuel` steps, the unit time is exactly the
    fuel (every step is counted). -/
theorem unitTimeUpto_eq_of_not_halted (c : Cfg) (fuel : ℕ)
    (h : ∀ j < fuel, ¬ Halted P (run P j c)) : unitTimeUpto P fuel c = fuel := by
  induction fuel generalizing c with
  | zero => simp
  | succ f ih =>
    have h0 : ¬ Halted P c := h 0 (Nat.succ_pos f)
    rw [unitTimeUpto_succ, ite_eq_right h0]
    have hrec : unitTimeUpto P f (step P c) = f := by
      apply ih
      intro j hj
      have hstep : run P j (step P c) = run P (j + 1) c := by
        rw [run_succ, ite_eq_right h0]
      rw [hstep]
      exact h (j + 1) (by omega)
    rw [hrec]
    omega

/-! ### Finite support of the register file -/

/-- The support of an updated function is contained in the support of the
    original with the written index inserted. -/
theorem support_update_subset (f : ℕ → ℕ) (i v : ℕ) :
    Function.support (Function.update f i v) ⊆ insert i (Function.support f) := by
  intro j hj
  simp only [Function.mem_support] at hj
  by_cases hji : j = i
  · subst hji; exact Set.mem_insert _ _
  · rw [Function.update_of_ne hji] at hj
    exact Set.mem_insert_of_mem _ hj

/-- The initial register file has finite support: only registers `0 … |x|` can
    be nonzero. -/
theorem initRegs_finiteSupport (x : List Bool) :
    (Function.support (initRegs x)).Finite := by
  apply Set.Finite.subset (Finset.range (x.length + 1)).finite_toSet
  intro i hi
  simp only [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  rw [not_lt] at hlt
  apply hi
  have hi0 : i ≠ 0 := by omega
  simp only [initRegs, hi0, ite_false, List.getElem?_eq_none (show x.length ≤ i - 1 by omega)]

/-- One instruction preserves finite support of the register file: each
    instruction writes at most one register. -/
theorem stepInstr_finiteSupport (i : Instr) (c : Cfg)
    (h : (Function.support c.regs).Finite) :
    (Function.support (stepInstr i c).regs).Finite := by
  cases i with
  | imm d v => exact (h.insert d).subset (support_update_subset c.regs d v)
  | add d s t => exact (h.insert d).subset (support_update_subset c.regs d _)
  | sub d s t => exact (h.insert d).subset (support_update_subset c.regs d _)
  | mul d s t => exact (h.insert d).subset (support_update_subset c.regs d _)
  | load d a => exact (h.insert d).subset (support_update_subset c.regs d _)
  | store a s => exact (h.insert (c.regs a)).subset (support_update_subset c.regs (c.regs a) _)
  | jz s tgt => dsimp only [stepInstr]; split <;> exact h
  | jmp tgt => exact h
  | halt => exact h

/-- One step preserves finite support of the register file. -/
theorem step_finiteSupport (c : Cfg) (h : (Function.support c.regs).Finite) :
    (Function.support (step P c).regs).Finite :=
  stepInstr_finiteSupport _ c h

/-- Finite support of the register file is a run invariant. -/
theorem run_finiteSupport (fuel : ℕ) (c : Cfg)
    (h : (Function.support c.regs).Finite) :
    (Function.support (run P fuel c).regs).Finite := by
  induction fuel generalizing c with
  | zero => simpa using h
  | succ f ih =>
    rw [run_succ]
    split
    · exact h
    · exact ih (step P c) (step_finiteSupport P c h)

/-- Finite support along any run started from an initial configuration. This
    guarantees `RAM.Cfg.space` is a genuine finite sum, not the `finsum`
    fallback value `0`. -/
theorem run_initCfg_finiteSupport (fuel : ℕ) (x : List Bool) :
    (Function.support (run P fuel (initCfg x)).regs).Finite :=
  run_finiteSupport P fuel (initCfg x) (initRegs_finiteSupport x)

end RAM

end Complexity
