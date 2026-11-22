/-
Copyright (c) 2026 Weighted Horn Cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weighted Horn Cores contributors
-/
module

public import LeanPool.WeightedHornCores.Budget
public import LeanPool.WeightedHornCores.Charging
public import LeanPool.WeightedHornCores.Semantics
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The size of a weighted Horn contradiction

Test the formula on the assignment consisting of atoms forced by small subformulas.
Increase the cardinality budget linearly from `p * 2^j` to `p * 2^(j+1)` over each block
of `p` tests. Once a positive rule fails, adding it to the certificates for its premises
repairs it within one test for a fact or unary rule, and within `p+1` tests for a binary
rule. A failing denial yields a core immediately. Summing the loss over all tests forces
a denial to fail before the cardinality budget becomes large.
-/

@[expose] public section

namespace WeightedHornCores

variable {α : Type*}

/-- Weight of the clauses falsified by one assignment. -/
noncomputable def violationWeight (F : Finset (Clause α)) (w : Clause α → ℝ) (s : Set α) : ℝ := by
  classical
  exact ∑ c ∈ F, if ¬ c.Holds s then w c else 0

/-- Positive rules with exactly two distinct premises are the branching rules. -/
def Clause.Branches (c : Clause α) : Prop := c.head.isSome = true ∧ c.body.card = 2

/-- Total weight of branching rules. Denials never contribute. -/
noncomputable def branchingWeight (F : Finset (Clause α)) (w : Clause α → ℝ) : ℝ := by
  classical
  exact ∑ c ∈ F, if c.Branches then w c else 0

private noncomputable def duration (p : ℕ) (c : Clause α) : ℕ := by
  classical
  exact if c.Branches then p + 1 else 1

private theorem sum_duration (F : Finset (Clause α)) (w : Clause α → ℝ) (p : ℕ) :
    (∑ c ∈ F, (duration p c : ℝ) * w c) = (∑ c ∈ F, w c) + p * branchingWeight F w := by
  classical
  rw [branchingWeight, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : c.Branches <;> simp [duration, h, add_mul, add_comm]

private theorem capacity_rule {p : ℕ} (hp : 0 < p) (t : ℕ) {c : Clause α} {x : α}
    (hh : c.head = some x) (hb : c.body.card ≤ 2) :
    1 + c.body.card * capacity p t ≤ capacity p (t + duration p c) := by
  classical
  by_cases h : c.body.card = 2
  · have hbr : c.Branches := ⟨by simp [hh], h⟩
    simpa [duration, hbr, h, Nat.add_comm 1] using double_capacity_le hp t
  · have hbr : ¬ c.Branches := fun H => h H.2
    have hone : c.body.card ≤ 1 := by omega
    have hmul := Nat.mul_le_mul_right (capacity p t) hone
    simp only [one_mul] at hmul
    simp only [duration, ite_eq_right hbr]
    have := succ_capacity_le hp t
    omega

private theorem positive_repaired {F : Finset (Clause α)} {c : Clause α} {p i j : ℕ}
    {x : α} (hp : 0 < p) (hc : c ∈ F) (hh : c.head = some x) (hb : c.body.card ≤ 2)
    (hi : ¬ c.Holds (Forced F (capacity p i))) (hj : i + duration p c ≤ j) :
    c.Holds (Forced F (capacity p j)) := by
  classical
  have ready : ∀ y ∈ c.body, y ∈ Forced F (capacity p i) := by
    by_contra h
    exact hi fun hbody => False.elim (h hbody)
  intro _
  rw [hh]
  exact forced_mono ((capacity_rule hp i hh hb).trans (capacity_mono hp hj))
    (force_head hc hh ready)

/-- If the total duration-weighted charge cannot pay for `H+1` failed tests, one of
the assignments up to time `H` exposes a denial with small premise certificates. -/
theorem exists_core_of_horizon (F : Finset (Clause α)) (w : Clause α → ℝ) (τ : ℝ) (a p H : ℕ)
    (hp : 0 < p) (hw : ∀ c ∈ F, 0 ≤ w c)
    (hpos : ∀ c ∈ F, c.head.isSome = true → c.body.card ≤ 2)
    (hneg : ∀ c ∈ F, c.head = none → c.body.card ≤ a)
    (hgap : ∀ s, τ ≤ violationWeight F w s)
    (hcharge : (∑ c ∈ F, w c) + p * branchingWeight F w < ((H + 1 : ℕ) : ℝ) * τ) :
    ∃ K ⊆ F, K.card ≤ 1 + a * capacity p H ∧ ¬ ∃ s, Models K s := by
  classical
  let bad (t : ℕ) (c : Clause α) := ¬ c.Holds (Forced F (capacity p t))
  by_contra noCore
  have hcount (c : Clause α) (hc : c ∈ F) :
      ((Finset.range (H + 1)).filter (fun t => bad t c)).card ≤ duration p c := by
    apply card_le_of_close
    intro i hi hbad j _ hij
    cases hh : c.head with
    | some x => exact fun hj => hj (positive_repaired hp hc hh (hpos c hc (by simp [hh])) hbad hij)
    | none =>
      have ready : ∀ y ∈ c.body, y ∈ Forced F (capacity p i) := by
        by_contra h
        exact hbad fun hbody => False.elim (h hbody)
      obtain ⟨K, hK, hsize, hunsat⟩ := core_of_denial hc hh ready
      have htime : i ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hcap := capacity_mono hp htime
      have hcard := hsize.trans (Nat.add_le_add_left (Nat.mul_le_mul (hneg c hc hh) hcap) 1)
      exact (noCore ⟨K, hK, hcard, hunsat⟩).elim
  have hclock := weighted_clock_bound F w (duration p) bad (H+1) τ hw (fun t _ => hgap _) hcount
  rw [sum_duration] at hclock
  exact hcharge.not_ge hclock

/-- Integer-parameter form of the core bound. `τ` is any positive lower bound for the
loss on every assignment, not an assumed certificate of unsatisfiability. -/
theorem exists_core_of_budgets (F : Finset (Clause α)) (w : Clause α → ℝ) (τ : ℝ) (a p q : ℕ)
    (hτ : 0 < τ) (hp : 0 < p) (hw : ∀ c ∈ F, 0 ≤ w c)
    (hpos : ∀ c ∈ F, c.head.isSome = true → c.body.card ≤ 2)
    (hneg : ∀ c ∈ F, c.head = none → c.body.card ≤ a)
    (hgap : ∀ s, τ ≤ violationWeight F w s)
    (htotal : (∑ c ∈ F, w c) ≤ p * τ) (hbranch : branchingWeight F w ≤ q * τ) :
    ∃ K ⊆ F, K.card ≤ 1 + a * (p * 2 ^ (q + 1)) ∧ ¬ ∃ s, Models K s := by
  rw [← capacity_mul hp (q + 1)]
  apply exists_core_of_horizon F w τ a p _ hp hw hpos hneg hgap
  have hprice := mul_le_mul_of_nonneg_left hbranch (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  push_cast
  linarith only [add_le_add htotal hprice, hτ]

/-- For total weight `W`, branching weight `B`, and positive loss lower bound `τ`, some
unsatisfiable subset has at most `1 + a * ⌈W/τ⌉ * 2^(⌈B/τ⌉+1)` distinct clauses. The
atom type need not be finite. The budget counts original clauses, not proof-tree nodes. -/
theorem exists_small_core (F : Finset (Clause α)) (w : Clause α → ℝ) (τ : ℝ) (a : ℕ)
    (hτ : 0 < τ) (hw : ∀ c ∈ F, 0 ≤ w c)
    (hpos : ∀ c ∈ F, c.head.isSome = true → c.body.card ≤ 2)
    (hneg : ∀ c ∈ F, c.head = none → c.body.card ≤ a)
    (hgap : ∀ s, τ ≤ violationWeight F w s) :
    ∃ K ⊆ F, K.card ≤ 1 + a * (⌈(∑ c ∈ F, w c) / τ⌉₊ * 2 ^ (⌈branchingWeight F w / τ⌉₊ + 1)) ∧
      ¬ ∃ s, Models K s := by
  classical
  have hW : τ ≤ ∑ c ∈ F, w c := by
    refine (hgap ∅).trans (Finset.sum_le_sum fun c hc => ?_)
    split <;> simp_all
  have hp : 0 < ⌈(∑ c ∈ F, w c) / τ⌉₊ := Nat.ceil_pos.mpr (div_pos (hτ.trans_le hW) hτ)
  exact exists_core_of_budgets F w τ a _ _ hτ hp hw hpos hneg hgap
    ((div_le_iff₀ hτ).mp (Nat.le_ceil _)) ((div_le_iff₀ hτ).mp (Nat.le_ceil _))

end WeightedHornCores
