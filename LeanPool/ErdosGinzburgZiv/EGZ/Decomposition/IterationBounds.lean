/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationEvents
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedOperations
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Initialization

/-!
# Numerical invariants of finite refinement runs

The state at stage `i` has at most `2^i` nodes, lies within the predetermined
radius horizon, and has lost at most the first `i` explicit mass budgets.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.FlagDecomposition.Iteration

open DecompositionParameters

/-- Scale assigned to a given stage of the bounded iteration. -/
noncomputable def stageScale (d : ℕ) (ε : ℝ) (i : ℕ) : ℝ :=
  scale d (initialScale d ε) (i + 1)

/-- Accumulated mass-loss budget before a given iteration index. -/
noncomputable def prefixBudget (d : ℕ) (ε : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, lossBudget d ε (initialScale d ε) (j + 1)

@[simp] theorem prefixBudget_zero (d : ℕ) (ε : ℝ) : prefixBudget d ε 0 = 0 := by
  simp [prefixBudget]

theorem prefixBudget_succ (d : ℕ) (ε : ℝ) (i : ℕ) :
    prefixBudget d ε (i + 1) = prefixBudget d ε i +
      (ε * stageScale d ε i ^ 2 + (3 : ℝ) ^ (d + 1) * stageScale d ε i) := by
  simp [prefixBudget, Finset.sum_range_succ, lossBudget, stageScale, refinementConstant]

theorem prefixBudget_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (i : ℕ) : prefixBudget d ε i ≤ ε ^ 2 / 8 := by
  simpa [prefixBudget] using initialScale_sum_tail_le hd hε hεhalf 0 (Finset.range i)

theorem stageScale_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    0 < stageScale d ε i := scale_pos d (initialScale_pos d hε) (i + 1)

theorem stageScale_antitone {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Antitone (stageScale d ε) :=
  fun _ _ h ↦ scale_antitone hd (initialScale_pos d hε).le (Nat.add_le_add_right h 1)

theorem stageScale_small {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (i : ℕ) :
    (3 : ℝ) ^ (d + 1) * stageScale d ε i < 1 ∧
      ε * stageScale d ε i ^ 2 < 1 := by
  have hle : stageScale d ε i ≤ initialScale d ε := by
    simpa [stageScale] using scale_antitone hd (initialScale_pos d hε).le (Nat.zero_le (i + 1))
  have hbase := initialScale_bounds d hε hεhalf
  have hδ := (stageScale_pos d hε i).le
  have hδone := hle.trans hbase.2.1
  constructor
  · exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans_lt hbase.1
  · have hs : stageScale d ε i ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hε.le]

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    {g : ℕ → ℕ} (P : NormalizedOperationParameters d g) (ε : ℝ)

/-- Iteration state with bounds on node count, radius, and accumulated mass loss. -/
structure BoundedState (i : ℕ) extends State p d f where
  card_bound : Fintype.card decomposition.flag.Node ≤ 2 ^ i
  radius_bound : radius ≤ P.radiusHorizon 1 i
  mass_loss_bound : (natMass f : ℝ) - decomposition.retainedMass ≤
    prefixBudget d ε i * natMass f

namespace BoundedState

variable {P ε} {i : ℕ} (s : BoundedState (f := f) P ε i)

omit [Fact (Nat.Prime p)] in
theorem mass_le_input : s.decomposition.retainedMass ≤ natMass f :=
  natMass_mono s.decomposition.retained_le

omit [Fact (Nat.Prime p)] in
theorem mass_bounds (hd : 1 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    (natMass f : ℝ) / 2 ≤ s.decomposition.retainedMass ∧
      (1 - ε) * (natMass f : ℝ) ≤ s.decomposition.retainedMass := by
  have hM := Nat.cast_nonneg (α := ℝ) (natMass f)
  have hbudget := mul_le_mul_of_nonneg_right (prefixBudget_le hd hε hεhalf i) hM
  have hhalf : ε ^ 2 / 8 ≤ 1 / 2 := by nlinarith
  have heps : ε ^ 2 / 8 ≤ ε := by nlinarith
  have hhalfM := mul_le_mul_of_nonneg_right hhalf hM
  have hepsM := mul_le_mul_of_nonneg_right heps hM
  constructor <;> nlinarith [s.mass_loss_bound]

/-- Initial bounded state for a nonzero input weight. -/
noncomputable def initial (hf : f ≠ 0) : BoundedState (f := f) P ε 0 where
  decomposition := FlagDecomposition.initial f hf
  radius := 1
  radius_pos := le_rfl
  minimal := initial_isMinimal f hf
  reduced := initial_isReduced f hf
  bounded := initial_isKBounded f hf _
  card_bound := by rw [initial_card]; norm_num
  radius_bound := le_rfl
  mass_loss_bound := by rw [initial_retainedMass, prefixBudget_zero]; simp

/-- Advance a bounded state using a certified progress step and a radius bound. -/
noncomputable def advance {t : State p d f} (hε : 0 < ε)
    (D : Progress s.toState t ε (stageScale d ε i) g)
    (hR : t.radius ≤ P.radiusGrowth s.radius) : BoundedState (f := f) P ε (i + 1) where
  toState := t
  card_bound := D.card_le.trans
    (by simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 2 s.card_bound)
  radius_bound := by
    change t.radius ≤ P.radiusGrowth^[i + 1] 1
    rw [Function.iterate_succ_apply']
    exact hR.trans (P.radiusGrowth_growing.1 s.radius_bound)
  mass_loss_bound := by
    rw [prefixBudget_succ]
    have hcoef : 0 ≤ ε * stageScale d ε i ^ 2 + (3 : ℝ) ^ (d + 1) * stageScale d ε i := by
      have := (stageScale_pos d hε i).le
      positivity
    have hM : (s.decomposition.retainedMass : ℝ) ≤ natMass f := by exact_mod_cast s.mass_le_input
    have hs := mul_le_mul_of_nonneg_left hM hcoef
    have hl := D.mass_loss_le
    change (s.decomposition.retainedMass : ℝ) - t.decomposition.retainedMass ≤ _ at hl
    nlinarith [s.mass_loss_bound]

/-- Retain the same underlying state at the next iteration index. -/
noncomputable def keep (hε : 0 < ε) : BoundedState (f := f) P ε (i + 1) where
  toState := s.toState
  card_bound := s.card_bound.trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ i))
  radius_bound := s.radius_bound.trans (P.radiusHorizon_monotone 1 (Nat.le_succ i))
  mass_loss_bound := by
    rw [prefixBudget_succ]
    have hcoef : 0 ≤ ε * stageScale d ε i ^ 2 + (3 : ℝ) ^ (d + 1) * stageScale d ε i := by
      have := (stageScale_pos d hε i).le
      positivity
    have hM := Nat.cast_nonneg (α := ℝ) (natMass f)
    nlinarith [s.mass_loss_bound, mul_nonneg hcoef hM]

end BoundedState
end EGZ.FlagDecomposition.Iteration
