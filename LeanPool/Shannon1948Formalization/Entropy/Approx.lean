/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import LeanPool.Shannon1948Formalization.Entropy.Rational

/-!
# Shannon.Entropy.Approx

Phase 3 of the characterization: continuity extension.

Constructs floor-count rational approximants `approxProb p N` and proves
their convergence to `p`. This is the bridge from the rational formula to the
full real-probability formula.
-/
namespace LeanPool.Shannon1948Formalization

noncomputable section
open Filter
open scoped Topology

/-! ## Phase 3: Continuity Extension by Rational Approximation -/

/-- Integer count approximation used in the continuity-extension phase. -/
def approxCount
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ)
    (a : α) : ℕ :=
  Nat.floor (((N + 1 : ℕ) : ℝ) * p a) + 1

/-- Total count for `approxCount`; this is the denominator of the rational approximation. -/
def approxTotal
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ) : ℕ :=
  ∑ a, approxCount p N a

lemma approxCount_pos
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ)
    (a : α) :
    0 < approxCount p N a := by
  unfold approxCount
  exact Nat.succ_pos _

lemma approxTotal_pos
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ) :
    0 < approxTotal p N := by
  classical
  obtain ⟨a0⟩ := nonempty_of_probDist p
  unfold approxTotal
  exact lt_of_lt_of_le
    (approxCount_pos p N a0)
    (Finset.single_le_sum
      (fun b _ => Nat.zero_le (approxCount p N b))
      (Finset.mem_univ a0))

/-- Rational approximation of `p` obtained from floor counts. -/
def approxProb
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ) : ProbDist α := by
  let T : ℕ := approxTotal p N
  have hT : 0 < T := by
    simpa [T] using approxTotal_pos p N
  refine ⟨fun a => (approxCount p N a : ℝ) / (T : ℝ), ?_⟩
  constructor
  · intro a
    positivity
  · have hT_ne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
    calc
      (∑ a, (approxCount p N a : ℝ) / (T : ℝ))
          = (∑ a, (approxCount p N a : ℝ)) / (T : ℝ) := by
              rw [Finset.sum_div]
      _ = (T : ℝ) / (T : ℝ) := by
            simp [T, approxTotal]
      _ = 1 := by
            field_simp [hT_ne]

@[simp] lemma approxProb_apply
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ)
    (a : α) :
    approxProb p N a = (approxCount p N a : ℝ) / (approxTotal p N : ℝ) := by
  unfold approxProb
  simp

lemma entropyNat_approxProb
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ) :
    H (approxProb p N) = -K H * ∑ a, approxProb p N a * Real.log (approxProb p N a) := by
  refine entropyNat_of_rational_counts H hH (approxProb p N) (approxCount p N) ?_ (approxTotal p N)
    (approxTotal_pos p N) ?_ ?_
  · intro a
    exact approxCount_pos p N a
  · simp [approxTotal]
  · intro a
    simp [approxProb_apply]

lemma approxCount_mul_bounds
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ)
    (a : α) :
    let M : ℝ := ((N + 1 : ℕ) : ℝ)
    0 ≤ (approxCount p N a : ℝ) - M * p a ∧
      (approxCount p N a : ℝ) - M * p a ≤ 1 := by
  intro M
  have hp_nonneg : 0 ≤ p a := prob_nonneg p a
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hfloor_le : (Nat.floor (M * p a) : ℝ) ≤ M * p a := by
    exact Nat.floor_le (mul_nonneg hM_nonneg hp_nonneg)
  have hlt : M * p a < (Nat.floor (M * p a) : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (M * p a)
  constructor
  · calc
      0 ≤ ((Nat.floor (M * p a) : ℝ) + 1) - M * p a := by
            linarith [hlt]
      _ = (approxCount p N a : ℝ) - M * p a := by
            simp [approxCount, M, add_comm]
  · calc
      (approxCount p N a : ℝ) - M * p a
          = ((Nat.floor (M * p a) : ℝ) + 1) - M * p a := by
              simp [approxCount, M, add_comm]
      _ ≤ (M * p a + 1) - M * p a := by
            gcongr
      _ = 1 := by ring

lemma approxTotal_bounds
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ) :
    let M : ℝ := ((N + 1 : ℕ) : ℝ)
    0 ≤ (approxTotal p N : ℝ) - M ∧
      (approxTotal p N : ℝ) - M ≤ Fintype.card α := by
  intro M
  have hsumDelta :
      (∑ a, ((approxCount p N a : ℝ) - M * p a))
        = (approxTotal p N : ℝ) - M := by
    calc
      (∑ a, ((approxCount p N a : ℝ) - M * p a))
          = (∑ a, (approxCount p N a : ℝ)) - ∑ a, (M * p a) := by
              rw [Finset.sum_sub_distrib]
      _ = (approxTotal p N : ℝ) - (M * ∑ a, p a) := by
            simp [approxTotal, Finset.mul_sum]
      _ = (approxTotal p N : ℝ) - M := by
            rw [prob_sum_eq_one p, mul_one]
  have hnonneg :
      0 ≤ ∑ a, ((approxCount p N a : ℝ) - M * p a) := by
    refine Finset.sum_nonneg ?_
    intro a _
    exact (approxCount_mul_bounds p N a).1
  have hupper :
      (∑ a, ((approxCount p N a : ℝ) - M * p a))
        ≤ ∑ _a : α, (1 : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro a _
    exact (approxCount_mul_bounds p N a).2
  constructor
  · simpa [hsumDelta]
      using hnonneg
  · calc
      (approxTotal p N : ℝ) - M
          = ∑ a, ((approxCount p N a : ℝ) - M * p a) := by
              simp [hsumDelta]
      _ ≤ ∑ _a : α, (1 : ℝ) := hupper
      _ = Fintype.card α := by simp

lemma approxProb_error_bound
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ)
    (a : α) :
    let M : ℝ := ((N + 1 : ℕ) : ℝ)
    |approxProb p N a - p a|
      ≤ ((Fintype.card α : ℝ) + 1) / M := by
  intro M
  have hM_pos : 0 < M := by
    dsimp [M]
    positivity
  have hM_nonneg : 0 ≤ M := le_of_lt hM_pos
  let T : ℝ := (approxTotal p N : ℝ)
  have hT_bounds : 0 ≤ T - M ∧ T - M ≤ Fintype.card α := by
    simpa [T, M] using approxTotal_bounds p N
  have hM_le_T : M ≤ T := by
    exact sub_nonneg.mp hT_bounds.1
  have hT_pos : 0 < T := lt_of_lt_of_le hM_pos hM_le_T
  have hT_ne : T ≠ 0 := ne_of_gt hT_pos
  have habs_MT : |M - T| ≤ Fintype.card α := by
    have habs_TM : |T - M| ≤ Fintype.card α := by
      simpa [abs_of_nonneg hT_bounds.1] using hT_bounds.2
    simpa [abs_sub_comm] using habs_TM
  have hdelta :
      0 ≤ (approxCount p N a : ℝ) - M * p a ∧
      (approxCount p N a : ℝ) - M * p a ≤ 1 := by
    simpa [M] using approxCount_mul_bounds p N a
  have hdelta_abs : |(approxCount p N a : ℝ) - M * p a| ≤ 1 := by
    simpa [abs_of_nonneg hdelta.1] using hdelta.2
  have hp_le_one : p a ≤ 1 := prob_le_one p a
  have hp_abs_le_one : |p a| ≤ 1 := by
    simpa [abs_of_nonneg (prob_nonneg p a)] using hp_le_one
  have hnum :
      |(approxCount p N a : ℝ) - p a * T| ≤ (Fintype.card α : ℝ) + 1 := by
    have hdecomp :
        (approxCount p N a : ℝ) - p a * T
          = ((approxCount p N a : ℝ) - M * p a) + p a * (M - T) := by
      ring
    have hmul_abs :
        |p a * (M - T)| = |p a| * |M - T| := by
      rw [abs_mul]
    have hmul_le_one :
        |p a| * |M - T| ≤ 1 * |M - T| := by
      exact mul_le_mul_of_nonneg_right hp_abs_le_one (abs_nonneg (M - T))
    have hMT_le_card :
        1 * |M - T| ≤ 1 * (Fintype.card α : ℝ) := by
      exact mul_le_mul_of_nonneg_left habs_MT (by positivity : (0 : ℝ) ≤ 1)
    calc
      |(approxCount p N a : ℝ) - p a * T|
          = |((approxCount p N a : ℝ) - M * p a) + p a * (M - T)| := by
              rw [hdecomp]
      _ ≤ |(approxCount p N a : ℝ) - M * p a| + |p a * (M - T)| := by
            exact abs_add_le _ _
      _ = |(approxCount p N a : ℝ) - M * p a| + (|p a| * |M - T|) := by
            rw [hmul_abs]
      _ ≤ 1 + (|p a| * |M - T|) := by linarith [hdelta_abs]
      _ ≤ 1 + (1 * |M - T|) := by linarith [hmul_le_one]
      _ ≤ 1 + (1 * (Fintype.card α : ℝ)) := by linarith [hMT_le_card]
      _ = (Fintype.card α : ℝ) + 1 := by ring
  have hsub :
      approxProb p N a - p a
        = ((approxCount p N a : ℝ) - p a * T) / T := by
    rw [approxProb_apply]
    change (approxCount p N a : ℝ) / T - p a = ((approxCount p N a : ℝ) - p a * T) / T
    field_simp [hT_ne]
  calc
    |approxProb p N a - p a|
        = |((approxCount p N a : ℝ) - p a * T) / T| := by rw [hsub]
    _ = |(approxCount p N a : ℝ) - p a * T| / T := by
          rw [abs_div, abs_of_pos hT_pos]
    _ ≤ (((Fintype.card α : ℝ) + 1) / T) := by
          exact (div_le_div_of_nonneg_right hnum (le_of_lt hT_pos))
    _ ≤ ((Fintype.card α : ℝ) + 1) / M := by
          exact div_le_div_of_nonneg_left (by positivity) hM_pos hM_le_T

lemma tendsto_approxProb_apply
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (a : α) :
    Tendsto (fun N : ℕ => approxProb p N a) atTop (𝓝 (p a)) := by
  have hbound_tendsto :
      Tendsto (fun N : ℕ => ((Fintype.card α : ℝ) + 1) / (((N + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hone :
        Tendsto (fun N : ℕ => (1 : ℝ) / ((N + 1 : ℕ))) atTop (𝓝 0) := by
      simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun N : ℕ => (1 : ℝ) / (N + 1)) atTop (𝓝 0))
    have hone' :
        Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [Nat.cast_add] using hone
    have hmul :
        Tendsto
          (fun N : ℕ => ((Fintype.card α : ℝ) + 1) * ((1 : ℝ) / (N + 1)))
          atTop
          (𝓝 (((Fintype.card α : ℝ) + 1) * 0)) :=
      tendsto_const_nhds.mul hone'
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
  have habs_tendsto :
      Tendsto (fun N : ℕ => |approxProb p N a - p a|) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => abs_nonneg _) ?_ hbound_tendsto
    intro N
    simpa using approxProb_error_bound p N a
  have hsub :
      Tendsto (fun N : ℕ => approxProb p N a - p a) atTop (𝓝 (0 : ℝ)) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa using habs_tendsto
  have hsub' :
      Tendsto (fun N : ℕ => approxProb p N a - p a) atTop (𝓝 (p a - p a)) := by
    simpa using hsub
  exact (Filter.tendsto_sub_const_iff (b := p a)).1 hsub'

lemma tendsto_approxProb
    {α : Type} [Fintype α]
    (p : ProbDist α) :
    Tendsto (fun N : ℕ => approxProb p N) atTop (𝓝 p) := by
  refine (tendsto_subtype_rng).2 ?_
  rw [tendsto_pi_nhds]
  intro a
  simpa using tendsto_approxProb_apply p a


end

end LeanPool.Shannon1948Formalization
