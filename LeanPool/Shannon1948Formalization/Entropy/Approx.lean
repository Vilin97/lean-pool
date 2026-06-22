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
    0 < approxCount p N a :=
  Nat.succ_pos _

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
  have hT : 0 < T := by simpa [T] using approxTotal_pos p N
  have hT_ne : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  refine ⟨fun a => (approxCount p N a : ℝ) / (T : ℝ), fun a => by positivity, ?_⟩
  rw [← Finset.sum_div, show (∑ a, (approxCount p N a : ℝ)) = (T : ℝ) by
    rw [← Nat.cast_sum]; rfl, div_self hT_ne]

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
  have hM_nonneg : 0 ≤ M := by dsimp [M]; positivity
  have hfloor_le : (Nat.floor (M * p a) : ℝ) ≤ M * p a :=
    Nat.floor_le (mul_nonneg hM_nonneg (prob_nonneg p a))
  have hlt : M * p a < (Nat.floor (M * p a) : ℝ) + 1 := Nat.lt_floor_add_one (M * p a)
  have hcount : (approxCount p N a : ℝ) = (Nat.floor (M * p a) : ℝ) + 1 := by
    simp [approxCount, M, add_comm]
  rw [hcount]; constructor <;> linarith

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
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, prob_sum_eq_one p, mul_one]
    simp [approxTotal]
  have hnonneg : 0 ≤ ∑ a, ((approxCount p N a : ℝ) - M * p a) :=
    Finset.sum_nonneg fun a _ => (approxCount_mul_bounds p N a).1
  have hupper :
      (∑ a, ((approxCount p N a : ℝ) - M * p a)) ≤ ∑ _a : α, (1 : ℝ) :=
    Finset.sum_le_sum fun a _ => (approxCount_mul_bounds p N a).2
  rw [hsumDelta] at hnonneg hupper
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hupper
  exact ⟨hnonneg, hupper⟩

lemma approxProb_error_bound
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ)
    (a : α) :
    let M : ℝ := ((N + 1 : ℕ) : ℝ)
    |approxProb p N a - p a|
      ≤ ((Fintype.card α : ℝ) + 1) / M := by
  intro M
  have hM_pos : 0 < M := by dsimp [M]; positivity
  let T : ℝ := (approxTotal p N : ℝ)
  have hT_bounds : 0 ≤ T - M ∧ T - M ≤ Fintype.card α := by
    simpa [T, M] using approxTotal_bounds p N
  have hM_le_T : M ≤ T := sub_nonneg.mp hT_bounds.1
  have hT_pos : 0 < T := lt_of_lt_of_le hM_pos hM_le_T
  have hT_ne : T ≠ 0 := ne_of_gt hT_pos
  have habs_MT : |M - T| ≤ Fintype.card α := by
    rw [abs_sub_comm, abs_of_nonneg hT_bounds.1]; exact hT_bounds.2
  have hdelta_abs : |(approxCount p N a : ℝ) - M * p a| ≤ 1 := by
    have hdelta := approxCount_mul_bounds p N a
    simp only [M] at hdelta ⊢
    rw [abs_of_nonneg hdelta.1]; exact hdelta.2
  have hp_abs_le_one : |p a| ≤ 1 := by
    rw [abs_of_nonneg (prob_nonneg p a)]; exact prob_le_one p a
  have hnum :
      |(approxCount p N a : ℝ) - p a * T| ≤ (Fintype.card α : ℝ) + 1 := by
    have hmul_le : |p a * (M - T)| ≤ (Fintype.card α : ℝ) := by
      rw [abs_mul]
      calc |p a| * |M - T| ≤ 1 * (Fintype.card α : ℝ) :=
            mul_le_mul hp_abs_le_one habs_MT (abs_nonneg _) (by norm_num)
        _ = (Fintype.card α : ℝ) := one_mul _
    have hdecomp : (approxCount p N a : ℝ) - p a * T
        = ((approxCount p N a : ℝ) - M * p a) + p a * (M - T) := by ring
    calc
      |(approxCount p N a : ℝ) - p a * T|
          = |((approxCount p N a : ℝ) - M * p a) + p a * (M - T)| := by rw [hdecomp]
      _ ≤ |(approxCount p N a : ℝ) - M * p a| + |p a * (M - T)| := abs_add_le _ _
      _ ≤ (Fintype.card α : ℝ) + 1 := by linarith
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
    _ ≤ (((Fintype.card α : ℝ) + 1) / T) := by gcongr
    _ ≤ ((Fintype.card α : ℝ) + 1) / M := div_le_div_of_nonneg_left (by positivity) hM_pos hM_le_T

lemma tendsto_approxProb_apply
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (a : α) :
    Tendsto (fun N : ℕ => approxProb p N a) atTop (𝓝 (p a)) := by
  have hbound_tendsto :
      Tendsto (fun N : ℕ => ((Fintype.card α : ℝ) + 1) / (((N + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hone' : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
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
  have hsub : Tendsto (fun N : ℕ => approxProb p N a - p a) atTop (𝓝 (0 : ℝ)) :=
    tendsto_zero_iff_abs_tendsto_zero _ |>.2 habs_tendsto
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
