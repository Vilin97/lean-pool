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
  exact lt_of_lt_of_le (approxCount_pos p N a0)
    (Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ a0))

/-- Rational approximation of `p` obtained from floor counts. -/
def approxProb
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ) : ProbDist α := by
  let T : ℕ := approxTotal p N
  have hT : 0 < T := approxTotal_pos p N
  have hT_ne : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  refine ⟨fun a => (approxCount p N a : ℝ) / (T : ℝ), ?_⟩
  constructor
  · intro a; positivity
  · have hsum : (∑ a, (approxCount p N a : ℝ)) = (T : ℝ) := by
      have : T = ∑ a, approxCount p N a := rfl
      exact_mod_cast this.symm
    rw [show (∑ a, (fun a => (approxCount p N a : ℝ) / (T : ℝ)) a) =
        (∑ a, (approxCount p N a : ℝ)) / (T : ℝ) from (Finset.sum_div _ _ _).symm,
        hsum, div_self hT_ne]

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
    H (approxProb p N) = -K H * ∑ a, approxProb p N a * Real.log (approxProb p N a) :=
  entropyNat_of_rational_counts H hH (approxProb p N) (approxCount p N)
    (fun a => approxCount_pos p N a) (approxTotal p N) (approxTotal_pos p N)
    (by simp [approxTotal]) (fun a => by simp [approxProb_apply])

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
  have hlt : M * p a < (Nat.floor (M * p a) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hval : (approxCount p N a : ℝ) = (Nat.floor (M * p a) : ℝ) + 1 := by
    simp [approxCount, M, add_comm]
  constructor
  · linarith
  · linarith [hfloor_le]

lemma approxTotal_bounds
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (N : ℕ) :
    let M : ℝ := ((N + 1 : ℕ) : ℝ)
    0 ≤ (approxTotal p N : ℝ) - M ∧
      (approxTotal p N : ℝ) - M ≤ Fintype.card α := by
  intro M
  have hsumDelta : (∑ a, ((approxCount p N a : ℝ) - M * p a)) = (approxTotal p N : ℝ) - M := by
    simp only [Finset.sum_sub_distrib, approxTotal]
    push_cast
    rw [← Finset.mul_sum, prob_sum_eq_one p, mul_one]
  have hnonneg : 0 ≤ ∑ a, ((approxCount p N a : ℝ) - M * p a) :=
    Finset.sum_nonneg fun a _ => (approxCount_mul_bounds p N a).1
  have hupper : (∑ a, ((approxCount p N a : ℝ) - M * p a)) ≤ ∑ _a : α, (1 : ℝ) :=
    Finset.sum_le_sum fun a _ => (approxCount_mul_bounds p N a).2
  constructor
  · linarith
  · calc (approxTotal p N : ℝ) - M
        = ∑ a, ((approxCount p N a : ℝ) - M * p a) := hsumDelta.symm
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
  have hM_pos : 0 < M := by dsimp [M]; positivity
  let T : ℝ := (approxTotal p N : ℝ)
  have hT_bounds : 0 ≤ T - M ∧ T - M ≤ Fintype.card α := by
    simpa [T, M] using approxTotal_bounds p N
  have hM_le_T : M ≤ T := sub_nonneg.mp hT_bounds.1
  have hT_pos : 0 < T := lt_of_lt_of_le hM_pos hM_le_T
  have hdelta := approxCount_mul_bounds p N a
  have hdelta_nonneg : 0 ≤ (approxCount p N a : ℝ) - M * p a := hdelta.1
  have hdelta_le : (approxCount p N a : ℝ) - M * p a ≤ 1 := hdelta.2
  have hdelta_abs : |(approxCount p N a : ℝ) - M * p a| ≤ 1 := by
    rw [abs_of_nonneg hdelta_nonneg]
    exact hdelta_le
  have habs_MT : |M - T| ≤ Fintype.card α := by
    rw [abs_of_nonpos (by linarith [hT_bounds.1])]
    linarith [hT_bounds.2]
  have hnum : |(approxCount p N a : ℝ) - p a * T| ≤ (Fintype.card α : ℝ) + 1 := by
    have : (approxCount p N a : ℝ) - p a * T =
        ((approxCount p N a : ℝ) - M * p a) + p a * (M - T) := by ring
    calc |(approxCount p N a : ℝ) - p a * T|
        = |((approxCount p N a : ℝ) - M * p a) + p a * (M - T)| := by rw [this]
      _ ≤ |(approxCount p N a : ℝ) - M * p a| + |p a| * |M - T| := by
            have := abs_add_le ((approxCount p N a : ℝ) - M * p a) (p a * (M - T))
            rwa [abs_mul] at this
      _ ≤ 1 + 1 * (Fintype.card α : ℝ) := by
            have hp_abs : |p a| ≤ 1 := by
              simpa [abs_of_nonneg (prob_nonneg p a)] using prob_le_one p a
            have := mul_le_mul hp_abs habs_MT (abs_nonneg _) (by positivity)
            linarith
      _ = (Fintype.card α : ℝ) + 1 := by ring
  have hsub : approxProb p N a - p a = ((approxCount p N a : ℝ) - p a * T) / T := by
    have hT_ne : T ≠ 0 := ne_of_gt hT_pos
    rw [approxProb_apply, show T = (approxTotal p N : ℝ) from rfl]
    rw [sub_div]
    congr 1
    rw [mul_div_assoc, div_self hT_ne, mul_one]
  rw [hsub, abs_div, abs_of_pos hT_pos]
  exact (div_le_div_of_nonneg_right hnum hT_pos.le).trans
    (div_le_div_of_nonneg_left (by positivity) hM_pos hM_le_T)

lemma tendsto_approxProb_apply
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (a : α) :
    Tendsto (fun N : ℕ => approxProb p N a) atTop (𝓝 (p a)) := by
  have hbound_tendsto :
      Tendsto (fun N : ℕ => ((Fintype.card α : ℝ) + 1) / (((N + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hone' : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [Nat.cast_add] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun N : ℕ => (1 : ℝ) / (N + 1)) atTop (𝓝 0))
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      tendsto_const_nhds.mul hone'
  have habs_tendsto : Tendsto (fun N : ℕ => |approxProb p N a - p a|) atTop (𝓝 0) :=
    squeeze_zero (fun N => abs_nonneg _) (fun N => by simpa using approxProb_error_bound p N a)
      hbound_tendsto
  have hsub : Tendsto (fun N : ℕ => approxProb p N a - p a) atTop (𝓝 (0 : ℝ)) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]; simpa using habs_tendsto
  exact (Filter.tendsto_sub_const_iff (b := p a)).1 (by simpa using hsub)

lemma tendsto_approxProb
    {α : Type} [Fintype α]
    (p : ProbDist α) :
    Tendsto (fun N : ℕ => approxProb p N) atTop (𝓝 p) :=
  tendsto_subtype_rng.2 (tendsto_pi_nhds.mpr fun a => by simpa using tendsto_approxProb_apply p a)


end

end LeanPool.Shannon1948Formalization
