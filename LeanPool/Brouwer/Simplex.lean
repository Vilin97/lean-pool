/-
Copyright (c) 2026 Math_XMUM. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math_XMUM
-/
module

public import Mathlib.Analysis.Convex.Topology

/-!
# Mixed strategies on the standard simplex

This file equips `standardSimplex` over a finite type with a `FunLike` coercion and
records the basic arithmetic facts about pure strategies and weighted sums used
when reasoning about mixed strategies, including the key inequality
`wsum_magic_ineq` relating a weighted sum to a uniform bound.
-/

@[expose] public section

namespace Brouwer

/-- The standard simplex as a set of coordinate functions. Keeping this representation gives
its points the subspace topology of the finite product used in the fixed-point proof. -/
def standardSimplex (k α : Type*) [Semiring k] [PartialOrder k] [Fintype α] : Set (α → k) :=
  {f | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}

/-- The real standard simplex is a closed subset of the unit cube. -/
theorem isCompact_standardSimplex (α : Type*) [Fintype α] :
    IsCompact (standardSimplex ℝ α) := by
  have closed : IsClosed (standardSimplex ℝ α) := by
    have description : standardSimplex ℝ α =
        (⋂ i, {f : α → ℝ | 0 ≤ f i}) ∩ {f | ∑ i, f i = 1} := by
      ext f
      simp only [standardSimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [description]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  refine IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (0 : α → ℝ) 1)) closed ?_
  intro f hf
  exact ⟨fun i => hf.1 i, fun i =>
    (Finset.single_le_sum (fun j _ => hf.1 j) (Finset.mem_univ i)).trans_eq hf.2⟩

instance (α : Type*) [Fintype α] : CompactSpace (standardSimplex ℝ α) :=
  isCompact_iff_compactSpace.mp (isCompact_standardSimplex α)

end Brouwer

open Brouwer (standardSimplex)

/- We use `MixedStrategy` to denote a mixed strategy over a finite type. -/

variable (α : Type*) [Fintype α] [DecidableEq α]

namespace stdSimplex
variable (k : Type*) [CommRing k] [LinearOrder k] [IsStrictOrderedRing k] (α : Type*) [Fintype α]

instance funlike : FunLike (standardSimplex k α) α k where
  coe := Subtype.val
  coe_injective := Subtype.val_injective

omit [IsStrictOrderedRing k] in
lemma funlike_eval1 (f : standardSimplex k α) : f = f.val := rfl

omit [IsStrictOrderedRing k] in
lemma funlike_eval2 (f : standardSimplex k α) (x : α) : f.val x = f x := rfl

variable {k α} in
/-- The pure strategy concentrated at `i`, as a point of the standard simplex. -/
abbrev pure [DecidableEq α] (i : α) : standardSimplex k α := ⟨fun j => if i = j then 1 else 0,
 by
  constructor
  · intro j
    by_cases H : i = j
    repeat simp [H]
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]⟩

variable {k α} in
lemma pure_eval_eq [DecidableEq α] {i j : α} (h : i = j) : pure i j = (1 : k) := by
  rw [← funlike_eval2]
  simp [h]


variable {k α} in
lemma pure_eval_neq [DecidableEq α] {i j : α} (h : ¬ i = j) : pure i j = (0 : k) := by
  rw [← funlike_eval2]
  simp [h]


noncomputable instance SInhabitedOfInhabited [DecidableEq α] [Inhabited α] :
    Inhabited (standardSimplex k α) where
  default := pure (default : α)

open scoped Classical in
noncomputable instance SNonempty_of_Inhabited {α : Type*} [Fintype α]
    [Inhabited α] : Nonempty (standardSimplex k α) :=
  Nonempty.intro (default : standardSimplex k α)

variable {k α} in
lemma wsum_magic_ineq [PosMulMono k]
    {σ : standardSimplex k α} {f : α → k} {c : k} :
  ∑ i : α, (σ i) *  f i = c → ∃ i, 0 < σ i ∧ f i ≤ c := by
    intro H1
    by_contra H2
    push Not at H2
    have h_exists_pos : ∃ i, 0 < σ i := by
      by_contra h_all_zero
      push Not at h_all_zero
      have h_all_eq_zero : ∀ i, σ i = 0 := fun i => le_antisymm (h_all_zero i) (σ.2.1 i)
      have h_sum_zero : ∑ i, σ i = 0 := by simp [h_all_eq_zero]
      have h_sum_one : ∑ i, σ i = 1 := σ.2.2
      simp_all
    obtain ⟨i₀, hi₀⟩ := h_exists_pos
    have h_ge : c < ∑ i, σ i * f i := by
      have h_sum_c : ∑ i, σ i * c = c := by
        have h_sum_eq_one : ∑ i, σ i = 1 := σ.2.2
        rw [← Finset.sum_mul, h_sum_eq_one, one_mul]
      rw [← h_sum_c]
      apply Finset.sum_lt_sum
      · intro i _
        by_cases h_pos : 0 < σ i
        · have h_fi_gt_c : c < f i := H2 i h_pos
          exact mul_le_mul_of_nonneg_left (le_of_lt h_fi_gt_c) (le_of_lt h_pos)
        · have h_zero : σ i = 0 := le_antisymm (le_of_not_gt h_pos) (σ.2.1 i)
          simp [h_zero]
      · use i₀, Finset.mem_univ i₀
        simp_all
    simp_all

end stdSimplex


/-- The standard simplex over `α` with real coefficients, used as mixed strategies. -/
abbrev MixedStrategy := standardSimplex ℝ α
