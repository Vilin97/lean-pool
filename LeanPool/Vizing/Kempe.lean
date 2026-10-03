/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Endpoints

/-!
# Kempe chains for partial edge colourings

Given a partial proper edge colouring `c` and two colours `a b`, the *Kempe graph* consists of
the edges coloured `a` or `b`.  Swapping the two colours on the connected component of a vertex
`x` produces another partial proper edge colouring, colouring exactly the same edges.
-/

public section

open SimpleGraph Finset

namespace LeanPool.Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}

/-- The subgraph consisting of the edges coloured `a` or `b`. -/
def kempeGraph (c : PEC G C) (a b : C) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (c.col u v = some a ∨ c.col u v = some b)
  symm.symm := by
    rintro u v ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rwa [c.col_symm v u]
  loopless := ⟨fun v h => h.1 rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
lemma kempeGraph_adj {c : PEC G C} {a b : C} {u v : V} :
    (c.kempeGraph a b).Adj u v ↔ u ≠ v ∧ (c.col u v = some a ∨ c.col u v = some b) := Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
lemma kempeGraph_adj_of_col {c : PEC G C} {a b : C} {u v : V}
    (h : c.col u v = some a ∨ c.col u v = some b) : (c.kempeGraph a b).Adj u v := by
  refine ⟨?_, h⟩
  rcases h with h | h <;> exact (c.col_adj h).ne

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
/-- Reachability in the Kempe graph propagates along edges coloured `a` or `b`. -/
lemma reachable_of_col {c : PEC G C} {a b : C} {x u v : V}
    (hu : (c.kempeGraph a b).Reachable x u)
    (h : c.col u v = some a ∨ c.col u v = some b) : (c.kempeGraph a b).Reachable x v :=
  hu.trans (kempeGraph_adj_of_col h).reachable

open Classical in
/-- The colour function after swapping `a` and `b` on the Kempe component of `x`. -/
noncomputable def kempeSwapFun (c : PEC G C) (a b : C) (x : V) : V → V → Option C :=
  fun u v => if (c.kempeGraph a b).Reachable x u ∧ (c.kempeGraph a b).Reachable x v
    then (c.col u v).map (Equiv.swap a b) else c.col u v

omit [Fintype V] [DecidableEq V] in
lemma kempeSwapFun_of_reachable (c : PEC G C) (a b : C) {x u : V}
    (hu : (c.kempeGraph a b).Reachable x u) (v : V) :
    c.kempeSwapFun a b x u v = (c.col u v).map (Equiv.swap a b) := by
  classical
  unfold kempeSwapFun
  by_cases hv : (c.kempeGraph a b).Reachable x v
  · rw [ite_eq_left ⟨hu, hv⟩]
  · rw [ite_eq_right (by tauto)]
    cases h : c.col u v with
    | none => simp
    | some γ =>
      have hγa : γ ≠ a := by
        rintro rfl
        exact hv (reachable_of_col hu (Or.inl h))
      have hγb : γ ≠ b := by
        rintro rfl
        exact hv (reachable_of_col hu (Or.inr h))
      simp [Equiv.swap_apply_of_ne_of_ne hγa hγb]

omit [Fintype V] [DecidableEq V] in
lemma kempeSwapFun_of_not_reachable (c : PEC G C) (a b : C) {x u : V}
    (hu : ¬ (c.kempeGraph a b).Reachable x u) (v : V) :
    c.kempeSwapFun a b x u v = c.col u v := by
  classical
  unfold kempeSwapFun
  rw [ite_eq_right (by tauto)]

omit [Fintype V] [DecidableEq V] in
lemma kempeSwapFun_isSome (c : PEC G C) (a b : C) (x u v : V) :
    (c.kempeSwapFun a b x u v = none) ↔ (c.col u v = none) := by
  classical
  by_cases hu : (c.kempeGraph a b).Reachable x u
  · rw [kempeSwapFun_of_reachable c a b hu v]
    cases c.col u v <;> simp
  · rw [kempeSwapFun_of_not_reachable c a b hu v]

/-- Swapping the colours `a` and `b` on the Kempe component of `x`. -/
@[expose]
noncomputable def kempeSwap (c : PEC G C) (a b : C) (x : V) : PEC G C where
  col := c.kempeSwapFun a b x
  col_symm := by
    classical
    intro u v
    unfold kempeSwapFun
    by_cases h : (c.kempeGraph a b).Reachable x u ∧ (c.kempeGraph a b).Reachable x v
    · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩, c.col_symm u v]
    · rw [ite_eq_right h, ite_eq_right (fun hh => h ⟨hh.2, hh.1⟩), c.col_symm u v]
  col_adj := by
    intro u v γ h
    by_cases hu : (c.kempeGraph a b).Reachable x u
    · rw [kempeSwapFun_of_reachable c a b hu v] at h
      cases hc : c.col u v with
      | none => rw [hc] at h; simp at h
      | some δ => exact c.col_adj hc
    · rw [kempeSwapFun_of_not_reachable c a b hu v] at h
      exact c.col_adj h
  col_proper := by
    intro u v w γ h1 h2
    by_cases hu : (c.kempeGraph a b).Reachable x u
    · rw [kempeSwapFun_of_reachable c a b hu v] at h1
      rw [kempeSwapFun_of_reachable c a b hu w] at h2
      cases hcv : c.col u v with
      | none => rw [hcv] at h1; simp at h1
      | some δ =>
        cases hcw : c.col u w with
        | none => rw [hcw] at h2; simp at h2
        | some ε =>
          rw [hcv] at h1
          rw [hcw] at h2
          simp only [Option.map_some] at h1 h2
          have : δ = ε := (Equiv.swap a b).injective (by
            rw [Option.some_injective _ h1, Option.some_injective _ h2])
          exact c.col_proper hcv (this ▸ hcw)
    · rw [kempeSwapFun_of_not_reachable c a b hu v] at h1
      rw [kempeSwapFun_of_not_reachable c a b hu w] at h2
      exact c.col_proper h1 h2

omit [Fintype V] [DecidableEq V] in
@[simp] lemma kempeSwap_col (c : PEC G C) (a b : C) (x : V) :
    (c.kempeSwap a b x).col = c.kempeSwapFun a b x := rfl

omit [Fintype V] [DecidableEq V] in
lemma extends_kempeSwap (c : PEC G C) (a b : C) (x : V) : Extends c (c.kempeSwap a b x) := by
  intro u v h
  rw [kempeSwap_col, ne_eq, kempeSwapFun_isSome]
  exact h

omit [Fintype V] [DecidableEq V] in
/-- On the Kempe component the free colours get swapped. -/
lemma isFree_kempeSwap_of_reachable (c : PEC G C) (a b : C) {x v : V}
    (hv : (c.kempeGraph a b).Reachable x v) (γ : C) :
    (c.kempeSwap a b x).IsFree v γ ↔ c.IsFree v (Equiv.swap a b γ) := by
  constructor
  · intro h u hu
    refine h u ?_
    rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hv u, hu]
    simp
  · intro h u hu
    rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hv u] at hu
    cases hc : c.col v u with
    | none => rw [hc] at hu; simp at hu
    | some δ =>
      rw [hc] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      refine h u ?_
      rw [hc, ← hu]
      simp

omit [Fintype V] [DecidableEq V] in
/-- Off the Kempe component the free colours are unchanged. -/
lemma isFree_kempeSwap_of_not_reachable (c : PEC G C) (a b : C) {x v : V}
    (hv : ¬ (c.kempeGraph a b).Reachable x v) (γ : C) :
    (c.kempeSwap a b x).IsFree v γ ↔ c.IsFree v γ := by
  constructor
  · intro h u hu
    exact h u (by rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hv u]; exact hu)
  · intro h u hu
    rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hv u] at hu
    exact h u hu

/-! ### Degrees in the Kempe graph -/

omit [DecidableEq V] [DecidableEq C] in
lemma kempe_degree_le_two (c : PEC G C) (a b : C) [DecidableRel (c.kempeGraph a b).Adj] (v : V) :
    (c.kempeGraph a b).degree v ≤ 2 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have hsub : (c.kempeGraph a b).neighborFinset v ⊆
      ((c.kempeGraph a b).neighborFinset v).filter (fun u => c.col v u = some a) ∪
      ((c.kempeGraph a b).neighborFinset v).filter (fun u => c.col v u = some b) := by
    intro u hu
    have hu' := hu
    rw [mem_neighborFinset, kempeGraph_adj] at hu'
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hu'.2 with h | h
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr ⟨hu, h⟩
  have hcarda : (((c.kempeGraph a b).neighborFinset v).filter
      (fun u => c.col v u = some a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    exact c.col_proper hp.2 hq.2
  have hcardb : (((c.kempeGraph a b).neighborFinset v).filter
      (fun u => c.col v u = some b)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    exact c.col_proper hp.2 hq.2
  calc ((c.kempeGraph a b).neighborFinset v).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 := by omega

omit [DecidableEq V] [DecidableEq C] in
lemma kempe_degree_le_one_of_isFree (c : PEC G C) {a b : C} [DecidableRel (c.kempeGraph a b).Adj]
    {v : V} {γ : C} (hγ : γ = a ∨ γ = b) (hfree : c.IsFree v γ) :
    (c.kempeGraph a b).degree v ≤ 1 := by
  classical
  rw [← card_neighborFinset_eq_degree, Finset.card_le_one]
  intro p hp q hq
  rw [mem_neighborFinset, kempeGraph_adj] at hp hq
  rcases hγ with rfl | rfl
  · rcases hp.2 with h | h
    · exact absurd h (hfree p)
    · rcases hq.2 with h' | h'
      · exact absurd h' (hfree q)
      · exact c.col_proper h h'
  · rcases hp.2 with h | h
    · rcases hq.2 with h' | h'
      · exact c.col_proper h h'
      · exact absurd h' (hfree q)
    · exact absurd h (hfree p)

end PEC

end LeanPool.Vizing
