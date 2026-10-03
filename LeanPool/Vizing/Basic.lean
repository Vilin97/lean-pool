/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto

/-!
# Partial edge colourings

Basic definitions and extension operations for the fan-and-Kempe proof of Vizing's theorem.
-/

public section

section
/-!
# Partial edge colourings

Basic framework for Vizing's theorem: a *partial proper edge colouring* of a simple graph `G`
is a symmetric partial function on pairs of vertices, defined only on edges, such that two
distinct edges sharing a vertex never receive the same colour.
-/

open SimpleGraph Finset

namespace LeanPool.Vizing

variable {V : Type*} [DecidableEq V] {C : Type*}

/-- A partial proper edge colouring of `G` with colours in `C`. -/
structure PEC (G : SimpleGraph V) (C : Type*) where
  /-- The colour of the edge `u v`, if it is coloured. -/
  col : V → V → Option C
  col_symm : ∀ u v, col u v = col v u
  col_adj : ∀ {u v γ}, col u v = some γ → G.Adj u v
  col_proper : ∀ {u v w γ}, col u v = some γ → col u w = some γ → v = w

namespace PEC

variable {G : SimpleGraph V}

/-- A colour is free at a vertex if no edge at that vertex carries it. -/
@[expose]
def IsFree (c : PEC G C) (v : V) (γ : C) : Prop := ∀ u, c.col v u ≠ some γ

/-- `c'` colours at least the edges that `c` colours. -/
@[expose]
def Extends (c c' : PEC G C) : Prop := ∀ u v, c.col u v ≠ none → c'.col u v ≠ none

omit [DecidableEq V] in
lemma Extends.rfl' (c : PEC G C) : Extends c c := fun _ _ h => h

omit [DecidableEq V] in
lemma Extends.trans {c₁ c₂ c₃ : PEC G C} (h₁ : Extends c₁ c₂) (h₂ : Extends c₂ c₃) :
    Extends c₁ c₃ := fun u v h => h₂ u v (h₁ u v h)

omit [DecidableEq V] in
lemma col_self (c : PEC G C) (u : V) : c.col u u = none := by
  cases h : c.col u u with
  | none => rfl
  | some γ => exact absurd (c.col_adj h) (G.irrefl)

omit [DecidableEq V] in
/-- At every vertex there is a free colour, provided there are more colours than the maximum
degree. -/
lemma exists_free [Fintype V] [Fintype C] [DecidableRel G.Adj] (c : PEC G C)
    (hcard : G.maxDegree < Fintype.card C)
    (v : V) : ∃ γ, c.IsFree v γ := by
  by_contra hcon
  push Not at hcon
  simp only [IsFree, not_forall, not_not] at hcon
  choose g hg using hcon
  have hginj : Set.InjOn g (univ : Finset C) := by
    intro γ₁ _ γ₂ _ h
    have : (some γ₁ : Option C) = some γ₂ := by rw [← hg γ₁, ← hg γ₂, h]
    exact Option.some_injective _ this
  have hmem : ∀ γ ∈ (univ : Finset C), g γ ∈ G.neighborFinset v := by
    intro γ _
    exact (mem_neighborFinset _ _ _).2 (c.col_adj (hg γ))
  have hcards := Finset.card_le_card_of_injOn g hmem hginj
  simp only [card_univ, card_neighborFinset_eq_degree] at hcards
  exact absurd (hcards.trans (G.degree_le_maxDegree v)) (by omega)

/-! ### Updating a single edge -/

/-- Change the colour of the edge `x y` (in both directions) to `o`. -/
def updFun (f : V → V → Option C) (x y : V) (o : Option C) : V → V → Option C :=
  fun u v => if (u = x ∧ v = y) ∨ (u = y ∧ v = x) then o else f u v

lemma updFun_of_ne {f : V → V → Option C} {x y u v : V} (o : Option C)
    (h : ¬((u = x ∧ v = y) ∨ (u = y ∧ v = x))) : updFun f x y o u v = f u v := ite_eq_right h

@[simp] lemma updFun_left {f : V → V → Option C} {x y : V} (o : Option C) :
    updFun f x y o x y = o := ite_eq_left (Or.inl ⟨rfl, rfl⟩)

@[simp] lemma updFun_right {f : V → V → Option C} {x y : V} (o : Option C) :
    updFun f x y o y x = o := ite_eq_left (Or.inr ⟨rfl, rfl⟩)

/-- Colour the (possibly already coloured) edge `x y` with a colour free at both endpoints. -/
@[expose]
def setEdge (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) : PEC G C where
  col := updFun c.col x y (some γ)
  col_symm := by
    intro u v
    unfold updFun
    by_cases h : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    · rw [ite_eq_left h, ite_eq_left (by tauto)]
    · rw [ite_eq_right h, ite_eq_right (by tauto)]
      exact c.col_symm u v
  col_adj := by
    intro u v δ h
    unfold updFun at h
    by_cases hc : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact hadj.symm
    · rw [ite_eq_right hc] at h
      exact c.col_adj h
  col_proper := by
    have key : ∀ u v δ, updFun c.col x y (some γ) u v = some δ →
        ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) ∨ c.col u v = some δ := by
      intro u v δ h
      unfold updFun at h
      by_cases hc : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
      · exact Or.inl hc
      · rw [ite_eq_right hc] at h
        exact Or.inr h
    have hcol : ∀ u v δ, updFun c.col x y (some γ) u v = some δ →
        (((u = x ∧ v = y) ∨ (u = y ∧ v = x)) → δ = γ) := by
      intro u v δ h hc
      unfold updFun at h
      rw [ite_eq_left hc] at h
      exact (Option.some_injective _ h).symm
    intro u v w δ h1 h2
    rcases key u v δ h1 with hc1 | hc1 <;> rcases key u w δ h2 with hc2 | hc2
    · rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hc2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        subst_vars <;> rfl
    · have hd1 := hcol u v δ h1 hc1
      subst hd1
      rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hc2 (hx w)
      · exact absurd hc2 (hy w)
    · have hd2 := hcol u w δ h2 hc2
      subst hd2
      rcases hc2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hc1 (hx v)
      · exact absurd hc1 (hy v)
    · exact c.col_proper hc1 hc2

@[simp] lemma setEdge_col (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) :
    (c.setEdge γ hadj hx hy).col = updFun c.col x y (some γ) := rfl

lemma setEdge_col_of_ne_left (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) {w : V} (hwx : w ≠ x) (hwy : w ≠ y) (u : V) :
    (c.setEdge γ hadj hx hy).col w u = c.col w u :=
  updFun_of_ne _ (by tauto)

lemma isFree_setEdge_of_ne (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) {w : V} (hwx : w ≠ x) (hwy : w ≠ y) (δ : C) :
    (c.setEdge γ hadj hx hy).IsFree w δ ↔ c.IsFree w δ := by
  constructor <;> intro h u hu
  · exact h u (by rw [c.setEdge_col_of_ne_left γ hadj hx hy hwx hwy u]; exact hu)
  · rw [c.setEdge_col_of_ne_left γ hadj hx hy hwx hwy u] at hu
    exact h u hu

lemma extends_setEdge (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) : Extends c (c.setEdge γ hadj hx hy) := by
  intro u v h
  simp only [setEdge_col, updFun]
  split
  · exact Option.some_ne_none _
  · exact h

end PEC

end LeanPool.Vizing
end
