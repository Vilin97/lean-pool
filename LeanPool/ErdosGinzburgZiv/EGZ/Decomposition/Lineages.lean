/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic

/-!
# Lineages of nodes below a fixed level

Parent maps which do not increase level backwards, and are injective on
the low-level nodes, embed every later low-level population in the initial
one. Event counts therefore reduce to counts for initial ancestor labels.
A killed lineage cannot label any later event.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.Lineages

attribute [local instance] Classical.propDecidable

universe u

/-- The abstract data needed for lineage bookkeeping. No geometric
properties of the nodes or parent maps are assumed. -/
structure System where
  /-- The finite node type at each stage of the lineage system. -/
  Node : ℕ → Type u
  finiteNode : ∀ i, Fintype (Node i)
  /-- The level assigned to each node at its stage. -/
  level : ∀ i, Node i → ℕ
  /-- The predecessor of a node in the preceding stage. -/
  parent : ∀ i, Node (i + 1) → Node i
  level_parent : ∀ i x, level i (parent i x) ≤ level (i + 1) x

attribute [instance] System.finiteNode

namespace System

variable (S : System)

/-- Nodes at or below the chosen level cutoff. -/
abbrev LowNode (L i : ℕ) := {x : S.Node i // S.level i x ≤ L}

/-- Later low-level nodes have distinct old parents. -/
def InjectiveBelow (L : ℕ) : Prop :=
  ∀ i, Set.InjOn (S.parent i) {x | S.level (i + 1) x ≤ L}

variable {L : ℕ} (hinj : S.InjectiveBelow L)

include hinj

/-- The restricted parent map is an embedding. -/
def parentEmbedding (i : ℕ) : S.LowNode L (i + 1) ↪ S.LowNode L i where
  toFun x := ⟨S.parent i x, (S.level_parent i x).trans x.property⟩
  inj' x y h := Subtype.ext (hinj i x.property y.property (congrArg Subtype.val h))

@[simp]
theorem parentEmbedding_val (i : ℕ) (x : S.LowNode L (i + 1)) :
    (S.parentEmbedding hinj i x).val = S.parent i x := rfl

/-- Follow a low-level node back to any earlier stage. -/
def ancestor {i j : ℕ} (h : i ≤ j) : S.LowNode L j ↪ S.LowNode L i :=
  Nat.leRecOn h (fun {k} e ↦ (S.parentEmbedding hinj k).trans e)
    (Function.Embedding.refl _)

@[simp]
theorem ancestor_self (i : ℕ) :
    S.ancestor hinj (le_refl i) = Function.Embedding.refl (S.LowNode L i) :=
  Nat.leRecOn_self _

theorem ancestor_succ {i j : ℕ} (h : i ≤ j) :
    S.ancestor hinj (h.trans (Nat.le_succ j)) =
      (S.parentEmbedding hinj j).trans (S.ancestor hinj h) :=
  Nat.leRecOn_succ h _

/-- Following parents in two stages agrees with following them directly. -/
theorem ancestor_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (x : S.LowNode L k) :
    S.ancestor hinj hij (S.ancestor hinj hjk x) = S.ancestor hinj (hij.trans hjk) x := by
  revert x
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    intro x
    rw [S.ancestor_succ hinj hk, S.ancestor_succ hinj (hij.trans hk)]
    exact ih (S.parentEmbedding hinj k x)

/-- The original low-level ancestor labels each surviving lineage. -/
def ancestry (i : ℕ) : S.LowNode L i ↪ S.LowNode L 0 :=
  S.ancestor hinj (Nat.zero_le i)

@[simp]
theorem ancestry_zero : S.ancestry hinj 0 = Function.Embedding.refl (S.LowNode L 0) :=
  S.ancestor_self hinj 0

@[simp]
theorem ancestry_succ (i : ℕ) (x : S.LowNode L (i + 1)) :
    S.ancestry hinj (i + 1) x = S.ancestry hinj i (S.parentEmbedding hinj i x) := by
  exact congrArg (fun e ↦ e x) (S.ancestor_succ hinj (Nat.zero_le i))

theorem ancestry_ancestor {i j : ℕ} (h : i ≤ j) (x : S.LowNode L j) :
    S.ancestry hinj i (S.ancestor hinj h x) = S.ancestry hinj j x :=
  S.ancestor_trans hinj (Nat.zero_le i) h x

theorem card_lowNode_le_initial (i : ℕ) :
    Fintype.card (S.LowNode L i) ≤ Fintype.card (S.Node 0) :=
  (Fintype.card_le_of_injective _ (S.ancestry hinj i).injective).trans
    (Fintype.card_subtype_le _)

/-- A selected node is killed when it has no child below the cutoff in
the next stage. Higher-level replacements are permitted. -/
def IsKilled (i : ℕ) (x : S.LowNode L i) : Prop :=
  ∀ y : S.LowNode L (i + 1), S.parent i y ≠ x.val

/-- Killing a lineage prevents its ancestor label from appearing later. -/
theorem ancestry_ne_of_killed {i j : ℕ} (hij : i < j)
    (x : S.LowNode L i) (y : S.LowNode L j) (hx : S.IsKilled i x) :
    S.ancestry hinj i x ≠ S.ancestry hinj j y := by
  intro heq
  let z := S.ancestor hinj (Nat.succ_le_of_lt hij) y
  have hz : S.ancestry hinj i (S.parentEmbedding hinj i z) = S.ancestry hinj j y := by
    rw [← S.ancestry_succ hinj i z]
    exact S.ancestry_ancestor hinj (Nat.succ_le_of_lt hij) y
  have hp := (S.ancestry hinj i).injective (hz.trans heq.symm)
  exact hx z (congrArg Subtype.val hp)

variable {E : Type*} [Fintype E]

/-- Label an event by the original ancestor of its selected low-level node. -/
def eventLabel (time : E → ℕ) (selected : ∀ e, S.LowNode L (time e)) (e : E) :
    S.Node 0 := (S.ancestry hinj (time e) (selected e)).val

/-- A uniform bound per ancestor gives a total event bound. -/
theorem card_events_le (time : E → ℕ) (selected : ∀ e, S.LowNode L (time e))
    (C : ℕ)
    (hcount : ∀ r : S.Node 0,
      (Finset.univ.filter fun e ↦ S.eventLabel hinj time selected e = r).card ≤ C) :
    Fintype.card E ≤ Fintype.card (S.Node 0) * C := by
  classical
  calc
    Fintype.card E = ∑ r : S.Node 0,
        (Finset.univ.filter fun e ↦ S.eventLabel hinj time selected e = r).card := by
      simpa using (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset E)) (t := (Finset.univ : Finset (S.Node 0)))
        (f := S.eventLabel hinj time selected) (by simp))
    _ ≤ ∑ _r : S.Node 0, C := Finset.sum_le_sum (fun r _ ↦ hcount r)
    _ = Fintype.card (S.Node 0) * C := by simp

omit [Fintype E] in
/-- Events at distinct times which kill their selected lineage have
distinct original ancestor labels. -/
theorem eventLabel_injective_of_killed (time : E → ℕ)
    (selected : ∀ e, S.LowNode L (time e)) (htime : Function.Injective time)
    (hkilled : ∀ e, S.IsKilled (time e) (selected e)) :
    Function.Injective (S.eventLabel hinj time selected) := by
  intro e f hef
  apply htime
  have heq : S.ancestry hinj (time e) (selected e) =
      S.ancestry hinj (time f) (selected f) := Subtype.ext hef
  rcases lt_trichotomy (time e) (time f) with h | h | h
  · exact (S.ancestry_ne_of_killed hinj h (selected e) (selected f) (hkilled e) heq).elim
  · exact h
  · exact (S.ancestry_ne_of_killed hinj h (selected f) (selected e)
      (hkilled f) heq.symm).elim

/-- There is at most one killing event for each initial lineage. -/
theorem card_killed_events_le (time : E → ℕ)
    (selected : ∀ e, S.LowNode L (time e)) (htime : Function.Injective time)
    (hkilled : ∀ e, S.IsKilled (time e) (selected e)) :
    Fintype.card E ≤ Fintype.card (S.Node 0) :=
  Fintype.card_le_of_injective _
    (S.eventLabel_injective_of_killed hinj time selected htime hkilled)

/-- Restart the bookkeeping at any stage, as needed for a color interval. -/
def shift (start : ℕ) : System where
  Node i := S.Node (start + i)
  finiteNode i := S.finiteNode (start + i)
  level i := S.level (start + i)
  parent i := S.parent (start + i)
  level_parent i := S.level_parent (start + i)

theorem injectiveBelow_shift (start : ℕ) : (S.shift start).InjectiveBelow L :=
  fun i ↦ hinj (start + i)

end System
end EGZ.Lineages
