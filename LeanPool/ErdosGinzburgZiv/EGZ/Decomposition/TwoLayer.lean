/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.Fin.Basic

/-!
# Two-layer refinements of a finite node poset

Every old node has an upper copy, while nodes below an anchor also have a
lower copy. The product order preserves joins. A global selector moves the
selected atoms below the anchor to the lower layer; this preserves all total
mass and every upper cumulative weight.
-/

open scoped BigOperators
open Classical

namespace EGZ.TwoLayer

variable {α : Type*} [SemilatticeSup α]

/-- Upper copies of every node and lower copies below the chosen anchor. -/
abbrev Node (anchor : α) := {a : α × Fin 2 // a.2 = 0 → a.1 ≤ anchor}

noncomputable instance (anchor : α) [Fintype α] : Fintype (Node anchor) := Subtype.fintype _

instance (anchor : α) : SemilatticeSup (Node anchor) :=
  Subtype.semilatticeSup fun a b ha hb h ↦ by
    have ha0 : a.2 = 0 := by
      have hle : a.2 ≤ (a ⊔ b).2 := le_sup_left
      rw [h] at hle
      omega
    have hb0 : b.2 = 0 := by
      have hle : b.2 ≤ (a ⊔ b).2 := le_sup_right
      rw [h] at hle
      omega
    exact sup_le (ha ha0) (hb hb0)

instance (anchor : α) [OrderTop α] : OrderTop (Node anchor) where
  top := ⟨(⊤, 1), by simp⟩
  le_top a := by
    constructor
    · exact le_top
    · change a.1.2 ≤ (1 : Fin 2)
      have := a.1.2.isLt
      omega

/-- Forget the layer; this preserves joins. -/
def projection (anchor : α) : SupHom (Node anchor) α where
  toFun a := a.1.1
  map_sup' _ _ := rfl

/-- The upper copy of an old node. -/
def upper (anchor : α) (a : α) : Node anchor := ⟨(a, 1), by simp⟩

/-- The lower copy of a node below the anchor. -/
def lower (anchor : α) (a : α) (ha : a ≤ anchor) : Node anchor := ⟨(a, 0), fun _ ↦ ha⟩

@[simp] theorem projection_upper (anchor a : α) : projection anchor (upper anchor a) = a := rfl
@[simp] theorem projection_lower (anchor a : α) (ha : a ≤ anchor) :
    projection anchor (lower anchor a ha) = a := rfl

@[simp] theorem upper_le_upper (anchor a b : α) :
    upper anchor a ≤ upper anchor b ↔ a ≤ b := by
  change (a ≤ b ∧ (1 : Fin 2) ≤ 1) ↔ a ≤ b
  simp

@[simp] theorem lower_le_lower (anchor a b : α) (ha : a ≤ anchor) (hb : b ≤ anchor) :
    lower anchor a ha ≤ lower anchor b hb ↔ a ≤ b := by
  change (a ≤ b ∧ (0 : Fin 2) ≤ 0) ↔ a ≤ b
  simp

@[simp] theorem lower_le_upper (anchor a b : α) (ha : a ≤ anchor) :
    lower anchor a ha ≤ upper anchor b ↔ a ≤ b := by
  change (a ≤ b ∧ (0 : Fin 2) ≤ 1) ↔ a ≤ b
  simp

@[simp] theorem not_upper_le_lower (anchor a b : α) (hb : b ≤ anchor) :
    ¬ upper anchor a ≤ lower anchor b hb := by
  change ¬ (a ≤ b ∧ (1 : Fin 2) ≤ 0)
  simp

def upperEmbedding (anchor : α) : α ↪o Node anchor where
  toFun := upper anchor
  inj' _ _ h := congrArg (projection anchor) h
  map_rel_iff' := upper_le_upper anchor _ _

def lowerEmbedding (anchor : α) : {a : α // a ≤ anchor} ↪o Node anchor where
  toFun a := lower anchor a.1 a.2
  inj' _ _ h := Subtype.ext (congrArg (projection anchor) h)
  map_rel_iff' := lower_le_lower anchor _ _ _ _

/-- Every layered node is uniquely either an upper copy or a lower copy. -/
noncomputable def layerEquiv (anchor : α) : α ⊕ {a : α // a ≤ anchor} ≃ Node anchor where
  toFun := Sum.elim (upper anchor) (fun a ↦ lower anchor a.1 a.2)
  invFun a := if h : a.1.2 = 0 then Sum.inr ⟨a.1.1, a.2 h⟩ else Sum.inl a.1.1
  left_inv a := by
    cases a <;> simp [upper, lower]
  right_inv a := by
    rcases a with ⟨⟨a, b⟩, ha⟩
    by_cases hb : b = 0
    · subst b
      simp [lower]
    · have hb1 : b = 1 := by have := b.isLt; omega
      subst b
      simp [upper, lower]

section Finite

variable [Fintype α]

theorem card_nodes (anchor : α) :
    Fintype.card (Node anchor) = Fintype.card α + Fintype.card {a : α // a ≤ anchor} := by
  rw [← Fintype.card_congr (layerEquiv anchor), Fintype.card_sum]

theorem card_nodes_le (anchor : α) : Fintype.card (Node anchor) ≤ 2 * Fintype.card α := by
  rw [card_nodes]
  have := Fintype.card_subtype_le (fun a : α ↦ a ≤ anchor)
  omega

/-- Split a sum over layered nodes into upper and lower contributions. -/
theorem sum_nodes {M : Type*} [AddCommMonoid M] (anchor : α) (g : Node anchor → M) :
    ∑ a, g a = (∑ a : α, g (upper anchor a)) +
      ∑ a : {a : α // a ≤ anchor}, g (lower anchor a.1 a.2) := by
  rw [← (layerEquiv anchor).sum_comp g, Fintype.sum_sum_type]
  rfl

theorem sum_below_eq {M : Type*} [AddCommMonoid M] (anchor : α) (g : α → M) :
    ∑ a : {a : α // a ≤ anchor}, g a = ∑ a : α, if a ≤ anchor then g a else 0 := by
  rw [← Finset.sum_filter]
  symm
  exact Finset.sum_subtype _ (by simp) g

end Finite

variable {β : Type*}

/-- Move selected atoms below the anchor into the lower layer. -/
noncomputable def splitWeight (anchor : α) (w : α → β → ℕ) (S : β → Prop)
    (a : Node anchor) (v : β) : ℕ :=
  if a.1.2 = 0 then (if S v then w a.1.1 v else 0)
  else if a.1.1 ≤ anchor ∧ S v then 0 else w a.1.1 v

@[simp] theorem splitWeight_upper (anchor : α) (w : α → β → ℕ) (S : β → Prop)
    (a : α) (v : β) :
    splitWeight anchor w S (upper anchor a) v =
      if a ≤ anchor ∧ S v then 0 else w a v := by
  simp only [splitWeight, upper]
  split_ifs <;> rfl

@[simp] theorem splitWeight_lower (anchor : α) (w : α → β → ℕ) (S : β → Prop)
    (a : α) (ha : a ≤ anchor) (v : β) :
    splitWeight anchor w S (lower anchor a ha) v = if S v then w a v else 0 := by
  simp [splitWeight, lower]

theorem splitWeight_le (anchor : α) (w : α → β → ℕ) (S : β → Prop)
    (a : Node anchor) (v : β) : splitWeight anchor w S a v ≤ w (projection anchor a) v := by
  change splitWeight anchor w S a v ≤ w a.1.1 v
  unfold splitWeight
  split_ifs <;> omega

/-- Every old atom retains its full weight at one of the two copies. -/
theorem exists_splitWeight_eq (anchor : α) (w : α → β → ℕ) (S : β → Prop)
    (a : α) (v : β) :
    ∃ b : Node anchor, projection anchor b = a ∧ splitWeight anchor w S b v = w a v := by
  by_cases h : a ≤ anchor ∧ S v
  · exact ⟨lower anchor a h.1, rfl, by simp [h.2]⟩
  · exact ⟨upper anchor a, rfl, by simp [h]⟩

section Finite

variable [Fintype α]

/-- Splitting atoms between the two layers preserves every retained weight. -/
theorem sum_splitWeight (anchor : α) (w : α → β → ℕ) (S : β → Prop) (v : β) :
    ∑ a : Node anchor, splitWeight anchor w S a v = ∑ a : α, w a v := by
  rw [sum_nodes]
  simp only [splitWeight_upper, splitWeight_lower]
  rw [sum_below_eq anchor (fun a ↦ if S v then w a v else 0), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ≤ anchor <;> by_cases hv : S v <;> simp [ha, hv]

/-- Cumulative weight in an arbitrary finite node order. -/
noncomputable def cumulativeWeight (w : α → β → ℕ) (a : α) (v : β) : ℕ :=
  ∑ b, if b ≤ a then w b v else 0

/-- Every upper node retains its entire old cumulative weight. -/
theorem cumulativeWeight_upper (anchor : α) (w : α → β → ℕ) (S : β → Prop)
    (a : α) (v : β) :
    cumulativeWeight (splitWeight anchor w S) (upper anchor a) v = cumulativeWeight w a v := by
  unfold cumulativeWeight
  rw [sum_nodes]
  simp only [upper_le_upper, lower_le_upper, splitWeight_upper, splitWeight_lower]
  rw [sum_below_eq anchor (fun b ↦ if b ≤ a then (if S v then w b v else 0) else 0),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hba : b ≤ a <;> by_cases hb : b ≤ anchor <;> by_cases hv : S v <;>
    simp [hba, hb, hv]

/-- A lower node has precisely the selected part of its old cumulative weight. -/
theorem cumulativeWeight_lower (anchor : α) (w : α → β → ℕ) (S : β → Prop)
    (a : α) (ha : a ≤ anchor) (v : β) :
    cumulativeWeight (splitWeight anchor w S) (lower anchor a ha) v =
      if S v then cumulativeWeight w a v else 0 := by
  unfold cumulativeWeight
  rw [sum_nodes]
  simp only [not_upper_le_lower, ite_false, Finset.sum_const_zero, zero_add,
    lower_le_lower, splitWeight_lower]
  rw [sum_below_eq anchor (fun b ↦ if b ≤ a then (if S v then w b v else 0) else 0)]
  by_cases hv : S v
  · simp only [hv, ite_true]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b ≤ a
    · simp [hb, hb.trans ha]
    · simp [hb]
  · simp [hv]

/-- Every layered cumulative weight is bounded by its old projected weight. -/
theorem cumulativeWeight_projection_le (anchor : α) (w : α → β → ℕ) (S : β → Prop)
    (a : Node anchor) (v : β) :
    cumulativeWeight (splitWeight anchor w S) a v ≤ cumulativeWeight w (projection anchor a) v := by
  obtain ⟨a, rfl⟩ := (layerEquiv anchor).surjective a
  cases a with
  | inl a =>
      change cumulativeWeight (splitWeight anchor w S) (upper anchor a) v ≤ cumulativeWeight w a v
      rw [cumulativeWeight_upper]
  | inr a =>
      change cumulativeWeight (splitWeight anchor w S) (lower anchor a.1 a.2) v ≤
        cumulativeWeight w a.1 v
      rw [cumulativeWeight_lower]
      split_ifs <;> omega

end Finite

end EGZ.TwoLayer
