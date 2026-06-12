/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.Meager
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.BorelDeterminacy

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.Choquet

Auxiliary declarations for the Borel determinacy formalization.
-/


open GaleStewartGame
open Descriptive

namespace Choquet

variable {X : Type*} (V : Set (Set X)) (PO : Set (Set X))
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def chainTree : tree V where
    val := {x | x.IsChain (· ≥ ·)}
    property _ _ := List.IsChain.left_of_append
lemma def_chainTree (x : List V) : x ∈ chainTree V ↔ x.IsChain (· ≥ ·) := by
    simp [chainTree]
lemma nil_mem_chainTree : [] ∈ chainTree V := by simp [chainTree]
lemma concat_mem_chainTree {x A} :
    x ++ [A] ∈ chainTree V ↔ x ∈ chainTree V ∧ ∀ hx, A ≤ x.getLast hx := by
    simp_rw [def_chainTree, List.isChain_append, List.isChain_singleton]
    obtain rfl | ⟨x, ⟨B, rfl⟩⟩ := x.eq_nil_or_concat' <;> simp
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def chainTree.concat (x : chainTree V) (A : V) (h : ∀ hx, A ≤ x.val.getLast hx) : chainTree V where
    val := x.val ++ [A]
    property := by rw [concat_mem_chainTree]; use x.prop
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def interGame : Game V where
    tree := chainTree V
    payoff A := PO (⋂ n, A.1 n)
variable {V}
variable {W : Set (Set X)} (hWV : W ⊆ V) (hW : ∀ A ∈ V, ∃ B ∈ W, B ⊆ A)
lemma extend_mem_iff (x : List W) : x.map (Set.inclusion hWV) ∈ chainTree V ↔ x ∈ chainTree W := by
    simp [chainTree, List.isChain_map]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def extend (x : chainTree W) : chainTree V where
    val := x.1.map (Set.inclusion hWV)
    property := by simpa only [extend_mem_iff] using x.2
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def extend' {x : chainTree W} (a : Tree.ExtensionsAt x) :
    Tree.ExtensionsAt (extend hWV x) where
    val := Set.inclusion hWV a.val
    property := by
        rw [← List.map_singleton, extend_coe, ← List.map_append, extend_mem_iff]
        exact a.prop
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def choosePair (A : V) : W where
    val := (hW A A.coe_prop).choose
    property := (hW A A.coe_prop).choose_spec.1
lemma choosePairSub A : (choosePair hW A).val ⊆ A.val := (hW A A.coe_prop).choose_spec.2
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def shrink' {x : chainTree W} (a : Tree.ExtensionsAt (extend hWV x)) :
    Tree.ExtensionsAt x := ⟨_, (chainTree.concat W x (choosePair hW a.val) (by
        intro hx; apply (choosePairSub hW a.val).trans
        have ha := a.prop; rw [concat_mem_chainTree] at ha
        have hlast : a.val ≤ Set.inclusion hWV (x.val.getLast hx) := by
          simpa [extend_coe, List.getLast_map] using ha.2 (by simpa [extend_coe] using hx)
        change a.val.val ⊆ (Set.inclusion hWV (x.val.getLast hx)).val
        exact hlast)).prop⟩
attribute [simp_lengths] extend_coe

variable (X)
variable [TopologicalSpace X]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def game := interGame (X := X) {A | IsOpen A ∧ A.Nonempty} {∅}
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def IsChoquet := (game X).ExistsWinning Player.one
end Choquet
