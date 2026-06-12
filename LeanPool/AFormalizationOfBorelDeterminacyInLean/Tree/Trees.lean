/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import Mathlib.SetTheory.Descriptive.Tree
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.FinLists

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.Trees

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace Descriptive.Tree
--TODO if continue commits, add newline between declarations before
variable {A A' : Type*} (S T : tree A) (x y : List A)

/-- Set of children of node x as elements of T -/
def ExtensionsAt {T : tree A} (x : T) := { a : A // x.val ++ [a] ∈ T }
namespace ExtensionsAt
variable {S T}
variable {n : ℕ} {x : T} (a : ExtensionsAt x)
/-- The underlying list of a child -/
def val' := x.val ++ [a.val]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps coe] def valT' : T := ⟨a.val', a.prop⟩
@[ext] lemma ext {a b : ExtensionsAt x} (h : a.val = b.val) : a = b := Subtype.ext h
lemma ext_val' {a b : ExtensionsAt x} (h : a.val' = b.val') : a = b := by
  ext; simpa [val'] using h
lemma ext_valT' {a b : ExtensionsAt x} (h : a.valT' = b.valT') : a = b :=
  ext_val' <| congr_arg Subtype.val h
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def drop {T : tree A} {n : ℕ} {x : T} :
  ExtensionsAt x ≃ ExtensionsAt (Tree.drop T n x) where --TODO fix T explicit
  toFun a := ⟨a.val, by simpa [← List.append_assoc] using a.prop⟩
  invFun a := ⟨a.val, by simpa [← List.append_assoc] using a.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
@[simp] lemma val'_length :
  a.val' (A := no_index _).length (α := no_index _) = x.val.length (α := no_index _) + 1 := by
  simp [ExtensionsAt.val']
lemma val'_get_last_of_eq (a : ExtensionsAt x) (h : n = x.val.length) :
  a.val'[n]'(by simp [h]) = a.val := by simp [val', h]
@[simp↓ 1100] lemma val'_get_last (a : ExtensionsAt x) :
  a.val' (A := no_index _)[x.val.length (α := no_index _)] = a.val := by simp [val']
lemma val'_take_of_le (a : ExtensionsAt x) (h : n ≤ x.val.length) :
  a.val'.take n = x.val.take n := by simpa [val']
lemma val'_take_of_eq (a : ExtensionsAt x) (h : n = x.val.length) :
  a.val'.take n = x.val := by simp [val', h]
@[simp↓ 1100] lemma val'_take (a : ExtensionsAt x) :
  a.val' (A := no_index _).take (x.val.length (α := no_index _)) = x.val := by simp [val']
lemma valT'_take_of_le (a : ExtensionsAt x) (h : n ≤ x.val.length) :
  take n a.valT' = take n x := Subtype.ext <| a.val'_take_of_le h
lemma valT'_take_of_eq (a : ExtensionsAt x) (h : n = x.val.length) :
  take n a.valT' = x := Subtype.ext <| a.val'_take_of_eq h
@[simp↓ 1100] lemma valT'_take (a : ExtensionsAt x) :
  take (x.val.length (α := no_index _)) a.valT'  (A := no_index _) = x := Subtype.ext a.val'_take
end ExtensionsAt

/-- A tree is pruned if it has no leaves -/
def IsPruned : Prop := ∀ x : T, Nonempty (ExtensionsAt x)
lemma IsPruned.sub {T : tree A} (h : IsPruned T) (x : List A) : IsPruned (subAt T x) := by
  intro ⟨y, h'⟩
  simpa only [ExtensionsAt, nonempty_subtype, List.append_assoc, mem_subAt] using h ⟨_, h'⟩
lemma IsPruned.pullSub {T : tree A} (hP : IsPruned T) (x : List A) : IsPruned (pullSub T x) := by
  intro ⟨y, hy⟩; rcases lt_or_ge y.length x.length with h | h
  · rw [mem_pullSub_short (by omega), List.prefix_iff_eq_take] at hy; use x.get ⟨y.length, h⟩
    simp_rw (config := {singlePass := true}) [hy.1]
    conv => simp [h.le]
    constructor
    · rw [List.take_take]; apply List.take_prefix
    · rw [List.drop_take]; simpa [h] using hy.2
  · rw [mem_pullSub_long h] at hy; obtain ⟨z, hz, rfl⟩ := hy; obtain ⟨a, ha⟩ := hP ⟨z, hz⟩
    use a; simpa
@[simp] lemma pullSub_ne {T : tree A} x : [] ∈ pullSub T x ↔ [] ∈ T := by
  simp [mem_pullSub_short]
@[simp] lemma top_isPruned [h : Nonempty A] : IsPruned (⊤ : tree A) :=
  fun _ ↦ ⟨h.some, CompleteSublattice.mem_top⟩

/-- Order elements of a tree by the prefix relation -/
@[simps] instance instPartialOrderTree (T : tree A) : PartialOrder T where
  le x y := x.val <+: y.val
  le_refl _ := List.prefix_refl _
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm _ _ h h' :=
    Subtype.ext <| List.IsPrefix.eq_of_length h <| h.length_le.antisymm h'.length_le
lemma apply_append {S : tree A} {T : tree A'} (f : OrderHom S T)
  {x y : List A} (h : x ++ y ∈ S) :
  ∃ z, (f ⟨x ++ y, h⟩).val = f ⟨x, mem_of_append h⟩ ++ z :=
  let ⟨z, h⟩ := f.monotone (a := ⟨x, mem_of_append h⟩) (b := ⟨_, h⟩) ⟨y, rfl⟩
  ⟨z, h.symm⟩

attribute [simp_lengths] take_coe drop_coe ExtensionsAt.valT'_coe ExtensionsAt.val'_length
end Tree
end Descriptive
