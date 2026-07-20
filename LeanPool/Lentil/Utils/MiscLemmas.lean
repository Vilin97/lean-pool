/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean

namespace LentilLib

theorem forall_unit {p : PUnit → Prop} : (∀ x, p x) ↔ p PUnit.unit := by grind

theorem exists_unit {p : PUnit → Prop} : (∃ x, p x) ↔ p PUnit.unit := by grind

namespace List

theorem mem_forall_iff_fin_index {α : Type u} (l : List α) (p : α → Prop) :
  (∀ x, x ∈ l → p x) ↔ ∀ (x : Fin l.length), p l[x] := by
  constructor
  · intro h x; apply h; simp
  · intro h x hin; rw [List.mem_iff_getElem] at hin
    rcases hin with ⟨n, hlt, heq⟩; subst_vars; exact h ⟨_, hlt⟩

theorem mem_exists_iff_fin_index {α : Type u} (l : List α) (p : α → Prop) :
  (∃ x, x ∈ l ∧ p x) ↔ ∃ (x : Fin l.length), p l[x] := by
  constructor
  · intro ⟨x, hin, h⟩; rw [List.mem_iff_getElem] at hin
    rcases hin with ⟨n, hlt, heq⟩; subst_vars; exists ⟨_, hlt⟩
  · intro ⟨n, h⟩; exists l[n]; simp; try assumption

theorem finRange_fin_in (n : Nat) : ∀ (x : Fin n), x ∈ List.finRange n := by
  simp

theorem take_getElem_drop {α : Type u} {l : List α} {n : Nat} (h : n < l.length) :
  l.take n ++ l[n] :: l.drop (n + 1) = l := by
  conv => enter [2]; rw [← List.take_append_drop n l, ← List.getElem_cons_drop h]

theorem modify_perm {α : Type u} {l : List α} {idx : Nat} (h : idx < l.length) (f : α → α) :
  List.Perm (l ++ [f (l[idx]'h)]) (l.modify idx f ++ [(l[idx]'h)]) := by
  conv => enter [1, 1]; rw [← take_getElem_drop h]
  rw [List.modify_eq_take_cons_drop h]
  repeat rw [List.append_assoc]
  apply List.Perm.append; rfl
  exact List.cons_append_cons_perm

theorem findFindIdx {α : Type u} {l : List α} {p : α → Bool} {res : α}
  (hpred : l.find? p = some res) :
  p res = true ∧ ∃ (idx : Nat) (hidx : idx < l.length), (l[idx]'hidx) = res ∧ l.findIdx? p = idx := by
  rw [List.find?_eq_some_iff_getElem] at hpred
  rcases hpred with ⟨ht, ⟨idx, hidx, rfl, h⟩⟩
  constructor
  · assumption
  · exists idx, hidx; constructor
    · rfl
    · rw [List.findIdx?_eq_some_iff_getElem]; grind

/-- Right-fold a non-empty list, returning the default `d` on the empty list. -/
def foldrD {β : Type v} (f : β → β → β) (d : β) : List β → β
  | [a] => a
  | a :: as => f a (foldrD f d as)
  | [] => d

theorem foldrD_eq_foldr {β : Type v} (f : β → β → β) (d : β) (l : List β)
  (h : ∀ x, f x d = x) :
  foldrD f d l = l.foldr f d := by
  induction l with
  | nil => simp [foldrD]
  | cons a l ih =>
    rcases hh : l with _ | ⟨b, l⟩
    · simp [foldrD, h]
    · simp [foldrD, ← hh, ih]

/-- Whether a list contains a duplicate element, using hashing. -/
def containsDuplicateElemHashable {α : Type u} [BEq α] [Hashable α] (l : List α) : Bool :=
  -- NOTE: Since `MProd` assumes the same universe level for both components,
  -- `α` has to have level 1
  Prod.snd <| l.foldl (init := (Std.HashSet.emptyWithCapacity (α := α), false)) fun (seen, dup) x =>
    if dup || seen.contains x then (seen, true)
    else (seen.insert x, false)

end List

namespace Nat

-- sometimes we depend on theorems that themselves or similar ones
-- are present in Mathlib, but to reduce dependencies, we prove them here

-- NOTE: usually, the unification is not strong enough to figure out `p`,
-- which would be supplied by the user in practice
theorem find_min {p : Nat → Prop} (n : Nat) (h : p n) :
  ∃ n', n' ≤ n ∧ p n' ∧ ∀ m, m < n' → ¬ p m := by
  induction n using Nat.strongRecOn
  rename_i n ih
  by_cases h' : ∃ m, m < n ∧ p m
  · rcases h' with ⟨m, hlt, h'⟩
    have ⟨n', hle, ha, hb⟩ := ih _ hlt h'
    exists n'; apply And.intro (by omega) (And.intro ‹_› ‹_›)
  · simp at h'; exists n; simp_all

theorem find_min' {p : Nat → Prop} (n : Nat) (h : p n) :
  ∃ n', n' ≤ n ∧ p n' ∧ ∀ m, p m → n' ≤ m := by
  have ⟨n', hn', ha, hb⟩ := find_min _ h
  exists n'; apply And.intro ‹_› (And.intro ‹_› _); intros; apply Nat.le_of_not_lt; intro hlt; solve_by_elim

end Nat

end LentilLib
