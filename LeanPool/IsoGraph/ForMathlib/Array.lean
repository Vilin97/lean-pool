/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Lemmas about arrays and `getElem!`

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/


theorem array_extD {α : Type _} [Inhabited α] {a b : Array α} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]! = b[i]!) : a = b := by
  refine Array.ext hs fun i hi hi' => ?_
  have := h i hi
  rwa [getElem!_pos a i hi, getElem!_pos b i hi'] at this

theorem mem_iff_getElemD {a : Array Nat} {v : Nat} : v ∈ a ↔ ∃ i, i < a.size ∧ a[i]! = v := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 h
    exact ⟨i, hi, by rw [getElem!_pos a i hi]⟩
  · rintro ⟨i, hi, rfl⟩
    rw [getElem!_pos a i hi]
    exact Array.getElem_mem hi

/-- An in-bounds `getElem!` is a member. -/
theorem getElemD_mem {a : Array Nat} {j : Nat} (h : j < a.size) : a[j]! ∈ a := by
  rw [getElem!_pos a j h]
  exact Array.getElem_mem h

/-- Reading one entry of `Array.set!`, the only fact about it these proofs need. -/
theorem getElemD_setD {α : Type _} [Inhabited α] {a : Array α} {i : Nat} {x : α}
    (hi : i < a.size) (k : Nat) :
    (a.set! i x)[k]! = if k = i then x else a[k]! := by
  by_cases hk : k < a.size
  · rw [getElem!_pos (a.set! i x) k (by simpa using hk), getElem!_pos a k hk]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hk, eq_comm (a := i)]
  · rw [getElem!_neg (a.set! i x) k (by simpa using hk), getElem!_neg a k hk,
      ite_eq_right (by omega)]

/-- Companion to `getElemD_setD` for the off-diagonal case, where no bound on `i` is needed:
writing at `i` never disturbs another index, in bounds or not. -/
theorem getElemD_setD_ne {α : Type _} [Inhabited α] {a : Array α} {i : Nat} {x : α} {k : Nat}
    (h : k ≠ i) :
    (a.set! i x)[k]! = a[k]! := by
  by_cases hk : k < a.size
  · rw [getElem!_pos (a.set! i x) k (by simpa using hk), getElem!_pos a k hk]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hk,
      ite_eq_right (Ne.symm h)]
  · rw [getElem!_neg (a.set! i x) k (by simpa using hk), getElem!_neg a k hk]

/-- Distinct positions of a duplicate-free array hold distinct values. -/
theorem nodup_getElemD_ne {a : Array Nat} (h : a.toList.Nodup) {i j : Nat} (hi : i < a.size)
    (hj : j < a.size) (hij : i ≠ j) : a[i]! ≠ a[j]! := by
  rw [getElem!_pos a i hi, getElem!_pos a j hj]
  intro he
  exact hij ((List.Nodup.getElem_inj_iff h).mp he)

/-- An array whose entries at distinct indices differ has no duplicates. -/
theorem nodup_of_getElemD_ne {a : Array Nat}
    (h : ∀ i j, i < a.size → j < a.size → i < j → a[i]! ≠ a[j]!) : a.toList.Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < a.size := by simpa using hi
  have hj' : j < a.size := by simpa using hj
  have := h i j hi' hj' hij
  rwa [getElem!_pos a i hi', getElem!_pos a j hj'] at this

theorem pairwise_getElemD_le {a : Array Nat} (hp : a.toList.Pairwise (· ≤ ·)) {i j : Nat}
    (hj : j < a.size) (hij : i ≤ j) : a[i]! ≤ a[j]! := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · subst h; exact le_refl _
  · have hi : i < a.size := by omega
    have := List.pairwise_iff_getElem.1 hp i j (by simpa using hi) (by simpa using hj) h
    rwa [getElem!_pos a i hi, getElem!_pos a j hj, ← Array.getElem_toList, ← Array.getElem_toList]

theorem pairwise_getElemD_lt {a : Array Nat} (hp : a.toList.Pairwise (· ≤ ·))
    (hnd : a.toList.Nodup) {i j : Nat} (hj : j < a.size) (hij : i < j) : a[i]! < a[j]! := by
  have hi : i < a.size := by omega
  have hle : a[i]! ≤ a[j]! := by
    have := List.pairwise_iff_getElem.1 hp i j (by simpa using hi) (by simpa using hj) hij
    rwa [getElem!_pos a i hi, getElem!_pos a j hj, ← Array.getElem_toList, ← Array.getElem_toList]
  exact lt_of_le_of_ne hle (nodup_getElemD_ne hnd hi hj (by omega))

theorem arr_isEmpty_iff (a : Array Nat) : a.isEmpty = true ↔ ∀ x, x ∉ a := by
  rw [Array.isEmpty_iff]
  constructor
  · intro h x hx
    rw [h] at hx
    simp at hx
  · intro h
    exact Array.ext' (List.eq_nil_iff_forall_not_mem.2 fun x hx => h x (by simpa using hx))

theorem push_getElemD_eq {α : Type} [Inhabited α] (a : Array α) (v : α) :
    (a.push v)[a.size]! = v := by
  rw [getElem!_pos (a.push v) a.size (by rw [Array.size_push]; omega)]
  simp

theorem push_getElemD_lt {α : Type} [Inhabited α] (a : Array α) (v : α) {i : Nat}
    (hi : i < a.size) : (a.push v)[i]! = a[i]! := by
  rw [getElem!_pos (a.push v) i (by rw [Array.size_push]; omega), getElem!_pos a i hi,
    Array.getElem_push_lt hi]

theorem extract_self (a : Array Nat) : a.extract 0 a.size = a := by
  apply Array.ext'; simp

theorem extract_size {a : Array Nat} {j : Nat} (hj : j ≤ a.size) : (a.extract 0 j).size = j := by
  simp; omega

theorem extract_getElemD {a : Array Nat} {j i : Nat} (hi : i < j) :
    (a.extract 0 j)[i]! = a[i]! := by
  rcases Nat.lt_or_ge i a.size with h | h
  · rw [getElem!_pos (a.extract 0 j) i (by simp; omega), getElem!_pos a i h]
    simp
  · rw [getElem!_neg (a.extract 0 j) i (by simp; omega), getElem!_neg a i (by omega)]

theorem push_extract {a : Array Nat} {v j : Nat} (hj : j ≤ a.size) :
    (a.push v).extract 0 j = a.extract 0 j := by
  apply Array.ext'
  simp only [Array.toList_extract, Array.toList_push, List.extract_eq_take_drop, Nat.sub_zero,
    List.drop_zero]
  rw [List.take_append_of_le_length (by simpa using hj)]

theorem take_toList_eq {a b : Array Nat} {j : Nat} (hja : j ≤ a.size) (hjb : j ≤ b.size)
    (h : ∀ k, k < j → a[k]! = b[k]!) : a.toList.take j = b.toList.take j := by
  refine List.ext_getElem (by simp; omega) fun k hk1 hk2 => ?_
  simp only [List.length_take, Array.length_toList, Nat.lt_min] at hk1
  have hka : k < a.toList.length := by simp; omega
  have hkb : k < b.toList.length := by simp; omega
  rw [List.getElem_take, List.getElem_take,
    show a.toList[k] = a[k]! by rw [getElem!_pos a k (by simpa using hka)]; simp,
    show b.toList[k] = b[k]! by rw [getElem!_pos b k (by simpa using hkb)]; simp]
  exact h k hk1.1

theorem take_getElemD_self {c : Array Nat} {j i : Nat} (hi : i < j) (hic : i < c.size) :
    (c.toList.take j)[i]! = c[i]! := by
  rw [getElem!_pos (c.toList.take j) i (by simp; omega), List.getElem_take, getElem!_pos c i hic]
  simp

theorem take_getElemD {a b : Array Nat} {j : Nat} (h : a.toList.take j = b.toList.take j)
    {i : Nat} (hi : i < j) (hia : i < a.size) : a[i]! = b[i]! := by
  have hlen : min j a.size = min j b.size := by simpa using congrArg List.length h
  have hib : i < b.size := by omega
  rw [← take_getElemD_self hi hia, ← take_getElemD_self hi hib, h]

theorem replicate_getElemD_false {n w : Nat} : (Array.replicate n false)[w]! = false := by
  by_cases h : w < n
  · rw [getElem!_pos (Array.replicate n false) w (by simpa using h)]; simp
  · rw [getElem!_neg (Array.replicate n false) w (by simpa using h)]; rfl
