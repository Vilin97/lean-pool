/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Lemmas
import Mathlib.Tactic

namespace List

variable {α β : Type*} {x y z : List α}

section append_append

lemma length_append_append :
  (x ++ y ++ z).length = x.length + y.length + z.length :=
by
  rw [length_append, length_append]

lemma map_append_append {f : α → β} :
  (x ++ y ++ z).map f = x.map f ++ y.map f ++ z.map f :=
by
  rw [map_append, map_append]

lemma filterMap_append_append {f : α → Option β} :
  (x ++ y ++ z).filterMap f = x.filterMap f ++ y.filterMap f ++ z.filterMap f :=
by
  rw [filterMap_append, filterMap_append]

lemma reverse_append_append :
  (x ++ y ++ z).reverse = z.reverse ++ y.reverse ++ x.reverse :=
by
  rw [reverse_append, reverse_append, append_assoc]

lemma mem_append_append {a : α} :
  a ∈ x ++ y ++ z ↔ a ∈ x ∨ a ∈ y ∨ a ∈ z :=
by
  rw [mem_append, mem_append, or_assoc]

lemma forall_mem_append_append {p : α → Prop} :
  (∀ a ∈ x ++ y ++ z, p a) ↔ (∀ a ∈ x, p a) ∧ (∀ a ∈ y, p a) ∧ (∀ a ∈ z, p a) :=
by
  rw [forall_mem_append, forall_mem_append, and_assoc]

lemma flatten_append_append {X Y Z : List (List α)} :
  (X ++ Y ++ Z).flatten = X.flatten ++ Y.flatten ++ Z.flatten :=
by
  rw [flatten_append, flatten_append]

end append_append

section replicating_succ

lemma replicate_succ_eq_singleton_append (s : α) (n : ℕ) :
  replicate n.succ s = [s] ++ replicate n s :=
rfl

lemma replicate_succ_eq_append_singleton (s : α) (n : ℕ) :
  replicate n.succ s = replicate n s ++ [s] :=
by
  change replicate (n + 1) s = replicate n s ++ [s]
  rw [replicate_add]
  rfl

end replicating_succ

section joining

private lemma cons_drop_succ {m : ℕ} (mlt : m < x.length) :
  x.drop m = x.get ⟨m, mlt⟩ :: x.drop m.succ :=
by
  induction' x with d l ih generalizing m
  · exfalso
    rw [length] at mlt
    exact Nat.not_lt_zero m mlt
  cases m
  · rw [get]
    simp
  rw [drop, drop, get]
  apply ih

-- proof copied from https://github.com/leanprover/lean4/blob/master/src/Init/Data/List/Nat/TakeDrop.lean
lemma take_append' (l₁ l₂ : List α) (n : ℕ) :
  (l₁ ++ l₂).take n = l₁.take n ++ l₂.take (n - l₁.length) :=
by
  induction l₁ generalizing n
  · simp
  · cases n
    · simp [*]
    · simp only [cons_append, take_succ_cons, length_cons, cons.injEq, append_cancel_left_eq, true_and, *]
      congr 1
      omega

-- proof copied from https://github.com/leanprover/lean4/blob/master/src/Init/Data/List/Nat/TakeDrop.lean
lemma drop_append' (l₁ l₂ : List α) (n : ℕ) :
  (l₁ ++ l₂).drop n = l₁.drop n ++ l₂.drop (n - l₁.length) :=
by
  induction l₁ generalizing n
  · simp
  · cases n
    · simp [*]
    · simp only [cons_append, drop_succ_cons, length_cons, append_cancel_left_eq, *]
      congr 1
      omega

-- proved by Patrick Johnson; ported to Lean 4 by Vlad
lemma take_flatten_of_lt {L : List (List α)} {n : ℕ} (hnL : n < L.flatten.length) :
  ∃ m k : ℕ, ∃ mlt : m < L.length,
    k < (L.get ⟨m, mlt⟩).length ∧
    L.flatten.take n = (L.take m).flatten ++ (L.get ⟨m, mlt⟩).take k :=
by
  simp at hnL; have h₂ : ∃ m, n < ((L.take m).map length).sum; use L.length; simpa
  generalize hm : Nat.find h₂ = m; have h₃ := Nat.find_spec h₂
  have h₅ := @Nat.find_min' (H := h₂) _ _; rw [hm] at h₃ h₅
  have h₄ := @h₅ L.length (by simp at hnL ⊢; exact hnL)
  cases m; simp at h₃; rename_i m; rw [Nat.succ_le_iff] at h₄
  specialize @h₅ m; simp at h₅; use m; simp [h₄]
  generalize hr : (L.map length |>.take m).sum = r at h₅
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₅; use n
  simp [take_add, ←take_sum_flatten, hr]
  have h₂ : L = L.take m ++ L.drop m; simp
  rw [h₂] at h₃; simp [-take_append_drop] at h₃; rw [take_append'] at h₃; simp at h₃
  rw [take_take] at h₃; simp [hr] at h₃; rw [min_eq_left_of_lt h₄] at h₃; simp at h₃
  rw [take_one] at h₃; simp [getElem?_eq_getElem h₄] at h₃; use h₃
  rw [←drop_take_succ_flatten_eq_getElem, hr, take_sum_flatten, take_add,
    flatten_append, drop_append']; simp [hr]
  simp [show L.flatten.drop r = (L.drop m).flatten by subst hr; apply drop_sum_flatten,
    ←show L.flatten.take r = (L.take m).flatten by subst hr; apply take_sum_flatten]
  generalize hM : L.drop m = M
  have h₇ : 0 < M.length; simpa [←hM]
  have h₈ : M.take 1 = [M[0]]
  · simp [←hM, take_one, head?_drop]
    aesop
  simp [h₈]; rw [show L[m] = M[0] by simp [←hM]] at h₃
  cases M; simp at h₈; simp at h₃; simp [le_of_lt h₃]

lemma drop_flatten_of_lt {L : List (List α)} {n : ℕ} (notall : n < L.flatten.length) :
  ∃ m k : ℕ, ∃ mlt : m < L.length,
    k < (L.get ⟨m, mlt⟩).length ∧
    L.flatten.drop n = (L.get ⟨m, mlt⟩).drop k ++ (L.drop m.succ).flatten :=
by
  obtain ⟨m, k, mlt, klt, left_half⟩ := take_flatten_of_lt notall
  use m, k, mlt, klt
  have L_two_parts := congr_arg flatten (take_append_drop m L)
  rw [flatten_append] at L_two_parts
  have whole := take_append_drop n L.flatten
  rw [left_half] at whole
  have important := whole.trans L_two_parts.symm
  rw [append_assoc] at important
  have right_side := append_cancel_left important
  have auxi : (drop m L).flatten = (L.get ⟨m, mlt⟩ :: drop m.succ L).flatten
  · apply congr_arg
    apply cons_drop_succ
  rw [flatten] at auxi
  rw [auxi] at right_side
  have near_result :
    take k (L.get ⟨m, mlt⟩) ++ drop n L.flatten =
    take k (L.get ⟨m, mlt⟩) ++ drop k (L.get ⟨m, mlt⟩) ++ (drop m.succ L).flatten
  · convert right_side
    rw [take_append_drop]
  rw [append_assoc] at near_result
  exact append_cancel_left near_result

def nTimes (l : List α) (n : ℕ) : List α :=
  (replicate n l).flatten

infixl:100 " ^^ " => nTimes

end joining

section indexing

lemma get_map (f : α → β) (l : List α) (i : Fin (l.map f).length) :
  (l.map f).get i = f (l.get (congr_arg Fin (l.length_map f) ▸ i)) :=
by
  simp
  congr
  · simp
  · simp

end indexing

variable [DecidableEq α]

section counting

def countIn (l : List α) (a : α) : ℕ :=
  sum (map (if · = a then 1 else 0) l)

lemma countIn_nil (a : α) :
  countIn [] a = 0 :=
rfl

lemma countIn_cons (a b : α) :
  countIn (b::x) a = (if b = a then 1 else 0) + countIn x a :=
by
  unfold countIn
  rw [map_cons, sum_cons]

lemma countIn_append (a : α) :
  countIn (x ++ y) a = countIn x a + countIn y a :=
by
  unfold countIn
  rw [map_append, sum_append]

lemma countIn_replicate_eq (a : α) (n : ℕ) :
  countIn (replicate n a) a = n :=
by
  unfold countIn
  induction' n with m ih
  · rfl
  rw [replicate_succ, map_cons, sum_cons, ih, if_pos rfl]
  apply Nat.one_add

lemma countIn_replicate_neq {a b : α} (hab : a ≠ b) (n : ℕ) :
  countIn (replicate n a) b = 0 :=
by
  unfold countIn
  induction' n with m ih
  · rfl
  rw [replicate_succ, map_cons, sum_cons, ih, Nat.add_zero, ite_eq_right_iff]
  intro impos
  exfalso
  exact hab impos

lemma countIn_singleton_eq (a : α) :
  countIn [a] a = 1 :=
countIn_replicate_eq a 1

lemma countIn_singleton_neq {a b : α} (hab : a ≠ b) :
  countIn [a] b = 0 :=
countIn_replicate_neq hab 1

lemma countIn_pos_of_in {a : α} (hax : a ∈ x) :
  countIn x a > 0 :=
by
  induction' x with d l ih
  · exfalso
    rw [mem_nil_iff] at hax
    exact hax
  by_contra contr
  rw [not_lt, Nat.le_zero] at contr
  rw [mem_cons] at hax
  unfold countIn map at contr
  simp at contr
  cases' hax with a_eq_d a_in_l
  · exact contr.left a_eq_d.symm
  specialize ih a_in_l
  have zero_in_tail : countIn l a = 0
  · unfold countIn
    exact contr.right
  rw [zero_in_tail] at ih
  exact Nat.lt_irrefl 0 ih

lemma countIn_zero_of_notin {a : α} (hax : a ∉ x) :
  countIn x a = 0 :=
by
  induction' x with d l ih
  · rfl
  unfold countIn
  rw [map_cons, sum_cons, Nat.add_eq_zero_iff, ite_eq_right_iff]
  constructor
  · simp only [Nat.one_ne_zero]
    exact (ne_of_not_mem_cons hax).symm
  · exact ih (not_mem_of_not_mem_cons hax)

lemma countIn_flatten (L : List (List α)) (a : α) :
  countIn L.flatten a = sum (map (countIn · a) L) :=
by
  induction' L with d l ih
  · rfl
  · rw [flatten, countIn_append, map, sum_cons, ih]

end counting

end List
