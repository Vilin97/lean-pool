/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Length and indexing of concatenated pairs

Flattening a list of two-element blocks doubles its length and
places the two components at the even and odd positions.
-/

@[expose] public section

namespace RS

/-- A list of pairs has twice as many entries as its source. -/
theorem len_flatMap_pair {α β : Type*} (L : List α) (f g : α → β) :
    (L.flatMap (fun x => [f x, g x])).length = 2 * L.length := by
  induction L with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih]; omega

-- The index arithmetic under the flat-map is
-- carried through a list induction.
/-- Even positions in a list of pairs come from the first component. -/
theorem getElem?_flatMap_pair_even {α β : Type*}
    (L : List α) (f g : α → β) (j : ℕ) :
    (L.flatMap (fun x => [f x, g x]))[2 * j]? = L[j]?.map f := by
  induction L generalizing j with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons]; cases j with
    | zero => simp
    | succ j =>
      rw [show 2 * (j + 1) = 2 + 2 * j from by omega,
          List.getElem?_append_right
            (show ([f a, g a] : List _).length ≤ 2 + 2 * j from by simp)]
      simp only [show ([f a, g a] : List _).length = 2 from rfl,
                  show 2 + 2 * j - 2 = 2 * j from by omega,
                  List.getElem?_cons_succ]
      exact ih j

-- As for the even positions.
/-- Odd positions in a list of pairs come from the second component. -/
theorem getElem?_flatMap_pair_odd {α β : Type*}
    (L : List α) (f g : α → β) (j : ℕ) :
    (L.flatMap (fun x => [f x, g x]))[2 * j + 1]? = L[j]?.map g := by
  induction L generalizing j with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons]; cases j with
    | zero => simp
    | succ j =>
      rw [show 2 * (j + 1) + 1 = 2 + (2 * j + 1) from by omega,
          List.getElem?_append_right
            (show ([f a, g a] : List _).length ≤ 2 + (2 * j + 1) from by simp)]
      simp only [show ([f a, g a] : List _).length = 2 from rfl,
                  show 2 + (2 * j + 1) - 2 = 2 * j + 1 from by omega,
                  List.getElem?_cons_succ]
      exact ih j

/-- In a flatMap of [x, h x] blocks, element 2j+1 is h applied to element 2j. -/
theorem getElem?_self_paired {α : Type*}
    (L : List α) (h : α → α) (j : ℕ) :
    (L.flatMap (fun x => [x, h x]))[2 * j + 1]? =
    (L.flatMap (fun x => [x, h x]))[2 * j]?.map h := by
  have key : (fun x => ([x, h x] : List α)) = (fun x => [id x, h x]) := by
    ext; simp
  rw [key, getElem?_flatMap_pair_even L id h j,
      getElem?_flatMap_pair_odd L id h j, Option.map_map]
  simp

/-- The entry at an even position is the first component. -/
theorem getElem_flatMap_pair_even {α β : Type*}
    (L : List α) (f g : α → β) (j : ℕ) (hj : j < L.length) :
    (L.flatMap (fun x => [f x, g x]))[2 * j]'(by
      rw [len_flatMap_pair]; omega) = f L[j] := by
  have h := getElem?_flatMap_pair_even L f g j
  rw [List.getElem?_eq_getElem (by rw [len_flatMap_pair]; omega),
      List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

/-- The entry at an odd position is the second component. -/
theorem getElem_flatMap_pair_odd {α β : Type*}
    (L : List α) (f g : α → β) (j : ℕ) (hj : j < L.length) :
    (L.flatMap (fun x => [f x, g x]))[2 * j + 1]'(by
      rw [len_flatMap_pair]; omega) = g L[j] := by
  have h := getElem?_flatMap_pair_odd L f g j
  rw [List.getElem?_eq_getElem (by rw [len_flatMap_pair]; omega),
      List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

end RS
