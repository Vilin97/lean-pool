/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.FlagGraph

/-!
# Fragment composition

Composition of fragments (`Fragment.compose`, defined in
`RS/Definitions.lean`) glues the last `t` boundary labels of an
`(s + t)`-fragment to the first `t` of a `(t + u)`-fragment through
the iterated single-pair primitive, re-indexing the surviving
labels by one-point removals.

This module carries the value computations for those removals: the
gluing chain rewrites boundary states through the re-indexings, so
it needs each surviving label's new index as an explicit natural
number.
-/

namespace RS

/-! ### Value computation for the one-point removals

A removal is inverted by `Fin.succAbove`, which shifts the indices
at or above the removed point up by one.  Reading that off gives
each surviving label's new index as an explicit natural number. -/

/-- `Fin.succAbove` shifts the indices at or above `a` up by one. -/
private theorem succAbove_val_ite {n : ℕ} (a : Fin (n + 1)) (y : Fin n) :
    ((a.succAbove y : Fin (n + 1)) : ℕ) =
      if (y : ℕ) < (a : ℕ) then (y : ℕ) else (y : ℕ) + 1 := by
  by_cases hc : Fin.castSucc y < a
  · rw [Fin.succAbove_of_castSucc_lt _ _ hc]
    have h1 : (y : ℕ) < (a : ℕ) := hc
    rw [if_pos h1]
    rfl
  · have hc' : a ≤ Fin.castSucc y := not_lt.mp hc
    rw [Fin.succAbove_of_le_castSucc _ _ hc']
    have h1 : (a : ℕ) ≤ (y : ℕ) := hc'
    rw [if_neg (not_lt.mpr h1)]
    rfl

/-- Inverting that shift: a label above the removed point drops by
one, a label below it keeps its index. -/
private theorem removed_val_ite {n : ℕ} {a : Fin (n + 1)} {y : Fin n}
    {v : ℕ} (h : ((a.succAbove y : Fin (n + 1)) : ℕ) = v) :
    (y : ℕ) = if v < (a : ℕ) then v else v - 1 := by
  rw [succAbove_val_ite] at h
  by_cases hc : (y : ℕ) < (a : ℕ)
  · rw [if_pos hc] at h
    rw [if_pos (by omega)]
    omega
  · rw [if_neg hc] at h
    rw [if_neg (by omega)]
    omega

/-- `Fin.succAbove` at the removed point inverts `finRemoveEquiv`. -/
theorem finRemoveEquiv_apply_val {n : ℕ} (a : Fin (n + 1))
    (x : {x : Fin (n + 1) // x ≠ a}) :
    a.succAbove (finRemoveEquiv a x) = x.val :=
  congrArg Subtype.val ((finRemoveEquiv a).symm_apply_apply x)

/-- The index a surviving label takes after a one-point removal. -/
theorem finRemoveEquiv_val {n : ℕ} (a : Fin (n + 1))
    (x : {x : Fin (n + 1) // x ≠ a}) :
    (finRemoveEquiv a x : ℕ) =
      if (x.val : ℕ) < (a : ℕ) then (x.val : ℕ) else (x.val : ℕ) - 1 :=
  removed_val_ite (congrArg Fin.val (finRemoveEquiv_apply_val a x))

/-- Removing the top point leaves every surviving label's index
unchanged. -/
theorem finRemoveEquiv_top_val {n : ℕ}
    (x : {x : Fin (n + 1) // x ≠ ⟨n, Nat.lt_succ_self n⟩}) :
    (finRemoveEquiv ⟨n, Nat.lt_succ_self n⟩ x : ℕ) = (x.val : ℕ) := by
  have h := finRemoveEquiv_val ⟨n, Nat.lt_succ_self n⟩ x
  have hx : (x.val : ℕ) ≠ n := fun hh => x.prop (Fin.ext hh)
  have hb : (x.val : ℕ) < n + 1 := x.val.isLt
  have ha : ((⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) : ℕ) = n := rfl
  rw [h, ha, if_pos (by omega)]

/-- `Fin.succAbove` at `t` inverts `rightRemoveEquiv`. -/
theorem rightRemoveEquiv_apply_val (t u : ℕ)
    (x : {x : Fin (t + 1 + u) // x ≠ ⟨t, by omega⟩}) :
    (((⟨t, by omega⟩ : Fin (t + u + 1)).succAbove
        (rightRemoveEquiv t u x) : Fin (t + u + 1)) : ℕ) =
      (x.val : ℕ) :=
  congrArg (fun z : {x : Fin (t + 1 + u) // x ≠ ⟨t, by omega⟩} =>
      (z.val : ℕ))
    ((rightRemoveEquiv t u).symm_apply_apply x)

/-- The index a surviving label takes after removing label `t` on
the right. -/
theorem rightRemoveEquiv_val (t u : ℕ)
    (x : {x : Fin (t + 1 + u) // x ≠ ⟨t, by omega⟩}) :
    (rightRemoveEquiv t u x : ℕ) =
      if (x.val : ℕ) < t then (x.val : ℕ) else (x.val : ℕ) - 1 :=
  removed_val_ite (rightRemoveEquiv_apply_val t u x)

end RS
