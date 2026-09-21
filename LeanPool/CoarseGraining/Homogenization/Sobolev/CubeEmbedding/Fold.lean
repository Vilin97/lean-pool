/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.WeakDerivatives
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Fin.Tuple.Basic

/-! # Fold -/

namespace Homogenization

open Homogenization
open scoped BigOperators

/-!
# The even-periodic fold onto a box

The coordinatewise even fold of `ℝ` onto the interval `[lo, hi]` with margin
equal to the side length: identity on `[lo, hi]`, reflected across `lo` below
and across `hi` above.  Applied coordinatewise it gives `Fold : Vec d → Vec d`,
and the extension of a function `v` is `v ∘ Fold`.  There are only two kinks per
coordinate; the fold is `1`-Lipschitz and equals the identity on the closed box.
-/

noncomputable section

variable {d : ℕ}

/-- Scalar even fold of `ℝ` onto `[lo, hi]`: reflected across `lo` below, across
`hi` above, identity in between. -/
def foldR (lo hi t : ℝ) : ℝ :=
  if t < lo then 2 * lo - t else if hi < t then 2 * hi - t else t

/-- The (right) derivative sign of `foldR`: `-1` on the reflected pieces, `+1` in
the interior. -/
def foldSign (lo hi t : ℝ) : ℝ :=
  if t < lo then -1 else if hi < t then -1 else 1

/-- The coordinatewise fold onto the box `[lo, hi]`. -/
def Fold (lo hi : Vec d) (x : Vec d) : Vec d :=
  fun j => foldR (lo j) (hi j) (x j)

@[simp] theorem foldR_of_mem {lo hi t : ℝ} (h1 : lo ≤ t) (h2 : t ≤ hi) :
    foldR lo hi t = t := by
  unfold foldR
  rw [if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h2)]

theorem continuous_foldR (lo hi : ℝ) (h : lo ≤ hi) : Continuous (foldR lo hi) := by
  have hB : Continuous (fun t => if hi < t then 2 * hi - t else t) := by
    have hEq : (fun t => if hi < t then 2 * hi - t else t)
        = fun t => if t ≤ hi then t else 2 * hi - t := by
      funext t; by_cases ht : hi < t
      · rw [if_pos ht, if_neg (not_le.mpr ht)]
      · rw [if_neg ht, if_pos (not_lt.mp ht)]
    rw [hEq]
    exact Continuous.if_le continuous_id (continuous_const.sub continuous_id)
      continuous_id continuous_const (fun x hx => by rw [hx]; ring)
  have hEq : foldR lo hi
      = fun t => if lo ≤ t then (if hi < t then 2 * hi - t else t) else 2 * lo - t := by
    funext t; unfold foldR
    by_cases ht : t < lo
    · rw [if_pos ht, if_neg (not_le.mpr ht)]
    · rw [if_neg ht, if_pos (not_lt.mp ht)]
  rw [hEq]
  refine Continuous.if_le hB (continuous_const.sub continuous_id) continuous_const
    continuous_id (fun x hx => ?_)
  subst hx
  rw [if_neg (not_lt.mpr h)]; ring

theorem continuous_Fold (lo hi : Vec d) (hlohi : ∀ j, lo j ≤ hi j) :
    Continuous (Fold lo hi) := by
  refine continuous_pi (fun j => ?_)
  exact (continuous_foldR (lo j) (hi j) (hlohi j)).comp (continuous_apply j)

/-- The fold is the identity on the closed box. -/
theorem Fold_of_mem {lo hi : Vec d} {x : Vec d}
    (h : ∀ j, lo j ≤ x j ∧ x j ≤ hi j) : Fold lo hi x = x := by
  funext j
  exact foldR_of_mem (h j).1 (h j).2

/-- Expansion of the fold along an insertion line: only the `j`-coordinate varies,
through `foldR (lo j) (hi j) t`; the tangential coordinates are frozen. -/
theorem Fold_insertNth {n : ℕ} (lo hi : Vec (n + 1)) (j : Fin (n + 1))
    (t : ℝ) (z : Vec n) :
    Fold lo hi (j.insertNth t z)
      = j.insertNth (foldR (lo j) (hi j) t)
          (fun m => foldR (lo (j.succAbove m)) (hi (j.succAbove m)) (z m)) := by
  funext k
  rcases eq_or_ne k j with h | h
  · subst h
    simp only [Fold, Fin.insertNth_apply_same]
  · obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq h
    simp only [Fold, Fin.insertNth_apply_succAbove]

end

end Homogenization
