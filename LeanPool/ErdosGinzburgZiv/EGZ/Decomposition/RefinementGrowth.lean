/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic
import Mathlib.Order.Iterate

/-!
# Growth functions for completeness refinements

One step of the width sequence dominates the requested width after changing
to the bounded lattice coordinates. The same sequence bounds every possible
number of added directions up to the ambient dimension.
-/

namespace EGZ

def refinementGrowth (A g : ℕ → ℕ) (n : ℕ) : ℕ := max (n + 1) (g (A n))

theorem refinementGrowth_isGrowing {A g : ℕ → ℕ} (hA : Monotone A) (hg : Monotone g) :
    IsGrowing (refinementGrowth A g) := by
  constructor
  · intro a b hab
    exact max_le_max (Nat.add_le_add_right hab 1) (hg (hA hab))
  · intro n
    exact (Nat.lt_succ_self n).trans_le (le_max_left _ _)

def refinementWidth (A g : ℕ → ℕ) (K i : ℕ) : ℕ := (refinementGrowth A g)^[i] K

@[simp]
theorem refinementWidth_zero (A g : ℕ → ℕ) (K : ℕ) : refinementWidth A g K 0 = K := rfl

theorem refinementWidth_succ (A g : ℕ → ℕ) (K i : ℕ) :
    refinementWidth A g K (i + 1) = refinementGrowth A g (refinementWidth A g K i) :=
  Function.iterate_succ_apply' _ _ _

theorem refinementWidth_mono (A g : ℕ → ℕ) (K : ℕ) : Monotone (refinementWidth A g K) := by
  intro i j hij
  exact Function.monotone_iterate_of_id_le
    (fun n ↦ (Nat.le_succ n).trans (le_max_left _ _)) hij K

theorem le_refinementWidth (A g : ℕ → ℕ) (K i : ℕ) : K ≤ refinementWidth A g K i :=
  refinementWidth_mono A g K (Nat.zero_le i)

theorem desired_width_le_refinementWidth_succ (A g : ℕ → ℕ) (K i : ℕ) :
    g (A (refinementWidth A g K i)) ≤ refinementWidth A g K (i + 1) := by
  rw [refinementWidth_succ]
  exact le_max_right _ _

theorem refinementWidth_le_of_index_le (A g : ℕ → ℕ) (K : ℕ) {i d : ℕ} (hi : i ≤ d) :
    refinementWidth A g K i ≤ refinementWidth A g K d := refinementWidth_mono A g K hi

theorem refinementWidth_mono_initial {A g : ℕ → ℕ} (hA : Monotone A) (hg : Monotone g)
    (i : ℕ) : Monotone (fun K ↦ refinementWidth A g K i) :=
  (refinementGrowth_isGrowing hA hg).1.iterate i

end EGZ
