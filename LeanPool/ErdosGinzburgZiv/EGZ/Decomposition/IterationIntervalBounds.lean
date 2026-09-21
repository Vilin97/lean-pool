/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.StoppedLineages

/-! # Bounds after restarting and stopping a finite interval -/

namespace EGZ.FlagDecomposition.Iteration


open Classical in
theorem card_filter_range_offset (χ : ℕ → ℕ) (a b l : ℕ) (hab : a ≤ b) :
    ((Finset.range (b + 1 - a)).filter fun i ↦ χ (a + i) = l).card =
      ((Finset.Icc a b).filter fun i ↦ χ i = l).card := by
  apply Finset.card_bij (fun i _ ↦ a + i)
  · intro i hi
    obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, heq⟩
  · intro i _ j _ hij
    omega
  · intro j hj
    obtain ⟨hj, heq⟩ := Finset.mem_filter.mp hj
    obtain ⟨haj, hjb⟩ := Finset.mem_Icc.mp hj
    refine ⟨j - a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, by omega⟩
    simpa only [Nat.add_sub_of_le haj] using heq

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}

open Classical in
theorem intervalState_mass_tail {s : ℕ → State p d f} {ε : ℝ} {a n N : ℕ}
    (hbound : a + n ≤ N)
    (htail : ∀ i j, i ≤ j → j ≤ N →
      ((s i).decomposition.retainedMass : ℝ) - (s j).decomposition.retainedMass ≤
        ε ^ 2 / 4 * (s i).decomposition.retainedMass)
    (i j : ℕ) (hij : i ≤ j) :
    ((intervalState s a n i).decomposition.retainedMass : ℝ) -
      (intervalState s a n j).decomposition.retainedMass ≤
        ε ^ 2 / 4 * (intervalState s a n i).decomposition.retainedMass :=
  htail (a + min i n) (a + min j n)
    (Nat.add_le_add_left (min_le_min_right n hij) a)
    ((Nat.add_le_add_left (min_le_right j n) a).trans hbound)

open Classical in
@[simp]
theorem intervalState_zero (s : ℕ → State p d f) (a n : ℕ) :
    intervalState s a n 0 = s a := by simp [intervalState]

end EGZ.FlagDecomposition.Iteration
