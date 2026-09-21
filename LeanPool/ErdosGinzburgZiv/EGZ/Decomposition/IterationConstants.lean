/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationBounds
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IntervalCapacity

/-! # Uniform constants for the bounded decomposition iteration -/

namespace EGZ.FlagDecomposition.Iteration

/-- A positive integer upper bound for face events on one surviving lineage. -/
noncomputable def faceCapacity (d : ℕ) (ε : ℝ) : ℕ :=
  max 1 ⌈((((ε / 2) ^ 3)⁻¹ + (d : ℝ) + 2) ^ (d + 2))⌉₊

theorem one_le_faceCapacity (d : ℕ) (ε : ℝ) : 1 ≤ faceCapacity d ε := le_max_left _ _

theorem le_faceCapacity_of_real_le {d n : ℕ} {ε : ℝ}
    (h : (n : ℝ) ≤ (((ε / 2) ^ 3)⁻¹ + (d : ℝ) + 2) ^ (d + 2)) :
    n ≤ faceCapacity d ε := by
  have hn : n ≤ ⌈((((ε / 2) ^ 3)⁻¹ + (d : ℝ) + 2) ^ (d + 2))⌉₊ := by
    exact_mod_cast h.trans (Nat.le_ceil _)
  exact hn.trans (le_max_right _ _)

noncomputable def intervalCapacity (d : ℕ) (ε : ℝ) (a : ℕ) : ℕ :=
  2 ^ a * faceCapacity d ε

theorem pow_le_intervalCapacity (d : ℕ) (ε : ℝ) (a : ℕ) :
    2 ^ a ≤ intervalCapacity d ε a := by
  change 2 ^ a ≤ 2 ^ a * faceCapacity d ε
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ a) (one_le_faceCapacity d ε)

theorem one_le_intervalCapacity (d : ℕ) (ε : ℝ) (a : ℕ) :
    1 ≤ intervalCapacity d ε a :=
  (Nat.one_le_two_pow).trans (pow_le_intervalCapacity d ε a)

noncomputable def stoppingBound (d : ℕ) (ε : ℝ) : ℕ :=
  intervalCapacityBound (2 * (d + 1) ^ 2 + 1) (intervalCapacity d ε)

theorem stoppingBound_pos (d : ℕ) (ε : ℝ) : 0 < stoppingBound d ε := by
  apply length_lt_intervalCapacityBound _ _ 0 (fun _ ↦ 0)
  · intro i hi
    omega
  · intro a b l _ hb
    omega

noncomputable def finalScale (d : ℕ) (ε : ℝ) : ℝ :=
  stageScale d ε (stoppingBound d ε)

theorem finalScale_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < finalScale d ε :=
  stageScale_pos d hε _

theorem finalScale_le {d i : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hi : i ≤ stoppingBound d ε) : finalScale d ε ≤ stageScale d ε i :=
  stageScale_antitone hd hε hi

end EGZ.FlagDecomposition.Iteration
