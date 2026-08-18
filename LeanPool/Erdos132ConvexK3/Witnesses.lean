/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact rational regression witnesses

Kernel-reduced checks for the three configurations used during the convex
`k = 3` campaign.  These are regression fixtures, not proof dependencies for
the eventual global degree theorem.
-/

namespace LeanPool.Erdos132ConvexK3.Witnesses

open LeanPool.Erdos132ConvexK3

/-- Attempt 2's exact integer heptagon, in positive cyclic order. -/
def heptagon : Fin 7 → Point ℚ :=
  ![(0, 0), (72, 0), (45, 68), (40, 75), (36, 77), (32, 75), (27, 68)]

theorem heptagon_strict_convex : CyclicStrictConvex heptagon := by
  intro i j hji hjnext
  fin_cases i <;> fin_cases j
  all_goals norm_num [cyclicNext, Fin.add_def, heptagon, turn] at *

theorem heptagon_top_three :
    HasTopThreeDistanceClasses heptagon 7225 6649 5353 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · refine ⟨(0, 3), by decide, ?_⟩
    change ((40 : ℚ) - 0) ^ 2 + (75 - 0) ^ 2 = 7225
    norm_num
  · refine ⟨(0, 2), by decide, ?_⟩
    change ((45 : ℚ) - 0) ^ 2 + (68 - 0) ^ 2 = 6649
    norm_num
  · refine ⟨(0, 6), by decide, ?_⟩
    change ((27 : ℚ) - 0) ^ 2 + (68 - 0) ^ 2 = 5353
    norm_num
  · rintro ⟨i, j⟩ hij
    fin_cases i <;> fin_cases j
    all_goals norm_num [unorderedPairList, heptagon, sqDist] at *

theorem heptagon_double_ladder :
    sqDist (heptagon 0) (heptagon 6) = 5353 ∧
    sqDist (heptagon 0) (heptagon 5) = 6649 ∧
    sqDist (heptagon 0) (heptagon 4) = 7225 ∧
    sqDist (heptagon 1) (heptagon 2) = 5353 ∧
    sqDist (heptagon 1) (heptagon 3) = 6649 ∧
    sqDist (heptagon 1) (heptagon 4) = 7225 := by
  change
    ((27 : ℚ) - 0) ^ 2 + (68 - 0) ^ 2 = 5353 ∧
    ((32 : ℚ) - 0) ^ 2 + (75 - 0) ^ 2 = 6649 ∧
    ((36 : ℚ) - 0) ^ 2 + (77 - 0) ^ 2 = 7225 ∧
    ((45 : ℚ) - 72) ^ 2 + (68 - 0) ^ 2 = 5353 ∧
    ((40 : ℚ) - 72) ^ 2 + (75 - 0) ^ 2 = 6649 ∧
    ((36 : ℚ) - 72) ^ 2 + (77 - 0) ^ 2 = 7225
  norm_num

theorem heptagon_x_degree : vertexDegree heptagon 7225 6649 5353 0 = 5 := by
  calc
    vertexDegree heptagon 7225 6649 5353 0 =
        ({2, 3, 4, 5, 6} : Finset (Fin 7)).card := by
      apply vertexDegree_eq_of_neighbors
      intro j
      fin_cases j <;> norm_num [heptagon, sqDist] <;> decide
    _ = 5 := by decide

/-- Attempt 3's exact nine-point low-altitude insertion witness. -/
def ninePoint : Fin 9 → Point ℚ :=
  ![(0, 0), (180, -1), (370, -1), (570, 0), (309, 862),
    (300, 875), (285, 880), (270, 875), (261, 862)]

theorem ninePoint_strict_convex : CyclicStrictConvex ninePoint := by
  intro i j hji hjnext
  fin_cases i <;> fin_cases j
  all_goals norm_num [cyclicNext, Fin.add_def, ninePoint, turn] at *

theorem ninePoint_top_three :
    HasTopThreeDistanceClasses ninePoint 855625 838525 811165 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · refine ⟨(0, 6), by decide, ?_⟩
    change ((285 : ℚ) - 0) ^ 2 + (880 - 0) ^ 2 = 855625
    norm_num
  · refine ⟨(0, 7), by decide, ?_⟩
    change ((270 : ℚ) - 0) ^ 2 + (875 - 0) ^ 2 = 838525
    norm_num
  · refine ⟨(0, 8), by decide, ?_⟩
    change ((261 : ℚ) - 0) ^ 2 + (862 - 0) ^ 2 = 811165
    norm_num
  · rintro ⟨i, j⟩ hij
    fin_cases i <;> fin_cases j
    all_goals norm_num [unorderedPairList, ninePoint, sqDist] at *

theorem ninePoint_insertions_isolated :
    vertexDegree ninePoint 855625 838525 811165 1 = 0 ∧
      vertexDegree ninePoint 855625 838525 811165 2 = 0 := by
  constructor
  · calc
      vertexDegree ninePoint 855625 838525 811165 1 =
          (∅ : Finset (Fin 9)).card := by
        apply vertexDegree_eq_of_neighbors
        intro j
        fin_cases j <;> simp [ninePoint, sqDist] <;> norm_num
      _ = 0 := rfl
  · calc
      vertexDegree ninePoint 855625 838525 811165 2 =
          (∅ : Finset (Fin 9)).card := by
        apply vertexDegree_eq_of_neighbors
        intro j
        fin_cases j <;> simp [ninePoint, sqDist] <;> norm_num
      _ = 0 := rfl

/-- A second exact rational hexagon, in positive cyclic order. -/
def rationalHexagon : Fin 6 → Point ℚ :=
  ![(0, -20),
    (24171 / 50380, -(12571661 / 629750)),
    (48331 / 50380, -(12546661 / 629750)),
    (1208 / 229, -(4480 / 229)),
    (1, 0),
    (-1, 0)]

theorem rationalHexagon_strict_convex : CyclicStrictConvex rationalHexagon := by
  intro i j hji hjnext
  fin_cases i <;> fin_cases j
  all_goals norm_num [cyclicNext, Fin.add_def, rationalHexagon, turn] at *

theorem rationalHexagon_top_three :
    HasTopThreeDistanceClasses rationalHexagon
      (96661 / 229) 401 (2776265163521 / 6927250000) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · refine ⟨(3, 5), by decide, ?_⟩
    change ((-1 : ℚ) - 1208 / 229) ^ 2 + (0 - (-(4480 / 229))) ^ 2 = 96661 / 229
    norm_num
  · refine ⟨(0, 5), by decide, ?_⟩
    change ((-1 : ℚ) - 0) ^ 2 + (0 - (-20)) ^ 2 = 401
    norm_num
  · refine ⟨(2, 5), by decide, ?_⟩
    change ((-1 : ℚ) - 48331 / 50380) ^ 2 +
      (0 - (-(12546661 / 629750))) ^ 2 = 2776265163521 / 6927250000
    norm_num
  · rintro ⟨i, j⟩ hij
    fin_cases i <;> fin_cases j
    all_goals norm_num [unorderedPairList, rationalHexagon, sqDist] at *

theorem rationalHexagon_key_edges :
    sqDist (rationalHexagon 3) (rationalHexagon 5) = 96661 / 229 ∧
    sqDist (rationalHexagon 0) (rationalHexagon 5) = 401 ∧
    sqDist (rationalHexagon 3) (rationalHexagon 4) = 401 ∧
    sqDist (rationalHexagon 0) (rationalHexagon 4) = 401 ∧
    sqDist (rationalHexagon 2) (rationalHexagon 5) =
      2776265163521 / 6927250000 := by
  change
    ((-1 : ℚ) - 1208 / 229) ^ 2 + (0 - (-(4480 / 229))) ^ 2 = 96661 / 229 ∧
    ((-1 : ℚ) - 0) ^ 2 + (0 - (-20)) ^ 2 = 401 ∧
    ((1 : ℚ) - 1208 / 229) ^ 2 + (0 - (-(4480 / 229))) ^ 2 = 401 ∧
    ((1 : ℚ) - 0) ^ 2 + (0 - (-20)) ^ 2 = 401 ∧
    ((-1 : ℚ) - 48331 / 50380) ^ 2 +
      (0 - (-(12546661 / 629750))) ^ 2 = 2776265163521 / 6927250000
  norm_num

theorem rationalHexagon_lower_degrees :
    vertexDegree rationalHexagon
        (96661 / 229) 401 (2776265163521 / 6927250000) 1 = 0 ∧
      vertexDegree rationalHexagon
        (96661 / 229) 401 (2776265163521 / 6927250000) 2 = 1 := by
  constructor
  · calc
      vertexDegree rationalHexagon
          (96661 / 229) 401 (2776265163521 / 6927250000) 1 =
          (∅ : Finset (Fin 6)).card := by
        apply vertexDegree_eq_of_neighbors
        intro j
        fin_cases j <;> simp [rationalHexagon, sqDist] <;> norm_num
      _ = 0 := rfl
  · calc
      vertexDegree rationalHexagon
          (96661 / 229) 401 (2776265163521 / 6927250000) 2 =
          ({5} : Finset (Fin 6)).card := by
        apply vertexDegree_eq_of_neighbors
        intro j
        fin_cases j <;> simp [rationalHexagon, sqDist] <;> norm_num
      _ = 1 := by decide

end LeanPool.Erdos132ConvexK3.Witnesses
