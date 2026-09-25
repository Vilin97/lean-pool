/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RiemannRochWinnable

/-!
# Degree bookkeeping for twice-marked twists

Transmission inequalities repeatedly use divisors of the form
`D + a • oneChip u - b • oneChip v`.  This module isolates the elementary
degree identities so later formalizations do not repeatedly unfold `deg` and
fight integer casts.
-/

namespace Utilities

/-- The marked difference `u-v` has degree zero. -/
theorem deg_seam_difference
    {G : CFGraph} (u v : G.V) :
    deg (oneChip u - oneChip v) = 0 := by
  rw [deg.map_sub, deg_one_chip, deg_one_chip]
  norm_num

/-- Integral multiples of a marked difference preserve degree. -/
theorem deg_zsmul_seam_difference
    {G : CFGraph} (u v : G.V) (n : ℤ) :
    deg (n • (oneChip u - oneChip v)) = 0 := by
  rw [map_zsmul, deg_seam_difference]
  simp

/-- Exact degree of a two-marked twist. -/
theorem deg_add_marked_twist
    {G : CFGraph} (D : CFDiv G) (u v : G.V) (a b : ℤ) :
    deg (D + a • oneChip u - b • oneChip v) = deg D + a - b := by
  rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
    deg_one_chip, deg_one_chip]
  simp

/-- Translating by the seam direction does not change degree. -/
theorem deg_add_zsmul_seam
    {G : CFGraph} (D : CFDiv G) (u v : G.V) (n : ℤ) :
    deg (D + n • (oneChip u - oneChip v)) = deg D := by
  rw [deg.map_add, map_zsmul, deg_seam_difference]
  simp

/-- The transmission convention `D + a u - b v` has the expected affine
change in degree.  This variant is useful when the base degree is known. -/
theorem deg_add_marked_twist_of_degree
    {G : CFGraph} (D : CFDiv G) (u v : G.V) (a b d : ℤ)
    (hDegree : deg D = d) :
    deg (D + a • oneChip u - b • oneChip v) = d + a - b := by
  rw [deg_add_marked_twist, hDegree]

end Utilities
