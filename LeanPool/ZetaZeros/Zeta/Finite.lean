/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import LeanPool.ZetaZeros.Zeta.Defs

/-!
# Finiteness of the zero set up to a height

The non-trivial zeros with imaginary part in `(0, T]` form a finite set, and each has positive
multiplicity. This is what lets the rescaled zeros be a finite multiset, which every statement of
the key proposition requires.

It is discharged from Mathlib's `IsCompact.inter_riemannZetaZeros_finite`, since the region is
bounded.
-/

@[expose] public section

namespace ZetaZeros

/-- The non-trivial zeros up to height `T` lie in a ball of radius `1 + |T|`. -/
private lemma nontrivialZeros_subset_closedBall (T : ℝ) :
    nontrivialZeros T ⊆ Metric.closedBall (0 : ℂ) (1 + |T|) := by
  intro ρ hρ
  obtain ⟨-, h1, h2, h3, h4⟩ := hρ
  have hre : |ρ.re| ≤ 1 := by rw [abs_of_pos h1]; linarith
  have him : |ρ.im| ≤ |T| := by
    rw [abs_of_pos h3]; exact le_trans h4 (le_abs_self T)
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    _ ≤ 1 + |T| := by linarith

/-- **The zero set up to a height is finite.** -/
@[zz_tag "lem_zeros_finite"]
theorem nontrivialZeros_finite (T : ℝ) : (nontrivialZeros T).Finite := by
  have hfin := (isCompact_closedBall (0 : ℂ) (1 + |T|)).inter_riemannZetaZeros_finite
  refine hfin.subset fun ρ hρ => ⟨nontrivialZeros_subset_closedBall T hρ, ?_⟩
  exact mem_riemannZetaZeros.mpr hρ.1

end ZetaZeros
