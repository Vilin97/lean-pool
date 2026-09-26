/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms


/-!
# Lattice seminorms

A seminorm monotone with respect to absolute value, together with its solid balls.
Extracted from BanLat `LocallySolid/WithSeminorms.lean` at
`b00e59836016aa1099b8011add6b07385e66428e`.
-/

@[expose] public section

open scoped Topology Pointwise

universe u v

/-- A lattice seminorm on a vector lattice is a seminorm that is monotone with respect to the
lattice absolute value. -/
structure LatticeSeminorm (E : Type u) [AddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [VectorLattice E] extends Seminorm ℝ E where
  /-- Monotonicity with respect to the lattice absolute value. -/
  monotone_abs' : ∀ {x y : E}, |x| ≤ |y| → toSeminorm x ≤ toSeminorm y

namespace LatticeSeminorm

variable {E : Type u} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]

/-- The underlying seminorm family of a lattice seminorm family. -/
abbrev toSeminormFamily {ι : Type v} (p : ι → LatticeSeminorm E) : SeminormFamily ℝ E ι :=
  fun i => (p i).toSeminorm

private lemma finset_sup_mono_abs {ι : Type v} (p : ι → LatticeSeminorm E) (I : Finset ι)
    {x y : E} (hxy : |x| ≤ |y|) :
    I.sup (toSeminormFamily p) x ≤ I.sup (toSeminormFamily p) y := by
  refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => ?_
  exact (p i).monotone_abs' hxy |>.trans
    (Seminorm.le_finset_sup_apply (p := toSeminormFamily p) (s := I) (x := y) hi)

/-- Every basis set of the seminorm family associated to a family of lattice seminorms is solid. -/
theorem isSolid_of_mem_basisSets {ι : Type v} (p : ι → LatticeSeminorm E) {s : Set E}
    (hs : s ∈ (toSeminormFamily p).basisSets) : LatticeOrderedAddCommGroup.IsSolid s := by
  rcases (SeminormFamily.basisSets_iff (p := toSeminormFamily p)).mp hs with ⟨I, r, hr, rfl⟩
  intro x hx y hy
  rw [Seminorm.mem_ball_zero] at hx ⊢
  exact (finset_sup_mono_abs p I hy).trans_lt hx

end LatticeSeminorm
