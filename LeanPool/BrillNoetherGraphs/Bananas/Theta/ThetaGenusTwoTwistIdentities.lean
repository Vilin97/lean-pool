/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaInversionFiniteSum

/-!
# Degree-twist deletion identities

The inclusion--exclusion proof of Lemma 4.10 repeatedly removes one or both
marked chips from a fixed-degree twist.  These elementary identities make the
resulting shifts of the finite torsion index explicit.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Removing the first marked chip lowers the degree-twist index by one. -/
theorem degreeTwistInt_sub_u
    (M : TwiceMarked) (D : CFDiv M.graph) (d b : ℤ) :
    degreeTwistInt M D d b - oneChip M.u =
      degreeTwistInt M D (d - 1) b := by
  unfold degreeTwistInt
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- Removing the second marked chip lowers degree and advances the torsion
index by one. -/
theorem degreeTwistInt_sub_v
    (M : TwiceMarked) (D : CFDiv M.graph) (d b : ℤ) :
    degreeTwistInt M D d b - oneChip M.v =
      degreeTwistInt M D (d - 1) (b + 1) := by
  unfold degreeTwistInt
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- Removing both marked chips lowers degree by two and advances the torsion
index once. -/
theorem degreeTwistInt_sub_uv
    (M : TwiceMarked) (D : CFDiv M.graph) (d b : ℤ) :
    degreeTwistInt M D d b - oneChip M.u - oneChip M.v =
      degreeTwistInt M D (d - 2) (b + 1) := by
  rw [degreeTwistInt_sub_u, degreeTwistInt_sub_v]
  congr 1
  ring

/-- The degree-one twists are exactly the first-mark additions of degree-zero
twists at the same finite orbit index. -/
theorem degreeTwistInt_one_eq_zero_add_u
    (M : TwiceMarked) (D : CFDiv M.graph) (b : ℤ) :
    degreeTwistInt M D 1 b =
      degreeTwistInt M D 0 b + oneChip M.u := by
  unfold degreeTwistInt
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

end Bananas
