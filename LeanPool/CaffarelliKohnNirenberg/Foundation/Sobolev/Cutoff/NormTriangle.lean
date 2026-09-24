/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Norm Triangle

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

namespace CKN

/-- The Euclidean norm on native coordinate vectors coincides with the `L²`
norm of `WithLp.toLp 2 x`. -/
theorem vecEuclideanNorm_eq_norm_toLp {d : ℕ} (x : Vec d) :
    vecEuclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [vecEuclideanNorm, vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The triangle inequality for the Euclidean norm on native coordinate vectors. -/
theorem vecEuclideanNorm_add_le {d : ℕ} (x y : Vec d) :
    vecEuclideanNorm (x + y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  rw [vecEuclideanNorm_eq_norm_toLp, vecEuclideanNorm_eq_norm_toLp, vecEuclideanNorm_eq_norm_toLp]
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

end CKN
