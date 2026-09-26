/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Smooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Translation and dilation bookkeeping

Adapted from CoarseGraining (LeanIntoHomogenization, 2026) with the author's
permission.  The statements here isolate the affine change of variables used
to pass from the unit ball to a general ball.  The weak-derivative result is
proved for the smooth pullback; a density theorem for the full representative
level is still a separate input.
-/

public section

namespace CKN

/-- Pull back a scalar function by the affine map from the unit ball. -/
@[expose] def ballPullback {d : ℕ} (x₀ : Vec d) (r : ℝ) (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => u (ballAffineMap x₀ r x)

theorem ballPullback_contDiff {d : ℕ} (x₀ : Vec d) (r : ℝ)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 (ballPullback x₀ r u) := by
  apply hu.comp
  change ContDiff ℝ 1 (fun x : Vec d => x₀ + r • x)
  exact contDiff_const.add (contDiff_id.const_smul r)

end CKN
