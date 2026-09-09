/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianElliptic
import LeanPool.NavierStokesAndEuler.Euler.LogarithmicCutoffOptimization

/-! The actual whole-space logarithmic derivative estimate for a scalar
elliptic equation whose right-hand side is the derivative of bounded fields. -/

@[expose] public section


noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerVectorCalculus Laplacian
open scoped ContDiff ENNReal RealInnerProductSpace Topology

/-- Split cost, given by `lowCost+middleCost+3`. -/
def splitCost : ℝ := lowCost+middleCost+3

theorem splitCost_nonneg : 0 ≤ splitCost := by
  unfold splitCost
  linarith [lowCost_nonneg, middleCost_nonneg]

theorem splitCost_pos : 0 < splitCost := by
  unfold splitCost
  linarith [lowCost_nonneg, middleCost_nonneg]

/-- The bound is proved for the genuine derivative of A.  H only bounds
its actual third L² derivative tensor; the elliptic equation is literal. -/
theorem elliptic_derivative_logarithmic (A G J : SmoothL2Field ℝ) (a b j : Fin 3)
    (hΔ : ∀ y, Δ A.field y = partialDerivative G.field a y - partialDerivative J.field b y)
    (W : ℝ) (hG : ∀ y, ‖G.field y‖ ≤ W) (hJ : ∀ y, ‖J.field y‖ ≤ W)
    (H : ℝ) (hH : ‖A.jetLp 3‖ ≤ H) (x : Space) :
    ‖partialDerivative A.field j x‖ ≤
      4*splitCost*(1+‖A.toLp‖+W*Real.log (Real.exp 1+H)) := by
  have hH0 : 0 ≤ H := (norm_nonneg (A.jetLp 3)).trans hH
  have hW : 0 ≤ W := (norm_nonneg (G.field x)).trans (hG x)
  apply EulerLogarithmicCutoff.optimize _ splitCost ‖A.toLp‖ W H
    splitCost_nonneg (norm_nonneg _) hH0
  intro ε hε hε1
  have he : 0 ≤ -Real.log ε := neg_nonneg.mpr (Real.log_nonpos hε.le hε1.le)
  have hr : 0 ≤ ε^((1:ℝ)/4) := Real.rpow_nonneg hε.le _
  have hl : lowCost ≤ splitCost := by unfold splitCost; linarith [middleCost_nonneg]
  have hm : middleCost ≤ splitCost := by unfold splitCost; linarith [lowCost_nonneg]
  have hh : (3:ℝ) ≤ splitCost := by unfold splitCost; linarith [lowCost_nonneg, middleCost_nonneg]
  calc
    _ ≤ lowCost*‖A.toLp‖+middleCost*W*(-Real.log ε)+3*ε^((1:ℝ)/4)*‖A.jetLp 3‖ :=
      elliptic_derivative_split A G J a b j hΔ W hG hJ x hε hε1.le
    _ = lowCost*‖A.toLp‖+middleCost*(W*(-Real.log ε))+3*(ε^((1:ℝ)/4)*‖A.jetLp 3‖) := by ring
    _ ≤ splitCost*‖A.toLp‖+splitCost*(W*(-Real.log ε))+splitCost*(ε^((1:ℝ)/4)*H) := by
      apply add_le_add
      · exact add_le_add (mul_le_mul_of_nonneg_right hl (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hm (mul_nonneg hW he))
      · exact mul_le_mul hh (mul_le_mul_of_nonneg_left hH hr)
          (mul_nonneg hr (norm_nonneg _)) splitCost_nonneg
    _ = _ := by ring

end EulerWholeSpaceGaussian
