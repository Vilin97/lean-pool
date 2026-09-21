/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Shared
import LeanPool.ParameterFreeGradient.O3.Stage3Descent

/-!
Compatibility and soundness of the current observable guards and the original analytic
inequalities.
-/

namespace V7

theorem upperModelGuard_of_scale_ge {p L M : ℝ} (hp : 1 < p)
    (inst : PositiveInstance p d x0) (hLM : L ≤ M) (hL : inst.L = L)
    (x y : Point d) : UpperModelGuard p M inst.oracle x y := by
  subst L
  have hdes := O3.Stage3Anchor.smooth_descent_lp hp
    (O3.holderConjugate_conjugateExponent hp)
    inst.coordinateGradient inst.smooth x y
  have hsq : 0 ≤ (lpNorm p (y - x)) ^ (2 : ℕ) := sq_nonneg _
  dsimp only [UpperModelGuard]
  nlinarith

theorem failed_upperModelGuard_lt_trueScale {p L M : ℝ} (hp : 1 < p)
    (inst : PositiveInstance p d x0) (hL : inst.L = L)
    (x y : Point d) (hfail : ¬ UpperModelGuard p M inst.oracle x y) :
    M < L := by
  by_contra hnot
  exact hfail (upperModelGuard_of_scale_ge hp inst (le_of_not_gt hnot) hL x y)

theorem gradientGuard_of_scale_ge {p L M : ℝ}
    (inst : PositiveInstance p d x0) (hLM : L ≤ M) (hL : inst.L = L)
    (x y : Point d) : GradientGuard p M inst.oracle x y := by
  subst L
  have hs := inst.smooth y x
  have hn := O3.lpNorm_nonneg p (y - x)
  dsimp only [GradientGuard]
  have hsym : lpNorm (conjugateExponent p)
      (inst.oracle.gradient y - inst.oracle.gradient x) ≤
      inst.L * lpNorm p (y - x) := hs
  nlinarith

theorem failed_gradientGuard_lt_trueScale {p L M : ℝ}
    (inst : PositiveInstance p d x0) (hL : inst.L = L)
    (x y : Point d) (hfail : ¬ GradientGuard p M inst.oracle x y) :
    M < L := by
  by_contra hnot
  exact hfail (gradientGuard_of_scale_ge inst (le_of_not_gt hnot) hL x y)

theorem upperModelGuard_iff_historical (p M : ℝ) (oracle : PairOracle d)
    (x y : Point d) :
    UpperModelGuard p M oracle x y ↔
      (O3.upperModelGuard (oracle.value x) (oracle.value y)
        (pairing (oracle.gradient x) (y - x))
        ((lpNorm p (y - x)) ^ (2 : ℕ)) M).Holds := by
  rw [O3.upperModelGuard_holds_iff]
  rfl

theorem euclideanInterpolationGuard_iff_historical (M : ℝ)
    (oracle : PairOracle d) (x y : Point d) :
    EuclideanInterpolationGuard M oracle x y ↔
      (O3.interpolationGuard (oracle.value x) (oracle.value y)
        (pairing (oracle.gradient y) (x - y))
        ((lpNorm 2 (oracle.gradient x - oracle.gradient y)) ^ (2 : ℕ)) M).Holds := by
  rfl

end V7
