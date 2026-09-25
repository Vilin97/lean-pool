/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.PositiveModel

/-!
Observable upper-model, gradient, cocoercivity, interpolation, and descent inequalities.
-/

@[expose] public section

namespace V7

/-- The objective's linearization error at `x`, based at `y`. -/
noncomputable def BregmanRemainder (oracle : PairOracle d)
    (x y : Point d) : ℝ :=
  oracle.value x - oracle.value y - pairing (oracle.gradient y) (x - y)

/-- The quadratic upper model with estimate `M` bounds the objective at `y`. -/
noncomputable def UpperModelGuard (p M : ℝ) (oracle : PairOracle d)
    (x y : Point d) : Prop :=
  oracle.value y ≤ oracle.value x + pairing (oracle.gradient x) (y - x) +
    (M / 2) * (lpNorm p (y - x)) ^ (2 : ℕ)

/-- The two observed gradients satisfy the proposed Lipschitz bound in the dual norm. -/
noncomputable def GradientGuard (p M : ℝ) (oracle : PairOracle d)
    (x y : Point d) : Prop :=
  lpNorm (conjugateExponent p) (oracle.gradient y - oracle.gradient x) ≤
    M * lpNorm p (y - x)

/-- Exact current orientation: `D_f(x,y)` uses the gradient at `y`. -/
noncomputable def CocoercivityGuard (p M : ℝ) (oracle : PairOracle d)
    (x y : Point d) : Prop :=
  BregmanRemainder oracle x y ≥
    (lpNorm (conjugateExponent p) (oracle.gradient x - oracle.gradient y)) ^
      (2 : ℕ) / (2 * M)

/-- The observed Euclidean Bregman gap dominates the squared gradient difference. -/
noncomputable def EuclideanInterpolationGuard (M : ℝ) (oracle : PairOracle d)
    (xi xj : Point d) : Prop :=
  oracle.value xi - oracle.value xj - pairing (oracle.gradient xj) (xi - xj) -
    (lpNorm 2 (oracle.gradient xi - oracle.gradient xj)) ^ (2 : ℕ) / (2 * M) ≥ 0

/-- The terminal gradient step achieves the decrease predicted by the smoothness estimate. -/
noncomputable def TerminalDescentGuard (M : ℝ) (oracle : PairOracle d)
    (u v : Point d) : Prop :=
  oracle.value v ≤ oracle.value u -
    (lpNorm 2 (oracle.gradient u)) ^ (2 : ℕ) / (2 * M)

/-- The observable inequalities that a local trial may check. -/
inductive ObservableGuardKind where
  | upperModel | gradient | cocoercivity | interpolation | terminalDescent
  deriving DecidableEq

/-- The kind and pair of points witnessing a failed observable guard. -/
structure ObservableGuardFailure (d : ℕ) where
  /-- The inequality that failed. -/
  kind : ObservableGuardKind
  /-- The first point of the failed guard. -/
  x : Point d
  /-- The second point of the failed guard. -/
  y : Point d

/-- The selected observable inequality fails for the supplied oracle and estimates. -/
noncomputable def GuardFails (p M : ℝ) (oracle : PairOracle d)
    (w : ObservableGuardFailure d) : Prop :=
  match w.kind with
  | .upperModel => ¬ UpperModelGuard p M oracle w.x w.y
  | .gradient => ¬ GradientGuard p M oracle w.x w.y
  | .cocoercivity => ¬ CocoercivityGuard p M oracle w.x w.y
  | .interpolation => ¬ EuclideanInterpolationGuard M oracle w.x w.y
  | .terminalDescent => ¬ TerminalDescentGuard M oracle w.x w.y

end V7
