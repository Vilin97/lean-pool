/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.PositiveModel

namespace V7

noncomputable def BregmanRemainder (oracle : PairOracle d)
    (x y : Point d) : ℝ :=
  oracle.value x - oracle.value y - pairing (oracle.gradient y) (x - y)

noncomputable def UpperModelGuard (p M : ℝ) (oracle : PairOracle d)
    (x y : Point d) : Prop :=
  oracle.value y ≤ oracle.value x + pairing (oracle.gradient x) (y - x) +
    (M / 2) * (lpNorm p (y - x)) ^ (2 : ℕ)

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

noncomputable def EuclideanInterpolationGuard (M : ℝ) (oracle : PairOracle d)
    (xi xj : Point d) : Prop :=
  oracle.value xi - oracle.value xj - pairing (oracle.gradient xj) (xi - xj) -
    (lpNorm 2 (oracle.gradient xi - oracle.gradient xj)) ^ (2 : ℕ) / (2 * M) ≥ 0

noncomputable def TerminalDescentGuard (M : ℝ) (oracle : PairOracle d)
    (u v : Point d) : Prop :=
  oracle.value v ≤ oracle.value u -
    (lpNorm 2 (oracle.gradient u)) ^ (2 : ℕ) / (2 * M)

inductive ObservableGuardKind where
  | upperModel | gradient | cocoercivity | interpolation | terminalDescent
  deriving DecidableEq

structure ObservableGuardFailure (d : ℕ) where
  kind : ObservableGuardKind
  x : Point d
  y : Point d

noncomputable def GuardFails (p M : ℝ) (oracle : PairOracle d)
    (w : ObservableGuardFailure d) : Prop :=
  match w.kind with
  | .upperModel => ¬ UpperModelGuard p M oracle w.x w.y
  | .gradient => ¬ GradientGuard p M oracle w.x w.y
  | .cocoercivity => ¬ CocoercivityGuard p M oracle w.x w.y
  | .interpolation => ¬ EuclideanInterpolationGuard M oracle w.x w.y
  | .terminalDescent => ¬ TerminalDescentGuard M oracle w.x w.y

end V7
