/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Foundation

/-!
The proof-side convex smooth optimization instance and its condition number.
-/

@[expose] public section

namespace V7

/-- The oracle's gradient is the coordinate gradient of its value function. -/
def IsCoordinateGradient (oracle : PairOracle d) : Prop :=
  O3.IsCoordinateGradient oracle.value oracle.gradient

/-- The set of global minimizers of the oracle's value function. -/
def MinimizerSet (oracle : PairOracle d) : Set (Point d) :=
  O3.MinimizerSet oracle.value

/-- The `ℓp` distance from the initial point to the objective's minimizer set. -/
noncomputable def minimizerDistance (p : ℝ) (oracle : PairOracle d)
    (x0 : Point d) : ℝ :=
  O3.minimizerDistance p oracle.value x0

/-- The oracle gradient is `L`-Lipschitz from the primal norm to its dual norm. -/
def IsLpSmooth (p L : ℝ) (oracle : PairOracle d) : Prop :=
  O3.IsLpSmooth p (conjugateExponent p) L oracle.gradient

/-- Proof-side objective certificate.  It is never an algorithm input. -/
structure PositiveInstance (p : ℝ) (d : ℕ) (x0 : Point d) where
  /-- The value-gradient oracle of the certified optimization instance. -/
  oracle : PairOracle d
  /-- A positive global Lipschitz constant for the gradient. -/
  L : ℝ
  L_pos : 0 < L
  coordinateGradient : IsCoordinateGradient oracle
  convex : O3.IsConvexObjective oracle.value
  minimizerNonempty : (MinimizerSet oracle).Nonempty
  smooth : IsLpSmooth p L oracle

/-- The initial distance to the minimizer set. -/
noncomputable def PositiveInstance.R (inst : PositiveInstance p d x0) : ℝ :=
  minimizerDistance p inst.oracle x0

/-- The common minimum value, expressed as an infimum over minimizers. -/
noncomputable def PositiveInstance.fstar (inst : PositiveInstance p d x0) : ℝ :=
  sInf (inst.oracle.value '' MinimizerSet inst.oracle)

/-- The gradient-accuracy condition number `L * R / eps`. -/
noncomputable def conditionNumber (inst : PositiveInstance p d x0) (eps : ℝ) : ℝ :=
  inst.L * inst.R / eps

/-- The condition number truncated below at one. -/
noncomputable def conditionBar (inst : PositiveInstance p d x0) (eps : ℝ) : ℝ :=
  max 1 (conditionNumber inst eps)

/-- Exact model split: the secant relation is proof-side evidence about the
primitive input, not an extra field of the method family. -/
def PositiveStandingAssumptions (input : MethodInput d)
    (inst : PositiveInstance input.p d input.x0) : Prop :=
  1 < input.p ∧ 0 < input.eps ∧ SecantInitialization input inst.oracle

end V7
