/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Foundation

namespace V7

def IsCoordinateGradient (oracle : PairOracle d) : Prop :=
  O3.IsCoordinateGradient oracle.value oracle.gradient

def MinimizerSet (oracle : PairOracle d) : Set (Point d) :=
  O3.MinimizerSet oracle.value

noncomputable def minimizerDistance (p : ℝ) (oracle : PairOracle d)
    (x0 : Point d) : ℝ :=
  O3.minimizerDistance p oracle.value x0

def IsLpSmooth (p L : ℝ) (oracle : PairOracle d) : Prop :=
  O3.IsLpSmooth p (conjugateExponent p) L oracle.gradient

/-- Proof-side objective certificate.  It is never an algorithm input. -/
structure PositiveInstance (p : ℝ) (d : ℕ) (x0 : Point d) where
  oracle : PairOracle d
  L : ℝ
  L_pos : 0 < L
  coordinateGradient : IsCoordinateGradient oracle
  convex : O3.IsConvexObjective oracle.value
  minimizerNonempty : (MinimizerSet oracle).Nonempty
  smooth : IsLpSmooth p L oracle

noncomputable def PositiveInstance.R (inst : PositiveInstance p d x0) : ℝ :=
  minimizerDistance p inst.oracle x0

noncomputable def PositiveInstance.fstar (inst : PositiveInstance p d x0) : ℝ :=
  sInf (inst.oracle.value '' MinimizerSet inst.oracle)

noncomputable def conditionNumber (inst : PositiveInstance p d x0) (eps : ℝ) : ℝ :=
  inst.L * inst.R / eps

noncomputable def conditionBar (inst : PositiveInstance p d x0) (eps : ℝ) : ℝ :=
  max 1 (conditionNumber inst eps)

/-- Exact model split: the secant relation is proof-side evidence about the
primitive input, not an extra field of the method family. -/
def PositiveStandingAssumptions (input : MethodInput d)
    (inst : PositiveInstance input.p d input.x0) : Prop :=
  1 < input.p ∧ 0 < input.eps ∧ SecantInitialization input inst.oracle

end V7
