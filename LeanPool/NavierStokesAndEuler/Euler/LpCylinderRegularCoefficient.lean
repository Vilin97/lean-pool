/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod

/-! A genuinely smooth translated bounded-field family lifts to actual mixed cylinder coefficients.
-/

@[expose] public section


noncomputable section

namespace EulerLpCylinderCoefficients

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderPaths
  EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ)
  (B : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))

/-- Cache the standard `NormedAddCommGroup (V →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient1 : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
/-- Cache the standard `NormedSpace ℝ (V →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient2 : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ V →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularCoefficient3 : NormedAddCommGroup (Space →ᵇ V →L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ V →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularCoefficient4 : NormedSpace ℝ (Space →ᵇ V →L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient5 : NormedAddCommGroup C(Icc (0 : ℝ) T,Space →ᵇ V
    →L[ℝ] V) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient6 : NormedSpace ℝ C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ]
    V) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Supported period V S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient7 : NormedAddCommGroup (Supported period V S hS) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported period V S hS)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularCoefficient8 : NormedSpace ℝ (Supported period V S hS) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Supported period V S hS →L[ℝ] Supported period V S
hS)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient9 : NormedAddCommGroup (Supported period V S hS
    →L[ℝ] Supported period V S hS)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported period V S hS →L[ℝ] Supported period V S hS)`
instance to shorten typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient10 : NormedSpace ℝ (Supported period V S hS →L[ℝ]
    Supported period V S hS) :=
    inferInstance

include hB in
/-- This requires only actual translated coefficient regularity, so applies to the constructed Gram
generator. -/
theorem mixedCoefficient_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => liftedOperatorPath period S hS T (translateCoefficientPath
        B a.1)) :=
  (hB.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff).continuousLinearMap_comp
    (liftedOperatorPathMap (V := V) period S hS T)

include hB in
/-- All actual mixed coefficient derivatives retain the real bounded-field derivative bound. -/
theorem mixedCoefficient_bound (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => liftedOperatorPath period S hS T
      (translateCoefficientPath B b.1)) a‖ ≤ C := by
  let f := translateCoefficientPath B
  have hright : ‖iteratedFDeriv ℝ n (f ∘ ContinuousLinearMap.fst ℝ Space ℝ) a‖ ≤ C := by
    rw [(ContinuousLinearMap.fst ℝ Space ℝ).iteratedFDeriv_comp_right hB a (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    exact (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ Space ℝ))).trans
        (hb (ContinuousLinearMap.fst ℝ Space ℝ a))
  have hleft := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (liftedOperatorPathMap (V := V) period S hS T)
    ((hB.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff).contDiffAt (x := a)) (n := n) (by simp)
  exact hleft.trans ((mul_le_of_le_one_left (norm_nonneg _)
    (liftedOperatorPathMap_norm period S hS T)).trans hright)

end EulerLpCylinderCoefficients
