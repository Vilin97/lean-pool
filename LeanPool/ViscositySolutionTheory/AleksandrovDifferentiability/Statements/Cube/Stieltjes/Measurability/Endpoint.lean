/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Stieltjes.Measurability.Secant

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Endpoint measurability reductions for Stieltjes coordinate-slice measures

This file reduces Stieltjes endpoint values and endpoint left limits to countable rational and
secant approximations, then packages the concrete convex endpoint measurability facts.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

theorem coordinateSliceConvexSourceRightDerivStieltjesEndpointValue_eq_iInf_ratApprox
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    (i : Fin n) (c : ℝ) (y : SourceCubeSpace n) :
    coordinateSliceConvexSourceRightDerivStieltjesEndpointValue u hu i c y =
      ⨅ q : {q' : ℚ // c < (q' : ℝ)},
        coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox u hu i c q y := by
  classical
  by_cases hy : y ∈ sourceOpenCube n 1
  · let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
    let hmono := ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy
    let F := sourceRightDerivStieltjesSecondDerivativeFunction v hmono
    have hF : F c = ⨅ q : {q' : ℚ // c < (q' : ℝ)}, F q :=
      (StieltjesFunction.iInf_rat_gt_eq F c).symm
    simpa [coordinateSliceConvexSourceRightDerivStieltjesEndpointValue,
      coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox, hy, v, hmono, F]
      using hF
  · simp [coordinateSliceConvexSourceRightDerivStieltjesEndpointValue,
      coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox, hy]

/-- Measurability of all rational right-approximations gives measurability of the fixed
right-continuous Stieltjes endpoint value. -/
theorem stieltjesEndpointValueAtMeasurable_of_ratApprox
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {c : ℝ}
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApproxMeasurable
        u hu i c) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueAtMeasurable u hu i c := by
  have hiInf :
      Measurable fun y : SourceCubeSpace n =>
        ⨅ q : {q' : ℚ // c < (q' : ℝ)},
          coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox u hu i c q y :=
    Measurable.iInf happrox
  change Measurable fun y : SourceCubeSpace n =>
    coordinateSliceConvexSourceRightDerivStieltjesEndpointValue u hu i c y
  convert hiInf using 1
  ext y
  exact coordinateSliceConvexSourceRightDerivStieltjesEndpointValue_eq_iInf_ratApprox i c y

/-- A rational right-approximation of the Stieltjes endpoint value is the infimum of the
underlying clamped right-derivative extension at rational points to its right. -/
theorem coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox_eq_iInf_extension
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    (i : Fin n) (c : ℝ) (q : {q' : ℚ // c < (q' : ℝ)}) (y : SourceCubeSpace n) :
    coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox u hu i c q y =
      ⨅ r : {r' : ℚ // (q : ℝ) < (r' : ℝ)},
        coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox
          u hu i (q : ℝ) r y := by
  classical
  by_cases hy : y ∈ sourceOpenCube n 1
  · let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
    let hmono := ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy
    let g := sourceRightDerivExtension v
    have hg : Monotone g := monotone_sourceRightDerivExtension hmono
    have hright :
        Function.rightLim g (q : ℝ) =
          ⨅ r : {r' : ℚ // (q : ℝ) < (r' : ℝ)}, g (r : ℝ) :=
      monotone_rightLim_eq_iInf_rat_gt hg (q : ℝ)
    have hF :
        sourceRightDerivStieltjesSecondDerivativeFunction v hmono (q : ℝ) =
          Function.rightLim g (q : ℝ) := by
      simp [sourceRightDerivStieltjesSecondDerivativeFunction_apply, g]
    calc
      coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox u hu i c q y =
          sourceRightDerivStieltjesSecondDerivativeFunction v hmono (q : ℝ) := by
        simp [coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox, hy,
          v]
      _ = Function.rightLim g (q : ℝ) := hF
      _ = ⨅ r : {r' : ℚ // (q : ℝ) < (r' : ℝ)}, g (r : ℝ) := hright
      _ = ⨅ r : {r' : ℚ // (q : ℝ) < (r' : ℝ)},
            coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox
              u hu i (q : ℝ) r y := by
        simp [coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox,
          coordinateSliceConvexSourceRightDerivExtensionValue, hy, v, g]
  · simp [coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox,
      coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox,
      coordinateSliceConvexSourceRightDerivExtensionValue, hy]

/-- Measurability of the underlying extension approximations gives measurability of one rational
right-approximation of the Stieltjes endpoint value. -/
theorem stieltjesEndpointValueRatApproxMeasurable_of_extensionRatApprox
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {c : ℝ} {q : {q' : ℚ // c < (q' : ℝ)}}
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApproxMeasurable
        u hu i (q : ℝ)) :
    Measurable fun y : SourceCubeSpace n =>
      coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox u hu i c q y := by
  have hiInf :
      Measurable fun y : SourceCubeSpace n =>
        ⨅ r : {r' : ℚ // (q : ℝ) < (r' : ℝ)},
          coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox
            u hu i (q : ℝ) r y :=
    Measurable.iInf happrox
  convert hiInf using 1
  ext y
  exact coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox_eq_iInf_extension
    i c q y

/-- Fixed clamped-extension measurability gives measurability of all rational extension
approximations above one base point. -/
theorem stieltjesEvaluationExtensionRatApproxMeasurable_of_extensionValueAt
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {s : ℝ}
    (hvalue : ∀ r : {r' : ℚ // s < (r' : ℝ)},
      CoordinateSliceConvexSourceRightDerivExtensionValueAtMeasurable u hu i (r : ℝ)) :
    CoordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApproxMeasurable
      u hu i s := by
  intro r
  simpa [CoordinateSliceConvexSourceRightDerivExtensionValueAtMeasurable,
    coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox]
    using hvalue r

/-- Global fixed clamped-extension measurability gives measurability of all rational extension
approximations above one base point. -/
theorem stieltjesEvaluationExtensionRatApproxMeasurable_of_extensionValue
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {s : ℝ}
    (hvalue : CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable u hu) :
    CoordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApproxMeasurable
      u hu i s :=
  stieltjesEvaluationExtensionRatApproxMeasurable_of_extensionValueAt
    (fun r => hvalue i (r : ℝ))

/-- Global fixed clamped-extension measurability gives measurability of every rational
right-approximation of a Stieltjes endpoint value. -/
theorem stieltjesEndpointValueRatApproxMeasurable_of_extensionValue
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {c : ℝ} {q : {q' : ℚ // c < (q' : ℝ)}}
    (hvalue : CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable u hu) :
    Measurable fun y : SourceCubeSpace n =>
      coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox u hu i c q y :=
  stieltjesEndpointValueRatApproxMeasurable_of_extensionRatApprox
    (stieltjesEvaluationExtensionRatApproxMeasurable_of_extensionValue hvalue)

/-- The Stieltjes endpoint left limit is the supremum of its rational left-approximations. -/
theorem coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit_eq_iSup_ratApprox
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    (i : Fin n) (c : ℝ) (y : SourceCubeSpace n) :
    coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit u hu i c y =
      ⨆ q : {q' : ℚ // (q' : ℝ) < c},
        coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox
          u hu i c q y := by
  classical
  by_cases hy : y ∈ sourceOpenCube n 1
  · let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
    let hmono := ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy
    let F := sourceRightDerivStieltjesSecondDerivativeFunction v hmono
    have hF : Function.leftLim F c = ⨆ q : {q' : ℚ // (q' : ℝ) < c}, F q :=
      stieltjesFunction_leftLim_eq_iSup_rat_lt F c
    simpa [coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit,
      coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox, hy, v, hmono, F]
      using hF
  · simp [coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit,
      coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox, hy]

/-- Measurability of all rational left-approximations gives measurability of the fixed Stieltjes
endpoint left limit. -/
theorem stieltjesEndpointLeftLimitAtMeasurable_of_ratApprox
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {c : ℝ}
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApproxMeasurable
        u hu i c) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitAtMeasurable u hu i c := by
  have hiSup :
      Measurable fun y : SourceCubeSpace n =>
        ⨆ q : {q' : ℚ // (q' : ℝ) < c},
          coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox u hu i c q y :=
    Measurable.iSup happrox
  change Measurable fun y : SourceCubeSpace n =>
    coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit u hu i c y
  convert hiSup using 1
  ext y
  exact coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit_eq_iSup_ratApprox i c y

/-- A rational left-approximation of the Stieltjes endpoint left limit is the infimum of the
underlying clamped right-derivative extension at rational points to its right. -/
theorem coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox_eq_iInf_extension
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    (i : Fin n) (c : ℝ) (q : {q' : ℚ // (q' : ℝ) < c}) (y : SourceCubeSpace n) :
    coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox u hu i c q y =
      ⨅ r : {r' : ℚ // (q : ℝ) < (r' : ℝ)},
        coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox
          u hu i (q : ℝ) r y := by
  classical
  by_cases hy : y ∈ sourceOpenCube n 1
  · let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
    let hmono := ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy
    let g := sourceRightDerivExtension v
    have hg : Monotone g := monotone_sourceRightDerivExtension hmono
    have hright :
        Function.rightLim g (q : ℝ) =
          ⨅ r : {r' : ℚ // (q : ℝ) < (r' : ℝ)}, g (r : ℝ) :=
      monotone_rightLim_eq_iInf_rat_gt hg (q : ℝ)
    have hF :
        sourceRightDerivStieltjesSecondDerivativeFunction v hmono (q : ℝ) =
          Function.rightLim g (q : ℝ) := by
      simp [sourceRightDerivStieltjesSecondDerivativeFunction_apply, g]
    calc
      coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox u hu i c q y =
          sourceRightDerivStieltjesSecondDerivativeFunction v hmono (q : ℝ) := by
        simp [coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox, hy,
          v]
      _ = Function.rightLim g (q : ℝ) := hF
      _ = ⨅ r : {r' : ℚ // (q : ℝ) < (r' : ℝ)}, g (r : ℝ) := hright
      _ = ⨅ r : {r' : ℚ // (q : ℝ) < (r' : ℝ)},
            coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox
              u hu i (q : ℝ) r y := by
        simp [coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox,
          coordinateSliceConvexSourceRightDerivExtensionValue, hy, v, g]
  · simp [coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox,
      coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox,
      coordinateSliceConvexSourceRightDerivExtensionValue, hy]

/-- Measurability of the underlying extension approximations gives measurability of one rational
left-approximation of the Stieltjes endpoint left limit. -/
theorem stieltjesEndpointLeftLimitRatApproxMeasurable_of_extensionRatApprox
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {c : ℝ} {q : {q' : ℚ // (q' : ℝ) < c}}
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApproxMeasurable
        u hu i (q : ℝ)) :
    Measurable fun y : SourceCubeSpace n =>
      coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox u hu i c q y := by
  have hiInf :
      Measurable fun y : SourceCubeSpace n =>
        ⨅ r : {r' : ℚ // (q : ℝ) < (r' : ℝ)},
          coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox
            u hu i (q : ℝ) r y :=
    Measurable.iInf happrox
  convert hiInf using 1
  ext y
  exact
    coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox_eq_iInf_extension
      i c q y

/-- Global fixed clamped-extension measurability gives measurability of every rational
left-approximation of a Stieltjes endpoint left limit. -/
theorem stieltjesEndpointLeftLimitRatApproxMeasurable_of_extensionValue
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {c : ℝ} {q : {q' : ℚ // (q' : ℝ) < c}}
    (hvalue : CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable u hu) :
    Measurable fun y : SourceCubeSpace n =>
      coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox u hu i c q y :=
  stieltjesEndpointLeftLimitRatApproxMeasurable_of_extensionRatApprox
    (stieltjesEvaluationExtensionRatApproxMeasurable_of_extensionValue hvalue)

/-- Global fixed clamped-extension measurability gives measurability of one right-continuous
Stieltjes endpoint value. -/
theorem stieltjesEndpointValueAtMeasurable_of_extensionValue
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {c : ℝ}
    (hvalue : CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable u hu) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueAtMeasurable u hu i c :=
  stieltjesEndpointValueAtMeasurable_of_ratApprox
    (fun _ => stieltjesEndpointValueRatApproxMeasurable_of_extensionValue hvalue)

/-- Global fixed clamped-extension measurability gives measurability of one Stieltjes endpoint
left limit. -/
theorem stieltjesEndpointLeftLimitAtMeasurable_of_extensionValue
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {c : ℝ}
    (hvalue : CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable u hu) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitAtMeasurable u hu i c :=
  stieltjesEndpointLeftLimitAtMeasurable_of_ratApprox
    (fun _ => stieltjesEndpointLeftLimitRatApproxMeasurable_of_extensionValue hvalue)

/-- Global fixed clamped-extension measurability gives the packaged endpoint-value
measurability for any endpoint enumeration. -/
theorem CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable.of_extensionValue
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a : ℕ → ℝ}
    (hvalue : CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable u hu) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable u hu a :=
  CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable.of_at
    (fun _ _ => stieltjesEndpointValueAtMeasurable_of_extensionValue hvalue)

/-- Global fixed clamped-extension measurability gives the packaged endpoint-left-limit
measurability for any endpoint enumeration. -/
theorem
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable.of_extensionValue
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {b : ℕ → ℝ}
    (hvalue : CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable u hu) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable u hu b :=
  CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable.of_at
    (fun _ _ => stieltjesEndpointLeftLimitAtMeasurable_of_extensionValue hvalue)

/-- Convex source-local Stieltjes endpoint values are measurable for any endpoint enumeration. -/
theorem CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable.of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a : ℕ → ℝ} :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable u hu a :=
  CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable.of_extensionValue
    coordinateSliceConvexSourceRightDerivExtensionValue_measurable

/-- Convex source-local Stieltjes endpoint left limits are measurable for any endpoint
enumeration. -/
theorem CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable.of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {b : ℕ → ℝ} :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable u hu b :=
  CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable.of_extensionValue
    coordinateSliceConvexSourceRightDerivExtensionValue_measurable

/-- The endpoint-average expression is the quotient of the endpoint left limit minus the endpoint
value. -/
theorem coordinateSliceConvexSourceRightDerivStieltjes_endpointAverageExpression_eq
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    (i : Fin n) (a b : ℝ) (y : SourceCubeSpace n) :
    coordinateSliceConvexSourceRightDerivStieltjesEndpointAverageExpression u hu i a b y =
      (coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit u hu i b y -
        coordinateSliceConvexSourceRightDerivStieltjesEndpointValue u hu i a y) / (b - a) := by
  classical
  by_cases hy : y ∈ sourceOpenCube n 1
  · simp [coordinateSliceConvexSourceRightDerivStieltjesEndpointAverageExpression,
      coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit,
      coordinateSliceConvexSourceRightDerivStieltjesEndpointValue, hy]
  · simp [coordinateSliceConvexSourceRightDerivStieltjesEndpointAverageExpression,
      coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit,
      coordinateSliceConvexSourceRightDerivStieltjesEndpointValue, hy]

/-- Measurability of one endpoint value and one endpoint left limit gives measurability of the
corresponding endpoint-average expression. -/
theorem stieltjesEndpointAverageAtMeasurable_of_endpointValue_leftLimit
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {i : Fin n} {a b : ℝ}
    (hleft :
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitAtMeasurable u hu i b)
    (hvalue :
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueAtMeasurable u hu i a) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageAtMeasurable u hu i a b := by
  change Measurable fun y : SourceCubeSpace n =>
    coordinateSliceConvexSourceRightDerivStieltjesEndpointAverageExpression u hu i a b y
  have hquot :
      Measurable fun y : SourceCubeSpace n =>
        (coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit u hu i b y -
          coordinateSliceConvexSourceRightDerivStieltjesEndpointValue u hu i a y) /
            (b - a) :=
    (hleft.sub hvalue).div_const _
  convert hquot using 1
  ext y
  exact (coordinateSliceConvexSourceRightDerivStieltjes_endpointAverageExpression_eq i a b y)

/-- Measurability of endpoint values and endpoint left limits gives measurability of the
endpoint-average expressions. -/
theorem CoordinateSliceStieltjesEndpointAverageMeasurable.of_endpointValue_leftLimit
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ}
    (hleft :
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable u hu b)
    (hvalue :
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable u hu a) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageMeasurable u hu a b := by
  intro i k
  exact stieltjesEndpointAverageAtMeasurable_of_endpointValue_leftLimit
    (hleft i k) (hvalue i k)

/-- Convex source-local Stieltjes endpoint-average expressions are measurable for any endpoint
enumeration. -/
theorem CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageMeasurable.of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageMeasurable u hu a b :=
  CoordinateSliceStieltjesEndpointAverageMeasurable.of_endpointValue_leftLimit
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable.of_convex
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable.of_convex

/-- For a genuine interval `a < b`, the fixed-interval average of the concrete convex Stieltjes
slice measure is the corresponding endpoint expression. -/
theorem coordinateSliceConvexSourceRightDerivStieltjes_average_eq_endpointAverageExpression
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    (i : Fin n) {a b : ℝ} (hab : a < b) (y : SourceCubeSpace n) :
    openIntervalMeasureAverage
        (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu i y) a b =
      coordinateSliceConvexSourceRightDerivStieltjesEndpointAverageExpression u hu i a b y := by
  classical
  by_cases hy : y ∈ sourceOpenCube n 1
  · simp [coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily,
      coordinateSliceSourceRightDerivStieltjesMeasureFamily,
      coordinateSliceConvexSourceRightDerivStieltjesEndpointAverageExpression,
      openIntervalMeasureAverage, hy,
      sourceRightDerivStieltjesSecondDerivativeMeasure_real_Ioo, hab]
  · simp [coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily,
      coordinateSliceSourceRightDerivStieltjesMeasureFamily,
      coordinateSliceConvexSourceRightDerivStieltjesEndpointAverageExpression,
      openIntervalMeasureAverage, hy]

end AleksandrovDifferentiability
