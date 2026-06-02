/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Complex.Basic

/-!
# Shared typeclass instances for `ℝ`-scalar-on-`ℂ`

In mathlib 4.29, `NormSMulClass.toIsBoundedSMul` is no longer an instance
(to avoid loops), which breaks the chain

    NormedSpace ℝ ℂ → NormSMulClass ℝ ℂ → IsBoundedSMul ℝ ℂ → ContinuousSMul ℝ ℂ

We provide all three instances here so every file in the project can
`import LeanModularForms.ForMathlib.Instances` instead of redeclaring them.

We also provide `IsScalarTower ℝ ℂ ℂ` which was previously redeclared
in several files with different proof terms.
-/

private noncomputable instance instNormSMulClassRealComplex : NormSMulClass ℝ ℂ :=
  NormedSpace.toNormSMulClass

private noncomputable instance instIsBoundedSMulRealComplex : IsBoundedSMul ℝ ℂ :=
  NormSMulClass.toIsBoundedSMul

private noncomputable instance instContinuousSMulRealComplex : ContinuousSMul ℝ ℂ :=
  IsBoundedSMul.continuousSMul

private instance instIsScalarTowerRealComplexComplex : IsScalarTower ℝ ℂ ℂ := inferInstance
