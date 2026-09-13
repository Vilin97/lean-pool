/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.CoordinateFree.EllipticCurve
public import LeanPool.RiemannRochFunctionFields.CoordinateFree.RiemannRoch
public import LeanPool.RiemannRochFunctionFields.EllipticCurve.ConcreteRegression
public import LeanPool.RiemannRochFunctionFields.RiemannRochTheorem.Regression
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Riemann–Roch for algebraic function fields

Source: url:https://github.com/vaca22/riemann-roch-function-fields
Authors: Guanghao Li
Status: verified
Main declarations: `FunctionField.riemann_roch`
Tags: riemann-roch, function-fields, algebraic-curves, weil-differentials, elliptic-curves
MSC: 14H05, 11R58, 14H52
-/

@[expose] public section
