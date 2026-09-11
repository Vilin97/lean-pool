/-
Copyright (c) 2026 Daniel Smania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Smania
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

public import LeanPool.Burkholder.Majorants
public import LeanPool.Burkholder.MartingaleTransforms
import Mathlib.Tactic.Positivity.Finset

/-!
# Burkholder Martingale Transform Inequality

Source: doi:10.1214/aop/1176993220
Authors: Daniel Smania
Status: verified
Main declarations: `MeasureTheory.Lp_Burkholder_inequality_martingaleTransform`
Tags: probability, martingales, burkholder-inequality
MSC: 60G42
-/

@[expose] public section
