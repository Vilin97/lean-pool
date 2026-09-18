/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import LeanPool.Erdos403.Basic
public import LeanPool.Erdos403.FactBase
public import LeanPool.Erdos403.Sharp
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Sums of Distinct Factorials That Are Powers of Two (Erdos Problem 403)

Source: url:https://www.erdosproblems.com/403
Authors: Trevor Morris
Status: verified
Main declarations: `Erdos403.erdos_403_sharp`, `Erdos403.erdos_403_finite`
Tags: number-theory, factorials, erdos-problems
MSC: 11B83
-/

@[expose] public section
