/-
Copyright (c) 2026 KitaKen1. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KitaKen1
-/
module

public import LeanPool.Erdos346.LimitExistsVariant
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset

/-!
# Erdős Problem 346: Ratio Limit Forces the Golden Ratio

Source: url:https://www.erdosproblems.com/346
Authors: KitaKen1
Status: verified
Main declarations: `Erdos346.intended_problem_if_limit_exists`
Tags: number-theory, golden-ratio, erdos-problems
MSC: 11B05, 11J70
-/

@[expose] public section
