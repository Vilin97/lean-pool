/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/
module

public import LeanPool.UlmsTheorem.Regression
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset

/-!
# Ulm's theorem for countable reduced abelian p-groups

Source: url:https://github.com/elanroth/UlmsTheorem
Authors: Elan Roth
Status: verified
Main declarations: `UlmsTheorem.ulm_theorem`
Tags: abelian-groups, p-groups, classification-theorems, ordinal-filtrations, ulm-invariants
MSC: 20K10
-/

@[expose] public section
