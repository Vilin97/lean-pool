/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/
module

public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Push
import LeanPool.FormalizationOfBoundedArithmetic.Register
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor

/-!
# LeanPool.FormalizationOfBoundedArithmetic.SimpRules
-/

@[expose] public section

attribute [delta0_simps]
  Sum.elim_inl
  Sum.elim_inr
  Sum.swap_inl
  Sum.swap_inr
  Function.comp_apply
  and_self
  not_true_eq_false
