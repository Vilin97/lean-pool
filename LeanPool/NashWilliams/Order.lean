/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
module

public import LeanPool.NashWilliams.Order.TwoBQO
public import LeanPool.NashWilliams.Order.WellQuasiOrder
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-! Results about well- and better-quasi-orders. -/

@[expose] public section
