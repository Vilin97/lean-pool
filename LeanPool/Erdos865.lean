/-
Copyright (c) 2026 Ricky Cipollini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ricky Cipollini
-/
module

public import LeanPool.Erdos865.Defs
public import LeanPool.Erdos865.FoldedAux
public import LeanPool.Erdos865.FoldedMain
public import LeanPool.Erdos865.Folding
public import LeanPool.Erdos865.Sharpness
public import LeanPool.Erdos865.UpperBound
public import LeanPool.Erdos865.Main
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# A sharp 5/8 bound for Erdős Problem 865

Source: url:https://github.com/mrricky22/erdos-865-lean
Authors: Ricky Cipollini
Status: verified
Main declarations: `Erdos865.erdos865_upper_bound`, `Erdos865.sharpness`
Tags: additive-combinatorics, erdos-problems, sum-free-sets, combinatorics
MSC: 11B75, 11B13
-/

@[expose] public section
