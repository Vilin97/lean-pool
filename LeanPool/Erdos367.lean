/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/
module

public import LeanPool.Erdos367.K3AbcUpperBound
public import LeanPool.Erdos367.GeneralKUpperBound
public import LeanPool.Erdos367.RFullLowerBound
public import LeanPool.Erdos367.PellLimsup
public import LeanPool.Erdos367.Core139
public import LeanPool.Erdos367.Core4027
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Erdős Problem #367

Source: url:https://github.com/scottdhughes/erdos367
Authors: Scott D. Hughes
Status: verified
Main declarations: `Erdos367.erdos_367_k3`, `RFullOdd.erdos367_iv`, `Erdos367.erdos367`
Tags: number-theory, erdos-problems, powerful-numbers, abc-conjecture, pell-equations
MSC: 11D09, 11N25, 11D45
-/

@[expose] public section
