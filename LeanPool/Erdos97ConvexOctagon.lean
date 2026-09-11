/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.Main
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-!
# The Convex-Octagon Case of Erdős Problem 97

Source: doi:10.1080/00029890.1946.11991674, url:https://www.erdosproblems.com/97
Authors: Egor Lyfar
Status: verified
Main declarations: `Erdos97Octagon.erdos97_convex_octagon`
Tags: discrete-geometry, distance-geometry, erdos-problems, convexity
MSC: 51K05, 52A10
-/

@[expose] public section
