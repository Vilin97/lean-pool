/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/
module

public import LeanPool.KaltonRoberts.Defs
public import LeanPool.KaltonRoberts.Numerical
public import LeanPool.KaltonRoberts.Collections
public import LeanPool.KaltonRoberts.Lemmas
public import LeanPool.KaltonRoberts.Pipeline
public import LeanPool.KaltonRoberts.PipelineEps
public import LeanPool.KaltonRoberts.EpsilonRecombination
public import LeanPool.KaltonRoberts.MainTheorem
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Halving the Kalton-Roberts upper bound

Source: arxiv:2606.06807, url:https://github.com/boonsuan/KaltonRoberts
Authors: Ho Boon Suan
Status: verified
Main declarations: `KaltonRoberts.KR_constant_lt`
Tags: functional-analysis, finitely-additive-measures, kalton-roberts
MSC: 46B20, 28A12, 05C35
-/

@[expose] public section
