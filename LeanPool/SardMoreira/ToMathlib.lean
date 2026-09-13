/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import LeanPool.SardMoreira.ToMathlib.ContinuousLinearMap
public import LeanPool.SardMoreira.ToMathlib.PR31960
public import LeanPool.SardMoreira.ToMathlib.PR32186
public import LeanPool.SardMoreira.ToMathlib.PR32986
public import LeanPool.SardMoreira.ToMathlib.PR32993
public import LeanPool.SardMoreira.ToMathlib.PR33029
public import LeanPool.SardMoreira.ToMathlib.PR33114
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# Lemmas slated for Mathlib

This module gathers auxiliary lemmas from the SardMoreira project that are
candidates for upstreaming to Mathlib.
-/

@[expose] public section
