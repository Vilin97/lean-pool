/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.OperatorCondition.TraceForm

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Operator comparison condition for the Ishii matrix inequality

This file specializes the structural continuity condition for operators to the
matrix relation used in the quadratic doubling-of-variables argument. The
development lives in the `OperatorCondition/` submodules; this file re-exports
all of them.
-/

@[expose] public section
