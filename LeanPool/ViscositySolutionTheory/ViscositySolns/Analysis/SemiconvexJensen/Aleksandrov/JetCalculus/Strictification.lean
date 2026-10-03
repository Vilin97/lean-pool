/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Strictification.StrictifiedObjective

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Strictification and jet bridges for the Aleksandrov--Jensen argument

Quartic strictification, compact Hessian, and jet transport lemmas used
before the contact-set and approximation arguments in `SemiconvexJensen`.
The development lives in the `Strictification/` submodules; this file
re-exports all of them.
-/

@[expose] public section
