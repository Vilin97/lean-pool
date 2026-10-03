/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.ExternalAleksandrov
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Strictification

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Strictification and jet bridges for the Aleksandrov--Jensen argument

This module re-exports the external Aleksandrov adapter and strictification
calculus for the historical import path. The strictification implementation lives in
`ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Strictification`.
-/

@[expose] public section
