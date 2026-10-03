/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.Selection.LocallyUniformApproximation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Compact selection lemmas for stability arguments

This file packages the compact-extremum tools used in viscosity stability
proofs. The main results convert maximum or minimum points of `uᵢ - φ` on a
compact set `K` into superjet or subjet graph points, and then into tail
closure membership when the selected points, values, and jets converge. The
development lives in the `Selection/` submodules; this file re-exports all of
them.
-/

@[expose] public section
