/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Jensen.MainTheorems

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Jensen Contact-Set Theorem

This module contains the localized Jensen contact-set theorem and the
smooth convex approximation machinery used to prove it. The later
Aleksandrov--Jensen matrix assembly imports this file and starts from the
contact-set theorem as a reusable input. The development lives in the
`Jensen/` submodules; this file re-exports all of them.
-/

@[expose] public section
