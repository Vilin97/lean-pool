/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.MatrixConclusion

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Aleksandrov--Jensen theorem for semiconvex functions

This file gives the public-facing theorem target for the
Aleksandrov--Jensen part of the finite-dimensional maximum principle. The
localized Jensen contact-set theorem lives in
`ViscositySolns.Analysis.SemiconvexJensen.Jensen`; this module assembles it
with Aleksandrov differentiability and the matrix conclusion used by the
comparison proof. The remaining development lives in the
`ContactSelection` and `MatrixConclusion` submodules; this file re-exports
both of them.
-/

@[expose] public section
