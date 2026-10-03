/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Dirichlet
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.Corollaries
public import LeanPool.ViscositySolutionTheory.ViscositySolns.TestFunctions.Characterization
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProperComparison.Compact.ConstantShiftBoundary

/-!
# Viscosity solutions, Aleksandrov differentiability and harmonic Dirichlet problems

Source: arxiv:math/9207212, url:https://github.com/willmfeldman/viscosity-solution-theory/tree/067e2540ad1594408c0b6145c5bde01b4d5791a9
Authors: William M. Feldman, AleksandrovDifferentiability contributors, The Tau Ceti contributors
Status: verified
Main declarations: `ViscositySolns.dirichlet_harmonic_modulus_of_uniformExteriorSphere`
Tags: pde, viscosity-solutions, convex-analysis, harmonic-functions, perron-method
MSC: 35D40, 35J60, 26B25
-/

/-! ## Imported scope and attribution

Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

The first public release was v0.1.0, published on 26 September 2026.
The source revision is pinned above. This port retains the dependency closure of
harmonic Dirichlet existence, compact comparison, uniqueness and smooth test-function
characterization: 126 viscosity modules and 83 Aleksandrov differentiability modules.
The bundled Aleksandrov dependency is from
https://github.com/willmfeldman/aleksandrov-differentiability/tree/6b318246f170ac472de4728e22f95a2adae420a5
and is also Apache-2.0. Its original copyright belongs to the
AleksandrovDifferentiability contributors. Four Weyl-lemma files preserve the
Tau Ceti contributors' copyright and their per-file source and modification notices.

Both upstream manifests disclose AI-assisted proof development with human direction
and review; the viscosity manifest does not record exact models or per-declaration
provenance. The pool records AI provenance conservatively, without attributing
unrecorded proof contributions to human reviewers.

The maximum principle retained here concerns quadratic penalties and global quadratic
test functions; it does not assert the full CIL theorem for arbitrary C² penalties.
General Perron existence is an assembly theorem with explicit analytic assumptions.
The harmonic application discharges those assumptions, including the analytic
Aleksandrov input, and concludes classical harmonicity through Weyl's lemma.
-/
