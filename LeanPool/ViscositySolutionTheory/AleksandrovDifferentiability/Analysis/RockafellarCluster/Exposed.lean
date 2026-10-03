/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Directional
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Mathlib

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Exposed faces and exposed points for the Rockafellar cluster argument

This compatibility module re-exports the exposed-face and exposed-point pieces used in the
Rockafellar cluster-density formalization:

* `RockafellarCluster.Exposed.Face` defines exposed faces and proves their basic geometric
  properties.
* `RockafellarCluster.Exposed.Thickening` contains norm-thickening and cluster-point tools.
* `RockafellarCluster.Exposed.Directional` contains the directional exposed-face
  outer-semicontinuity wrappers.
* `RockafellarCluster.Exposed.Point` contains exposed-point normalization and singleton-face
  lemmas.
* `RockafellarCluster.Exposed.Mathlib` bridges the project-local exposed-point carrier with
  Mathlib's `Set.exposedPoints`.
-/
