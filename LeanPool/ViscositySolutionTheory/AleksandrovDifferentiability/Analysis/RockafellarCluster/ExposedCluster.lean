/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.ExposedCluster.Local

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Exposed subgradients as gradient cluster limits

This compatibility module re-exports the conceptual pieces of the exposed-cluster part of the
Rockafellar formalization:

* `RockafellarCluster.ExposedCluster.Pointwise` contains the pointwise exposed-subgradient
  cluster bridges.
* `RockafellarCluster.ExposedCluster.Compact` contains compact and bounded Straszewicz
  reductions for subdifferentials.
* `RockafellarCluster.ExposedCluster.Local` contains the final local cluster-density assembly
  wrappers.
-/
