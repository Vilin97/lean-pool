/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Straszewicz
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.ExposedCluster
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Recession

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Rockafellar-style subgradient cluster density

This compatibility module re-exports the conceptual pieces of the Rockafellar cluster-density
formalization. The implementation is split across `RockafellarCluster.Basic`,
`RockafellarCluster.Exposed`, `RockafellarCluster.SupportingBall`,
`RockafellarCluster.ConvexHull`, `RockafellarCluster.Straszewicz`,
`RockafellarCluster.ExposedCluster`, and `RockafellarCluster.Recession`.
-/
