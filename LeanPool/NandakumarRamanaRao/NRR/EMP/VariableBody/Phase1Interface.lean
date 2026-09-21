/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.BodySpace
import LeanPool.NandakumarRamanaRao.NRR.ConfigurationSpace

/-!
# Convex-body interface for variable-body power partitions

This module re-exports the convex-body hyperspace API used by the variable-body power-partition
construction and defines its parameter-space conventions.

## Re-exported convex-body interface

The interface includes compactness of `ConvexSubbody` and `BodySpace`, continuity of area and of
the body projection, positivity at a positive area threshold, and membership stability under
Hausdorff convergence. The metric is Mathlib's Hausdorff metric inherited through
`TopologicalSpace.NonemptyCompacts Plane`; no competing metric or topology is introduced.

## Body projections

* `NRR.BodySpace.body : BodySpace K A → ConvexSubbody K` lands in the fixed-parent hyperspace,
  whose elements may be lower-dimensional.
* `NRR.BodySpace.toGeometryConvexBody (hA : 0 < A)` lands in the solid planar convex-body type and
  is continuous.

## Parameterization

Continuity results are stated over a compact metric parameter space `X` carrying a continuous site
family `sites : C(X, Config n)`. The configuration space `Config n` itself is not assumed compact.
-/

open MeasureTheory Filter Topology

open NRR.Geometry

namespace NRR.EMP.VariableBody

/-- A **continuous site family** over a parameter space `X`: a continuous map assigning to each
parameter a configuration of `n` distinct labelled planar sites. Continuity results use a compact
metric `X`; `Config n` itself is not assumed compact. -/
abbrev SiteFamily (X : Type*) [TopologicalSpace X] (n : ℕ) :=
  C(X, Config n)

/-- The variable-body parameter space: the compact convex-body factor `BodySpace K A` paired
with an auxiliary parameter space `X`, typically the site-family parameter. -/
abbrev Param
    (K : Geometry.ConvexBody Plane) (A : ℝ)
    (X : Type*) :=
  BodySpace K A × X

end NRR.EMP.VariableBody
