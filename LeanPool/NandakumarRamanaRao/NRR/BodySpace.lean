/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.BodySpace.Basic
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.Topology
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.ConvexClosed
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.Compactness
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.BoundaryNull
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.MembershipStability
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.AreaContinuity
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.PositiveArea
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.SupportWidthContinuity
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.PerimeterContinuity
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.FullBody

/-!
# `NRR.BodySpace` — convex-body hyperspace

This aggregator re-exports the convex-body hyperspace API in dependency order.

Three body types are kept distinct:

* `NRR.Geometry.ConvexBody Plane` is the solid planar body type: compact, convex, with nonempty
  interior. Solid bodies alone are not closed under Hausdorff degeneration.
* `NRR.ConvexSubbody K` is the fixed-parent hyperspace of compact nonempty convex subsets of a
  solid body `K`. Its elements may be lower-dimensional, and the space is compact.
* `NRR.BodySpace K A` is the closed lower-area subspace `{C : ConvexSubbody K // A ≤ C.area}`.
  When `A > 0`, every element is solid and admits the continuous bridge
  `BodySpace.toGeometryConvexBody`.

The metric is Mathlib's Hausdorff distance on nonempty compact planar sets, transported through
`ConvexSubbody.toNonemptyCompacts`. The API includes continuity of area and Cauchy perimeter and
pointwise membership stability under Hausdorff convergence.
-/
