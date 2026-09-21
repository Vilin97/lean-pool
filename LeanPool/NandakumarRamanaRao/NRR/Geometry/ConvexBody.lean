/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.AffineOps
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Basic
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.HalfspaceCut
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Interior
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.LinearImage
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarCircle
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeter
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterBasic
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterContinuity
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterMonotonicity
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterTransform
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PositiveAreaInterior
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunction
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionBasic
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionContinuity
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionParametric
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionTransform
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Topology
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Width
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthContinuity
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthFamilies
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthIdentities

/-! Supporting modules for Equal-area and equal-perimeter convex partitions. -/
