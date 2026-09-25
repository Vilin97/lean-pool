/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Phase1Interface
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Basic
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.HalfspaceCoefficients
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.IndicatorStability
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CellAreaContinuity
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.AreaVector
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.EqualAreaRelation
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CompactSiteFamily
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.WeightBounds
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.WeightBox
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.ClosedGraph
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.NormalizedWeightContinuity
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CanonicalCell
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CanonicalCellGraph
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CanonicalCellContinuity
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Children
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Partition

/-!
# `NRR.EMP.VariableBody` — variable-body equal-area power partitions

This public aggregator exposes the stable variable-body API for the Akopyan–Avvakumov–Karasev
power-partition development. All results are stated over a compact metric parameter space with a
continuous site family:

```
[MetricSpace X] [CompactSpace X]    sites : C(X, Config n)
```

The parent body varies in the Hausdorff subbody space `BodySpace K A` of a fixed planar parent
`K`. Over this compact family the development provides:

* continuity of each power-cell area (`continuous_cellArea`);
* the closed equal-area relation and the resulting continuity of the canonical normalized
  equal-area weight (`isClosed_isNormalizedEqualAreaWeight`, `weightBound`,
  `continuous_normalizedWeight_compactFamily`);
* continuity of the canonical cells and their packaging as subbodies
  (`continuous_canonicalCell`);
* the canonical children `child`, each lying in `BodySpace K (A / (n : ℝ))`, with continuous
  bodies, areas, and perimeters (`continuous_child`, `continuous_child_perimeter`);
* the pointwise equal-area partition exposed only as a dependent witness (`witness`), with no
  topology placed on `ConvexPartition`.

The continuity results hold on this compact family only; `Config n` itself is not claimed to be
compact. The proofs go through the equal-area existence and uniqueness cores reached via
`EMP.normalizedWeight`, and do not invoke `EMP.continuous_normalizedWeight_core`.
-/

@[expose] public section
