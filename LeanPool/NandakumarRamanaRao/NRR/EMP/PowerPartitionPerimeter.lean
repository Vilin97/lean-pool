/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.EMP.PartitionFromPowerDiagram
public import LeanPool.NandakumarRamanaRao.NRR.Partition.PerimeterVector

/-!
# `NRR.EMP.PowerPartitionPerimeter` — perimeter vector of the canonical power partition

This module specializes the generic convex-partition perimeter API
(`NRR.ConvexPartition.perimeterVec`, `averagePerimeter`, `perimeterDeviation`) to the
canonical equal-area power partition `EMP.powerPartition`.

The power-partition parameter profile is the one fixed in the project:

```lean
(K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n) (hK : 0 < K.area)
```

## Public API

* `EMP.powerPartitionPerimeterVec` — the perimeter vector of the canonical power partition.
* `EMP.powerPartitionAveragePerimeter` — its average perimeter.
* `EMP.powerPartitionPerimeterDeviation` — its perimeter-deviation vector.
* `EMP.powerPartitionPerimeterVec_apply` — the defining simp lemma for the perimeter vector.
* `EMP.sum_powerPartitionPerimeterDeviation_eq_zero` — the deviation vector sums to zero.

No continuity, equivariance, or test-map material is introduced here.
-/

@[expose] public section

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR

variable {n : ℕ}

/-- The **perimeter vector** of the canonical equal-area power partition. -/
noncomputable def EMP.powerPartitionPerimeterVec
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n) (hK : 0 < K.area) :
    Fin n → ℝ :=
  (EMP.powerPartition K s hn hK).perimeterVec

/-- The **average perimeter** of the canonical equal-area power partition. -/
noncomputable def EMP.powerPartitionAveragePerimeter
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n) (hK : 0 < K.area) : ℝ :=
  (EMP.powerPartition K s hn hK).averagePerimeter

/-- The **perimeter-deviation vector** of the canonical equal-area power partition. -/
noncomputable def EMP.powerPartitionPerimeterDeviation
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n) (hK : 0 < K.area) :
    Fin n → ℝ :=
  (EMP.powerPartition K s hn hK).perimeterDeviation

/-- The `i`-th entry of the power-partition perimeter vector is the perimeter of its `i`-th
piece. -/
@[simp] theorem EMP.powerPartitionPerimeterVec_apply
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n) (hK : 0 < K.area) (i : Fin n) :
    EMP.powerPartitionPerimeterVec K s hn hK i =
      perimeter ((EMP.powerPartition K s hn hK).piece i) := rfl

/-- The perimeter-deviation vector of the canonical equal-area power partition sums to zero. -/
theorem EMP.sum_powerPartitionPerimeterDeviation_eq_zero
    (K : Geometry.ConvexBody Plane) (s : Config n) (hn : 0 < n) (hK : 0 < K.area) :
    ∑ i, EMP.powerPartitionPerimeterDeviation K s hn hK i = 0 :=
  (EMP.powerPartition K s hn hK).sum_perimeterDeviation_eq_zero hn

end NRR
