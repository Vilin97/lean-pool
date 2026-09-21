/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.EMP.AreaVectorTarget
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightCellRigidity
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightCoercivity
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightMaxUnion
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightOutward
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightsExistence
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightsUniqueness
import LeanPool.NandakumarRamanaRao.NRR.EMP.NormalizedAreaDeviation
import LeanPool.NandakumarRamanaRao.NRR.EMP.NormalizedWeightSelection
import LeanPool.NandakumarRamanaRao.NRR.EMP.NormalizedWeights
import LeanPool.NandakumarRamanaRao.NRR.EMP.OptimalTransportCore
import LeanPool.NandakumarRamanaRao.NRR.EMP.PartitionFromPowerDiagram
import LeanPool.NandakumarRamanaRao.NRR.EMP.PowerCellPositiveArea
import LeanPool.NandakumarRamanaRao.NRR.EMP.PowerPartitionPerimeter
import LeanPool.NandakumarRamanaRao.NRR.EMP.PowerPartitionPieces
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody
import LeanPool.NandakumarRamanaRao.NRR.EMP.WeightShift
import LeanPool.NandakumarRamanaRao.NRR.EMP.WeightSpace

/-! Supporting modules for Equal-area and equal-perimeter convex partitions. -/
