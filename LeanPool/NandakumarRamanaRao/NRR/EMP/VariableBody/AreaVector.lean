/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Basic
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CellAreaContinuity

/-!
# `NRR.EMP.VariableBody.AreaVector` — the variable-body area vector

The scalar cell-area continuity of `CellAreaContinuity` is lifted to the finite area vector
`areaVec hA C s w : Fin n → ℝ`, whose `i`-th component is the restricted power-cell area
`cellArea hA C s w i`. The target area `targetArea C n = C.body.area / n` is the common value that
an equal-area weight assigns to every cell.

* `areaVec` — the vector of restricted cell areas.
* `targetArea` — the average cell area `C.body.area / n`.
* `continuous_areaVec` — joint continuity of the area vector in body, sites, and weights.
* `continuous_targetArea` — continuity of the average area in the parent subbody.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR.EMP.VariableBody

variable {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}

/-- The **area vector** of the variable body `C` for sites `s` and weights `w`: the vector whose
`i`-th component is the area of the restricted power cell of site `i`. -/
noncomputable def areaVec
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => cellArea hA C s w i

/-- The **target area** for an equal-area partition of the variable body `C` into `n` cells: the
average cell area `C.body.area / n`. -/
noncomputable def targetArea
    (C : BodySpace K A) (n : ℕ) : ℝ :=
  C.body.area / (n : ℝ)

@[simp] theorem areaVec_apply
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    areaVec hA C s w i = cellArea hA C s w i :=
  rfl

/-- **Joint continuity of the area vector.** The finite vector of restricted cell areas depends
continuously on the parent subbody, the configuration, and the weight vector. -/
theorem continuous_areaVec
    (hA : 0 < A) :
    Continuous fun z :
        BodySpace K A × Config n × (Fin n → ℝ) =>
      areaVec hA z.1 z.2.1 z.2.2 := by
  refine continuous_pi (fun i => ?_)
  exact continuous_cellArea hA i

/-- **Continuity of the target area.** The average cell area depends continuously on the parent
subbody through the continuity of the area functional. -/
theorem continuous_targetArea :
    Continuous fun C : BodySpace K A => targetArea C n := by
  simp only [targetArea]
  exact ((ConvexSubbody.continuous_area K).comp BodySpace.continuous_body).div_const _

end NRR.EMP.VariableBody
