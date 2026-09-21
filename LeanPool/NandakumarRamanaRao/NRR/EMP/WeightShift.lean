/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights

/-!
# `NRR.EMP.WeightShift` — additive‑constant shift invariance of power weights

Adding a fixed constant `c` to *all* power weights leaves every power cell — and hence every
restricted cell, the whole area vector, and the equal‑area property — unchanged. Intuitively,
the power distance `powerDist s w i x = ‖x - sᵢ‖² - wᵢ` shifts by exactly `-c` at *every* site
simultaneously, so all the comparisons `powerDist i x ≤ powerDist j x` defining the cells are
preserved.

## Definition

* `EMP.addConstWeight w c = fun i => w i + c` — the constant shift of a weight vector.

## API

* `PowerDiagram.powerDist_addConstWeight` — the power distance shifts by `-c`.
* `PowerDiagram.cell_addConstWeight` — power cells are unchanged.
* `PowerDiagram.bodyCellSet_addConstWeight` — restricted power cells are unchanged.
* `EMP.areaVec_addConstWeight` — the equal‑area area vector is unchanged.
* `EMP.IsEqualAreaWeight_addConstWeight` — the equal‑area property is preserved.

No equal‑area existence, no normalization, and no variation of sites is used: the sites `s`
are held fixed throughout and every result is a pure algebraic cancellation of the constant.
-/

open NRR NRR.Geometry NRR.PowerDiagram

namespace NRR

variable {n : ℕ}

namespace EMP

/-- **Constant shift of a weight vector**: add the fixed constant `c` to every weight. -/
def addConstWeight (w : Fin n → ℝ) (c : ℝ) : Fin n → ℝ :=
  fun i => w i + c

@[simp] theorem addConstWeight_apply (w : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    addConstWeight w c i = w i + c := rfl

end EMP

namespace PowerDiagram

/-- **Power distance under a constant weight shift.** Adding `c` to all weights decreases every
power distance by exactly `c`. -/
theorem powerDist_addConstWeight
    (s : Fin n → Plane) (w : Fin n → ℝ) (c : ℝ) (i : Fin n) (x : Plane) :
    powerDist s (EMP.addConstWeight w c) i x = powerDist s w i x - c := by
  simp only [powerDist, EMP.addConstWeight_apply]
  ring

/-- **Cell invariance under a constant weight shift.** Since every power distance shifts by the
same constant, all defining comparisons are preserved, so the power cell is unchanged. -/
theorem cell_addConstWeight
    (s : Fin n → Plane) (w : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    cell s (EMP.addConstWeight w c) i = cell s w i := by
  ext x
  simp only [cell, Set.mem_ofPred_eq, powerDist_addConstWeight]
  constructor <;> intro h j <;> have := h j <;> linarith [this]

/-- **Restricted‑cell invariance under a constant weight shift.** Immediate from
`cell_addConstWeight`, since the restricted cell is `K ∩ cell`. -/
theorem bodyCellSet_addConstWeight
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    bodyCellSet K s (EMP.addConstWeight w c) i = bodyCellSet K s w i := by
  simp only [bodyCellSet_def, cell_addConstWeight]

end PowerDiagram

namespace EMP

/-- **Area‑vector invariance under a constant weight shift.** Every restricted cell is unchanged,
hence so is its area and the whole area vector. -/
theorem areaVec_addConstWeight
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) (c : ℝ) :
    EMP.areaVec K s (EMP.addConstWeight w c) = EMP.areaVec K s w := by
  funext i
  simp only [EMP.areaVec_apply, NRR.PowerDiagram.areaVec_apply, bodyCellArea,
    PowerDiagram.bodyCellSet_addConstWeight]

/-- **Equal‑area invariance under a constant weight shift.** Since the area vector is unchanged
(`areaVec_addConstWeight`), the equal‑area property is preserved. -/
theorem IsEqualAreaWeight_addConstWeight
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) (c : ℝ)
    (hw : EMP.IsEqualAreaWeight K s w) :
    EMP.IsEqualAreaWeight K s (EMP.addConstWeight w c) := by
  intro i
  have := congrFun (areaVec_addConstWeight K s w c) i
  rw [IsEqualAreaWeight] at hw
  rw [this]
  exact hw i

end EMP

end NRR
