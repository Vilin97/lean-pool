/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights

/-!
# `NRR.EMP.AreaVectorTarget` — area vector into the fixed total‑mass hyperplane

This module packages the equal‑area area vector `EMP.areaVec K s w` relative to the fixed
total mass `K.area`, phrasing the equal‑area problem as **finding zeroes of a continuous
finite‑dimensional deviation map**.

## Definitions

* `EMP.equalAreaTarget K n : Fin n → ℝ` — the constant target vector `fun _ => K.area / n`,
 whose components sum to `K.area` (for `n > 0`).
* `EMP.areaDeviation K s w : Fin n → ℝ` — the deviation `EMP.areaVec K s w - equalAreaTarget`,
 which lies in the zero‑sum hyperplane for distinct sites.

## API

* `sum_equalAreaTarget` — the target components sum to `K.area`.
* `sum_areaDeviation_eq_zero` — the deviation is zero‑sum (distinct sites, at least one site).
* `continuous_areaDeviation_weights` — with distinct fixed sites, `w ↦ areaDeviation K s w`
 is continuous in the weights.

## Necessary nondegeneracy hypotheses

* `sum_equalAreaTarget` needs `hn : 0 < n` (an empty sum is `0`, not `K.area`).
* `sum_areaDeviation_eq_zero` needs `hn : 0 < n` and `hs : Function.Injective s` — the
 total‑mass identity `sum_EMP_areaVec_eq_area` uses the almost‑disjoint covering of `K` by
 the restricted cells, which requires distinct sites (and at least one site).
* `continuous_areaDeviation_weights` needs `hs : Function.Injective s`: it reduces to the
 continuity of `EMP.areaVec` (a constant target is continuous), which is genuinely false
 when two sites coincide (see `NRR.PowerDiagram.CellAreaVector`). The signature in
 the design omitted `hs`; it is added here because the statement is false without it.

No existence of equal‑area weights and no topological‑degree/obstruction argument is used or
proved here.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR

variable {n : ℕ}

namespace EMP

/-- **Target equal‑area vector.** The constant vector whose every component is the average
area `K.area / n`. -/
noncomputable def equalAreaTarget
    (K : Geometry.ConvexBody Plane) (n : ℕ) : Fin n → ℝ :=
  fun _ => K.area / n

/-- **Zero‑sum deviation map.** The difference between the area vector and the equal‑area
target; for distinct sites its components sum to zero. -/
noncomputable def areaDeviation
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => EMP.areaVec K s w i - EMP.equalAreaTarget K n i

@[simp] theorem equalAreaTarget_apply
    (K : Geometry.ConvexBody Plane) (n : ℕ) (i : Fin n) :
    equalAreaTarget K n i = K.area / n := rfl

@[simp] theorem areaDeviation_apply
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) (i : Fin n) :
    areaDeviation K s w i = EMP.areaVec K s w i - EMP.equalAreaTarget K n i := rfl

/-- **Total mass of the target vector.** The equal‑area target components sum to `K.area`. -/
theorem sum_equalAreaTarget
    (K : Geometry.ConvexBody Plane) (hn : 0 < n) :
    ∑ i : Fin n, EMP.equalAreaTarget K n i = K.area := by
  simp +decide [ EMP.equalAreaTarget, mul_div_cancel₀, hn.ne' ]

/-- **Zero‑sum deviation.** With distinct sites and at least one site, the deviation vector
has zero total mass. -/
theorem sum_areaDeviation_eq_zero
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (hn : 0 < n) (hs : Function.Injective s) :
    ∑ i, EMP.areaDeviation K s w i = 0 := by
  -- Expand the definition of `EMP.areaDeviation`.
  -- Then use `Finset.sum_sub_distrib` to split the sum into two separate sums.
  unfold EMP.areaDeviation
  rw [Finset.sum_sub_distrib];
  convert sub_eq_zero.mpr ( sum_EMP_areaVec_eq_area K s w hs ) using 1;
  · rw [ sum_equalAreaTarget K hn ];
  · exact ⟨ hn.ne' ⟩

/-- **Fixed‑site weight‑continuity of the deviation map.** With sites `s` fixed and pairwise
distinct (`hs`), the map `w ↦ EMP.areaDeviation K s w` is continuous in the weights. -/
theorem continuous_areaDeviation_weights
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (hs : Function.Injective s) :
    Continuous fun w : Fin n → ℝ => EMP.areaDeviation K s w := by
  exact (continuous_EMP_areaVec_weights K s hs).sub continuous_const

end EMP

end NRR
