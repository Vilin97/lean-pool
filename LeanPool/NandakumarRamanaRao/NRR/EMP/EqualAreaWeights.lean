/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellAreaVector
import LeanPool.NandakumarRamanaRao.NRR.EMP.WeightSpace

/-!
# `NRR.EMP.EqualAreaWeights` — equal‑area power weights (definitions and API)

This module packages the **equal‑area weight** vocabulary for the equal‑measure‑partition
(EMP) development, on top of the fixed‑site restricted power‑cell area vector
`NRR.PowerDiagram.areaVec`.

## Definitions

* `EMP.areaVec K s w : Fin n → ℝ` — the area vector, a thin alias of
 `PowerDiagram.areaVec K s w`.
* `EMP.IsEqualAreaWeight K s w` — the predicate that every restricted power cell carries
 exactly the average area `K.area / n`. Here `n : ℕ` is coerced to `ℝ` via `Nat.cast`
 (`K.area / (n : ℝ)`).
* `EMP.WeightNormalized w` — the affine normalization `∑ i, w i = 0` (used to pin down the
 additive‑constant freedom in the weights).

## Easy API (proved here)

* `continuous_EMP_areaVec_weights` — with sites fixed and pairwise distinct, the map
 `w ↦ EMP.areaVec K s w` is continuous.
* `sum_EMP_areaVec_eq_area` — with distinct sites and at least one site, the components of
 the area vector sum to `K.area`.

## Necessary nondegeneracy hypotheses

Both easy theorems require `hs : Function.Injective s` (distinct sites); continuity is
genuinely false when two sites coincide, and the total‑mass identity needs the null‑overlap
of distinct cells. The total‑mass identity additionally needs `[NeZero n]` (at least one
site): with no sites the empty sum is `0` while a convex body has positive area. See the
docstring of `NRR.PowerDiagram.CellAreaVector` for details.

## Existence and uniqueness

The following signatures describe the existence and uniqueness theorems proved in the dedicated
EMP modules.

```
theorem EMP.exists_equalArea_weights
 (K : ConvexBody Plane) (s : Fin n → Plane)
 (hn : 0 < n) (hs : Function.Injective s) :
 ∃ w : Fin n → ℝ, EMP.IsEqualAreaWeight K s w

theorem EMP.equalArea_weights_unique
 (K : ConvexBody Plane) (s : Fin n → Plane)
 (hs : Function.Injective s)
 {w w' : Fin n → ℝ}
 (hw : EMP.IsEqualAreaWeight K s w)
 (hw' : EMP.IsEqualAreaWeight K s w') :
 ∃ c : ℝ, ∀ i, w' i = w i + c
```
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR

variable {n : ℕ}

namespace EMP

/-- **Equal‑area (power‑cell) area vector.** A thin alias of the fixed‑site restricted
power‑cell area vector `PowerDiagram.areaVec K s w`. -/
noncomputable def areaVec
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) : Fin n → ℝ :=
  NRR.PowerDiagram.areaVec K s w

/-- The `i`‑th component of `EMP.areaVec` is the restricted power‑cell area. -/
@[simp] theorem areaVec_apply
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) (i : Fin n) :
    areaVec K s w i = NRR.PowerDiagram.areaVec K s w i := rfl

/-- **Equal‑area weight.** The weights `w` are *equal‑area* for the sites `s` in `K` if every
restricted power cell has exactly the average area `K.area / n`. The count `n : ℕ` is coerced
to `ℝ` via `Nat.cast`. -/
def IsEqualAreaWeight
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) : Prop :=
  ∀ i, areaVec K s w i = K.area / (n : ℝ)

-- `EMP.WeightNormalized` now lives in `NRR.EMP.WeightSpace` (pure algebra of
-- normalized weights) and is re‑exported here via the import above.

end EMP

/-- **Fixed‑site weight‑continuity of the equal‑area area vector.** With sites `s` fixed and
pairwise distinct (`hs`), the vector‑valued map `w ↦ EMP.areaVec K s w` is continuous in the
weights. The injectivity hypothesis is necessary (see the module docstring). -/
theorem continuous_EMP_areaVec_weights
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (hs : Function.Injective s) :
    Continuous fun w : Fin n → ℝ => EMP.areaVec K s w :=
  NRR.PowerDiagram.continuous_areaVec_weights K s hs

/-- **Total mass of the equal‑area area vector.** For distinct sites (`hs`) and at least one
site (`[NeZero n]`), the areas of the restricted power cells sum to the body area `K.area`. -/
theorem sum_EMP_areaVec_eq_area [NeZero n]
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (hs : Function.Injective s) :
    ∑ i, EMP.areaVec K s w i = K.area :=
  NRR.PowerDiagram.sum_areaVec_eq_area K s w hs

end NRR
