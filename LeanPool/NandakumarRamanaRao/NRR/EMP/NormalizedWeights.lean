/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights
import LeanPool.NandakumarRamanaRao.NRR.EMP.WeightShift
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightsExistence
/-!
# `NRR.EMP.NormalizedWeights` — normalized equal‑area power weights and existence

This module defines the **normalized** equal‑area weight subtype together with the
mean‑subtraction normalization operation, and proves that normalized equal‑area weights
exist.

## Definitions

* `EMP.NormalizedEqualAreaWeight K s` — the subtype of weight vectors that are simultaneously
 equal‑area (`EMP.IsEqualAreaWeight`) and normalized (`EMP.WeightNormalized`, i.e.
 `∑ i, w i = 0`).
* `EMP.weightMean w = (∑ i, w i) / n` — the arithmetic mean of a weight vector.
* `EMP.normalizeWeight w = fun i => w i - EMP.weightMean w` — subtract the mean, producing a
 zero‑sum weight vector.

## API

* `EMP.WeightNormalized_normalizeWeight` — mean subtraction produces a normalized weight (needs
 `0 < n`).
* `EMP.IsEqualAreaWeight_normalizeWeight` — mean subtraction preserves the equal‑area property,
 using the constant‑shift invariance `EMP.areaVec_addConstWeight`: subtracting the
 mean is the constant shift by `-(weightMean w)`.
* `EMP.exists_normalized_equalArea_weight` — normalized equal‑area weights exist, combining the
 existence theorem `EMP.exists_equalArea_weights` with the two facts above.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR

variable {n : ℕ}

namespace EMP

/-- **Normalized equal‑area weight.** A weight vector that is both equal‑area for the sites `s`
in `K` and normalized (`∑ i, w i = 0`). -/
def NormalizedEqualAreaWeight
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) :=
  {w : Fin n → ℝ // EMP.IsEqualAreaWeight K s w ∧ EMP.WeightNormalized w}

-- `EMP.weightMean`, `EMP.normalizeWeight`, `EMP.normalizeWeight_apply`, and
-- `EMP.WeightNormalized_normalizeWeight` now live in `NRR.EMP.WeightSpace`
-- (pure algebra of normalized weights) and are re‑exported here via imports.

/-- `normalizeWeight w` is the constant shift of `w` by `-(weightMean w)`. -/
theorem normalizeWeight_eq_addConstWeight (w : Fin n → ℝ) :
    normalizeWeight w = EMP.addConstWeight w (-(EMP.weightMean w)) := by
  funext i
  simp only [normalizeWeight_apply, EMP.addConstWeight_apply]
  ring

end EMP

/-- **Mean subtraction preserves the equal‑area property.** Subtracting the mean is a constant
shift, and the area vector is invariant under constant shifts (`EMP.areaVec_addConstWeight`,
the project). Constant-shift invariance gives the result for every number of sites. -/
theorem EMP.IsEqualAreaWeight_normalizeWeight
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (hw : EMP.IsEqualAreaWeight K s w) :
    EMP.IsEqualAreaWeight K s (EMP.normalizeWeight w) := by
  intro i
  rw [EMP.normalizeWeight_eq_addConstWeight]
  have := congrFun (EMP.areaVec_addConstWeight K s w (-(EMP.weightMean w))) i
  rw [EMP.areaVec_apply] at this ⊢
  rw [this]
  exact hw i

/-- **Existence of normalized equal‑area weights.** For a planar convex body `K`, `n > 0`
pairwise‑distinct sites `s`, there exists a weight vector that is both equal‑area and
normalized. Combines existence (`EMP.exists_equalArea_weights`, the project) with mean
subtraction (constant‑shift invariance, the project). -/
theorem EMP.exists_normalized_equalArea_weight
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s) :
    Nonempty (EMP.NormalizedEqualAreaWeight K s) := by
  obtain ⟨w, hw⟩ := EMP.exists_equalArea_weights K s hn hs
  exact ⟨⟨EMP.normalizeWeight w,
    EMP.IsEqualAreaWeight_normalizeWeight K s w hw,
    EMP.WeightNormalized_normalizeWeight w hn⟩⟩

end NRR
