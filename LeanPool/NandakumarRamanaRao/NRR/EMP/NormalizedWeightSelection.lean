/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightsUniqueness
import LeanPool.NandakumarRamanaRao.NRR.EMP.NormalizedWeights

/-!
# `NRR.EMP.NormalizedWeightSelection` — canonical normalized equal‑area weight

This module proves that normalized equal‑area weights are **unique** (as a `Subsingleton` of
the subtype `EMP.NormalizedEqualAreaWeight`), and then selects a canonical representative,
`EMP.normalizedWeight`, via `Classical.choice` of the existence result from the existing existence theorem.

## Results

* `EMP.normalized_equalArea_weight_subsingleton` — the subtype of normalized equal‑area
 weights is a subsingleton (uniqueness), from the normalized uniqueness theorem
 `EMP.equalArea_weights_unique_normalized`.
* `EMP.normalizedWeight` — the selected canonical normalized equal‑area weight vector,
 `Classical.choice` of `EMP.exists_normalized_equalArea_weight` (the existing existence theorem).
* `EMP.normalizedWeight_isEqualArea` — the selected weight is equal‑area.
* `EMP.normalizedWeight_normalized` — the selected weight is normalized.
* `EMP.normalizedWeight_unique` — any equal‑area normalized weight equals the selected one.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR

variable {n : ℕ}

/-- **Uniqueness of normalized equal‑area weights.** The subtype of weight vectors that are
simultaneously equal‑area and normalized is a subsingleton: any two of its elements are equal.
This packages the normalized uniqueness theorem
`EMP.equalArea_weights_unique_normalized`. The hypothesis `hn : 0 < n` is retained to match
the required public API signature, even though this particular proof does not use it. -/
theorem EMP.normalized_equalArea_weight_subsingleton
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s) :
    Subsingleton (EMP.NormalizedEqualAreaWeight K s) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨wa, hwa, hna⟩ := a
  obtain ⟨wb, hwb, hnb⟩ := b
  exact Subtype.ext (EMP.equalArea_weights_unique_normalized K s hn hs hwa hwb hna hnb)

/-- **Selected normalized equal‑area weight.** A canonical choice of a weight vector that is
both equal‑area for the sites `s` in `K` and normalized (`∑ i, w i = 0`), obtained by
`Classical.choice` from the existence theorem `EMP.exists_normalized_equalArea_weight`
(the existing existence theorem). By `EMP.normalized_equalArea_weight_subsingleton` this choice is in fact unique. -/
noncomputable def EMP.normalizedWeight
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s) : Fin n → ℝ :=
  (Classical.choice (EMP.exists_normalized_equalArea_weight K s hn hs)).val

/-- The selected normalized weight is an equal‑area weight. -/
theorem EMP.normalizedWeight_isEqualArea
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s) :
    EMP.IsEqualAreaWeight K s (EMP.normalizedWeight K s hn hs) :=
  (Classical.choice (EMP.exists_normalized_equalArea_weight K s hn hs)).2.1

/-- The selected normalized weight is normalized (`∑ i, w i = 0`). -/
theorem EMP.normalizedWeight_normalized
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s) :
    EMP.WeightNormalized (EMP.normalizedWeight K s hn hs) :=
  (Classical.choice (EMP.exists_normalized_equalArea_weight K s hn hs)).2.2

/-- **Canonicity.** Any equal‑area normalized weight equals the selected normalized weight,
by the subsingleton property of normalized equal‑area weights. -/
theorem EMP.normalizedWeight_unique
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    {w : Fin n → ℝ}
    (hw : EMP.IsEqualAreaWeight K s w)
    (hnorm : EMP.WeightNormalized w) :
    w = EMP.normalizedWeight K s hn hs :=
  EMP.equalArea_weights_unique_normalized K s hn hs hw
    (EMP.normalizedWeight_isEqualArea K s hn hs) hnorm
    (EMP.normalizedWeight_normalized K s hn hs)

end NRR
