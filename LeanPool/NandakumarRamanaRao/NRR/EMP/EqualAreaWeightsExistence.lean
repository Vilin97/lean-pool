/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights
import LeanPool.NandakumarRamanaRao.NRR.EMP.OptimalTransportCore

/-!
# `NRR.EMP.EqualAreaWeightsExistence` — existence of equal‑area power weights

This module records the **derived existence theorem** for equal‑area power weights, obtained
from the single isolated optimal‑transport core theorem
`NRR.EMP.powerDiagram_equalArea_weights_exists_core`
(in `NRR/EMP/OptimalTransportCore.lean`).

## Result

```
theorem EMP.exists_equalArea_weights
 (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
 (hn : 0 < n) (hs : Function.Injective s) :
 ∃ w : Fin n → ℝ, EMP.IsEqualAreaWeight K s w
```

For a planar convex body `K`, `n > 0` pairwise‑distinct sites `s`, there exist additive
weights `w` whose restricted power cells all have equal area `K.area / n`.

The proof is a direct application of the core theorem: the whole mathematical content lives in
the isolated dependency, and this module only re‑exports it under the public name required by
the equal‑area‑partition development. No new hypotheses are introduced — the signature matches
the core theorem exactly, and the nondegeneracy hypotheses (`hn`, `hs`) are the minimal ones
justified in `OptimalTransportCore`.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR

variable {n : ℕ}

/-- **Existence of equal‑area power weights.** For a planar convex body `K`, `n > 0`
pairwise‑distinct sites `s`, there exist additive weights `w : Fin n → ℝ` whose restricted
power cells all carry the average area `K.area / n`, i.e. `EMP.IsEqualAreaWeight K s w`.

Derived directly from the isolated optimal‑transport core theorem
`EMP.powerDiagram_equalArea_weights_exists_core`. -/
theorem EMP.exists_equalArea_weights
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s) :
    ∃ w : Fin n → ℝ, EMP.IsEqualAreaWeight K s w :=
  EMP.powerDiagram_equalArea_weights_exists_core K s hn hs

end NRR
