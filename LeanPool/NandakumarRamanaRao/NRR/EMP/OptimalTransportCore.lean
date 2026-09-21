/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeights
import LeanPool.NandakumarRamanaRao.NRR.EMP.NormalizedAreaDeviation
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightCoercivity
import LeanPool.NandakumarRamanaRao.NRR.Topology.OutwardFieldZero

/-!
# `NRR.EMP.OptimalTransportCore` — the isolated optimal‑transport core

This module isolates the **single external mathematical dependency** needed to obtain
equal‑area power weights for a planar convex body: the existence of weights that make every
restricted power cell carry the average area `K.area / n`.

## The core theorem

```
theorem EMP.powerDiagram_equalArea_weights_exists_core
 (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
 (hn : 0 < n) (hs : Function.Injective s) :
 ∃ w : Fin n → ℝ, EMP.IsEqualAreaWeight K s w
```

This is the classical **Aurenhammer–Hoffmann–Aronov** (power / Laguerre diagram) existence
result, equivalently the semi‑discrete **optimal‑transport** existence theorem specialized to
the plane with fixed distinct sites and uniform (equal‑area) target masses: for a convex body
`K` of positive area and `n` pairwise‑distinct sites there exist additive weights `w` whose
Laguerre (power) cells restricted to `K` all have equal area `K.area / n`.

### Standard proof (convex‑optimization route)

The result is the first‑order optimality condition for a concave, coercive‑modulo‑constants
energy on the zero‑sum weight hyperplane `{w : ∑ i, w i = 0}`:

1. The map `w ↦ ∑ i, w i · (target_i)` minus the total power‑cell "potential" is concave and
 coercive modulo the additive‑constant direction (adding a constant to all weights does not
 change the power diagram; cf. `NRR.EMP.WeightShift`).
2. Hence it attains a maximum on the zero‑sum hyperplane (Weierstrass on a compact sublevel
 set / coercivity).
3. The gradient of this energy is exactly the vector of cell‑area deviations
 `EMP.areaDeviation K s w`, which is continuous (`continuous_areaDeviation_weights`)
 and zero‑sum (`sum_areaDeviation_eq_zero`).
4. At the maximizer the gradient (projected onto the zero‑sum hyperplane) vanishes, i.e. every
 cell area equals the common target `K.area / n`. That is `EMP.IsEqualAreaWeight K s w`.

The formal proof below uses the continuous area-deviation map, the coercivity estimate, and the
outward-field zero theorem. It is consumed by `NRR.EMP.exists_equalArea_weights` in
`NRR/EMP/EqualAreaWeightsExistence.lean`.

## Necessary nondegeneracy hypotheses

* `hn : 0 < n` — with no sites the target `K.area / n` is not defined meaningfully and the
 statement is vacuous/false for a positive‑area body.
* `hs : Function.Injective s` — the restricted power cells only tile `K` almost disjointly
 when the sites are pairwise distinct; coincident sites break the area bookkeeping. This is
 the same distinct‑site hypothesis carried by `sum_EMP_areaVec_eq_area` and
 `continuous_EMP_areaVec_weights`.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR

variable {n : ℕ}

/--
Core semi-discrete optimal transport theorem:
for an injective finite site configuration in a positive-area planar convex body,
there are power weights whose restricted power cells have equal area.
This theorem is the core existence result used by the equal-area weight API.
-/
theorem EMP.powerDiagram_equalArea_weights_exists_core
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s) :
    ∃ w : Fin n → ℝ, EMP.IsEqualAreaWeight K s w := by
  by_cases hn1 : n = 1
  · subst n
    letI : NeZero 1 := ⟨by omega⟩
    refine ⟨fun _ => 0, ?_⟩
    intro i
    fin_cases i
    have hsum := NRR.sum_EMP_areaVec_eq_area K s (fun _ => 0) hs
    simpa [EMP.IsEqualAreaWeight] using hsum
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hd : 1 ≤ d := by omega
    let R := EMP.equalAreaOutwardRadius K s (by omega : 0 < d + 1)
    let F : EuclideanSpace Real (Fin (d + 1)) →
        EuclideanSpace Real (Fin (d + 1)) := fun x =>
      EMP.augmentedAreaDeviation K s (by omega) hs (R • x)
    have hF : Continuous F := by
      have hscale : Continuous (fun x : EuclideanSpace Real (Fin (d + 1)) => R • x) :=
        by fun_prop
      exact (EMP.continuous_augmentedAreaDeviation K s (by omega) hs).comp
        hscale
    have hout : ∀ x : EuclideanSpace Real (Fin (d + 1)), ‖x‖ = 1 →
        0 < inner Real x (F x) := by
      intro x hx
      exact EMP.augmentedAreaDeviation_outward_on_radius K s (by omega) hs x hx
    obtain ⟨x, _hxball, hxzero⟩ :=
      NRR.Topology.exists_zero_closedBall_of_inner_pos_on_sphere hd F hF hout
    refine ⟨EMP.normalizeWeight (fun i => (R • x) i), ?_⟩
    apply EMP.augmentedAreaDeviation_zero_gives_equalArea K s (by omega) hs (R • x)
    simpa [F] using hxzero


end NRR
