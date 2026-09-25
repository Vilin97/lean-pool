/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Width
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionContinuity

/-!
# `NRR.Geometry.ConvexBody` — continuity of the width function

This module proves that the **width function** `u ↦ w_K(u) = h_K(u) + h_K(-u)` of a
`ConvexBody` `K` in a real inner product space `E` is continuous in the direction variable,
and gives the quantitative Lipschitz estimate.

## Contents

* `continuous_widthFunction` — full-space continuity of `u ↦ w_K(u)`.
* `continuousAt_widthFunction` — continuity at a point.
* `continuousOn_widthFunction` — continuity on a set.
* `widthFunction_lipschitz_with_radius` — the quantitative estimate
 `|w_K(u) - w_K(v)| ≤ (2 R) · ‖u - v‖` whenever `‖x‖ ≤ R` for all `x ∈ K`.

## Design notes

Everything is built on the support-function continuity and Lipschitz results from
`SupportFunctionContinuity.lean`. Continuity follows since `w_K` is the sum of `h_K` and its
composition with the (continuous) negation map. The Lipschitz estimate applies the support
function estimate to `u, v` and to `-u, -v`, and adds; the two `‖·‖` terms coincide since
`‖(-u) - (-v)‖ = ‖u - v‖`.

## Import policy

`Width.lean` and `SupportFunctionContinuity.lean` (via `Basic.lean`) already pull in
`import Mathlib`, so no extra imports are required here.
-/

@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Full-space continuity** of the width function in the direction variable. -/
theorem continuous_widthFunction
    (K : ConvexBody E) :
    Continuous (fun u : E => widthFunction K u) := by
  simp only [widthFunction_def]
  exact K.continuous_supportFunction.add
    (K.continuous_supportFunction.comp continuous_neg)

/-- **Continuity at a point.** -/
theorem continuousAt_widthFunction
    (K : ConvexBody E) (u : E) :
    ContinuousAt (fun v : E => widthFunction K v) u :=
  K.continuous_widthFunction.continuousAt

/-- **Continuity on a set.** -/
theorem continuousOn_widthFunction
    (K : ConvexBody E) (s : Set E) :
    ContinuousOn (fun u : E => widthFunction K u) s :=
  K.continuous_widthFunction.continuousOn

/-- **Lipschitz estimate.** If every point of `K` has norm at most `R`, the width function
satisfies `|w_K(u) - w_K(v)| ≤ (2 R) · ‖u - v‖`. -/
theorem widthFunction_lipschitz_with_radius
    (K : ConvexBody E) {R : ℝ}
    (hR : ∀ x ∈ (K : Set E), ‖x‖ ≤ R) :
    ∀ u v : E,
      |widthFunction K u - widthFunction K v| ≤ (2 * R) * ‖u - v‖ := by
  intro u v
  have h1 : |supportFunction K u - supportFunction K v| ≤ R * ‖u - v‖ :=
    K.supportFunction_lipschitz_with_radius hR u v
  have h2 : |supportFunction K (-u) - supportFunction K (-v)| ≤ R * ‖(-u) - (-v)‖ :=
    K.supportFunction_lipschitz_with_radius hR (-u) (-v)
  have hnorm : ‖(-u) - (-v)‖ = ‖u - v‖ := by
    rw [show (-u) - (-v) = -(u - v) from by abel, norm_neg]
  rw [hnorm] at h2
  have hsum :
      |widthFunction K u - widthFunction K v|
        ≤ |supportFunction K u - supportFunction K v|
          + |supportFunction K (-u) - supportFunction K (-v)| := by
    simp only [widthFunction_def]
    calc |supportFunction K u + supportFunction K (-u)
            - (supportFunction K v + supportFunction K (-v))|
        = |(supportFunction K u - supportFunction K v)
            + (supportFunction K (-u) - supportFunction K (-v))| := by ring_nf
      _ ≤ |supportFunction K u - supportFunction K v|
            + |supportFunction K (-u) - supportFunction K (-v)| := abs_add_le _ _
  calc |widthFunction K u - widthFunction K v|
      ≤ |supportFunction K u - supportFunction K v|
        + |supportFunction K (-u) - supportFunction K (-v)| := hsum
    _ ≤ R * ‖u - v‖ + R * ‖u - v‖ := add_le_add h1 h2
    _ = (2 * R) * ‖u - v‖ := by ring

end ConvexBody

end NRR.Geometry
