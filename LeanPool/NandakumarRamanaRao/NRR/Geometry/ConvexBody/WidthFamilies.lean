/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthContinuity
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthIdentities
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionParametric
/-!
# `NRR.Geometry.ConvexBody` — width continuity for parameterized families

This module packages the **joint continuity of the width function** for a family of convex
bodies `K : α → ConvexBody E` varying continuously in a parameter `t`. Concretely we introduce

```text
WidthContinuousFamily K : Continuous fun p : α × E => widthFunction (K p.1) p.2
```

the width-function analogue of `SupportFunctionContinuousFamily` from
`SupportFunctionParametric.lean`, and provide the standard closure properties needed by later
partition-cell / perimeter continuity arguments:

* `WidthContinuousFamily.of_support` — a support-function continuous family is width continuous,
* `WidthContinuousFamily.const` — constant families,
* `WidthContinuousFamily.translate` — translation by an arbitrary vector field, and
* `WidthContinuousFamily.scalePos` — positive scaling by a continuous factor.

## Design notes

Everything reduces to the width transformation identities from `WidthIdentities.lean`
(`widthFunction_translate`, `widthFunction_scalePos_body`) and to `SupportFunctionContinuousFamily`
from `SupportFunctionParametric.lean`:

* `of_support` writes `w = h(t, u) + h(t, -u)`, where the second summand is the joint support map
 precomposed with the continuous reparameterisation `(t, u) ↦ (t, -u)`.
* `translate` is immediate: width is translation invariant, so the translated family is the *same*
 function of `(t, u)` as the original width family (`ha` is not needed but is included for a uniform interface).
* `scalePos` uses `widthFunction_scalePos_body` to rewrite the family as `(t, u) ↦ r t · w_{K_t}(u)`
 and takes the product of the (continuous) scalar with the width map.

No structure internals or `sSup` are unfolded here.

## Import policy

`WidthContinuity.lean`, `WidthIdentities.lean` and `SupportFunctionParametric.lean` (all
transitively via `Basic.lean`) already pull in `import Mathlib`, so no extra imports are required.
-/

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {α : Type*} [TopologicalSpace α]

/-- A family of convex bodies `K : α → ConvexBody E` is a *width continuous family* if the map
`(t, u) ↦ w_{K_t}(u)` is (jointly) continuous. This is the width-function analogue of
`SupportFunctionContinuousFamily`. -/
def WidthContinuousFamily (K : α → ConvexBody E) : Prop :=
  Continuous fun p : α × E => widthFunction (K p.1) p.2

/-- **Evaluation.** Unfolding the predicate: joint continuity of `(t, u) ↦ w_{K_t}(u)`. -/
theorem widthFunction_continuous_family_eval
    {K : α → ConvexBody E} (hK : WidthContinuousFamily K) :
    Continuous fun p : α × E => widthFunction (K p.1) p.2 :=
  hK

/-- **From a support-function continuous family.** If `(t, u) ↦ h_{K_t}(u)` is jointly continuous,
then so is `(t, u) ↦ w_{K_t}(u) = h_{K_t}(u) + h_{K_t}(-u)`. -/
theorem WidthContinuousFamily.of_support
    {K : α → ConvexBody E} (hK : SupportFunctionContinuousFamily K) :
    WidthContinuousFamily K := by
  unfold SupportFunctionContinuousFamily at hK
  unfold WidthContinuousFamily
  simp only [widthFunction_def]
  refine hK.add ?_
  exact hK.comp (continuous_fst.prodMk (continuous_neg.comp continuous_snd))

/-- **Constant family.** A constant family is a width continuous family. -/
theorem WidthContinuousFamily.const (K : ConvexBody E) :
    WidthContinuousFamily (fun _ : α => K) :=
  WidthContinuousFamily.of_support (SupportFunctionContinuousFamily.const K)

/-- **Translated family.** Translating a width continuous family by an arbitrary vector field
preserves width continuity, because width is invariant under translations. -/
theorem WidthContinuousFamily.translate
    {K : α → ConvexBody E} (hK : WidthContinuousFamily K)
    (a : α → E) :
    WidthContinuousFamily (fun t => (K t).translate (a t)) := by
  unfold WidthContinuousFamily at hK ⊢
  simpa only [widthFunction_translate] using hK

/-- **Positively scaled family.** Scaling a continuous family by a continuous positive function
keeps it a width continuous family, using `w_{rK}(u) = r · w_K(u)`. -/
theorem WidthContinuousFamily.scalePos
    {K : α → ConvexBody E} (hK : WidthContinuousFamily K)
    (r : α → ℝ) (hr : ∀ t, 0 < r t) (hrc : Continuous r) :
    WidthContinuousFamily (fun t => (K t).scalePos (r t) (hr t)) := by
  unfold WidthContinuousFamily at hK ⊢
  simp only [widthFunction_scalePos_body]
  exact (hrc.comp continuous_fst).mul hK

end ConvexBody

end NRR.Geometry
