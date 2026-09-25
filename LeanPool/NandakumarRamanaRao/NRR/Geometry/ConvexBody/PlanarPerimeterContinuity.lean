/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeter
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterTransform
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthFamilies

/-!
# `NRR.Geometry.ConvexBody` — continuity of the planar perimeter

This module proves a **deterministic continuity theorem** for the planar (Cauchy) perimeter
`planarPerimeter` of a parameterized family of convex bodies `K : α → ConvexBody Plane`.

Since

```text
planarPerimeter (K a) = (1 / 2) * ∫ θ in 0..2π, w_{K a}(circleVec θ),
```

perimeter continuity reduces to continuity of a parameterized interval integral. The decisive
Mathlib result is `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`:
if the uncurried integrand `(a, θ) ↦ f a θ` is (jointly) continuous, then
`a ↦ ∫ θ in a₀..b₀, f a θ` is continuous, for **any** topological parameter space `α`
(the measure `volume` has no atoms and is locally finite). No metric or first-countability
assumption on `α` is required, so the fully general `continuous_planarPerimeter_of_angleWidth`
holds and the metric fallback is unnecessary.

## The angle-width predicate

The hypothesis is packaged as the minimal predicate

```text
AngleWidthContinuousFamily K : Continuous fun p : α × ℝ => w_{K p.1}(circleVec p.2),
```

which is exactly joint continuity of the uncurried perimeter integrand. It is implied by the
stronger `WidthContinuousFamily` from `WidthFamilies.lean` (precompose with the continuous
reparameterisation `(a, θ) ↦ (a, circleVec θ)`), and holds for constant families.

## Design notes

* `continuous_planarPerimeter_of_angleWidth` wraps the Mathlib parametric-integral theorem and
 multiplies by the constant `1 / 2` (`continuous_const.mul`).
* The translation / scaling corollaries reduce to the *pointwise* transformation laws
 `planarPerimeter_translate` and `planarPerimeter_scalePos` from `PlanarPerimeterTransform.lean`,
 so the translation corollary needs no continuity of the vector field (perimeter is
 translation invariant).

## Import policy

`PlanarPerimeter.lean`, `PlanarPerimeterTransform.lean` and `WidthFamilies.lean` each transitively
pull in `import Mathlib`, so no extra imports are required.
-/

@[expose] public section

namespace NRR.Geometry

open Real MeasureTheory _root_.NRR.Geometry.ConvexBody

variable {α : Type*} [TopologicalSpace α]

/-- A family of convex bodies `K : α → ConvexBody Plane` has a **continuous angle-width
integrand** if the uncurried Cauchy perimeter integrand `(a, θ) ↦ w_{K a}(circleVec θ)` is
(jointly) continuous on `α × ℝ`. This is the minimal hypothesis needed for perimeter continuity. -/
def AngleWidthContinuousFamily (K : α → ConvexBody Plane) : Prop :=
  Continuous fun p : α × ℝ => widthFunction (K p.1) (circleVec p.2)

/-- **Evaluation.** Unfolding the predicate: joint continuity of `(a, θ) ↦ w_{K a}(circleVec θ)`. -/
theorem angleWidthContinuousFamily_eval
    {K : α → ConvexBody Plane} (hK : AngleWidthContinuousFamily K) :
    Continuous fun p : α × ℝ => widthFunction (K p.1) (circleVec p.2) :=
  hK

/-- **Constant family.** A constant family has a continuous angle-width integrand. -/
theorem AngleWidthContinuousFamily.const (K : ConvexBody Plane) :
    AngleWidthContinuousFamily (fun _ : α => K) :=
  (K.continuous_widthFunction.comp continuous_circleVec).comp continuous_snd

/-- **From a width-continuous family.** If `(a, u) ↦ w_{K a}(u)` is jointly continuous, then so is
its restriction to the angle parameterization `(a, θ) ↦ w_{K a}(circleVec θ)`. -/
theorem AngleWidthContinuousFamily.of_widthFamily
    {K : α → ConvexBody Plane} (hK : WidthContinuousFamily K) :
    AngleWidthContinuousFamily K :=
  hK.comp (continuous_fst.prodMk (continuous_circleVec.comp continuous_snd))

/-- **Main theorem.** If a family of convex bodies has a continuous angle-width integrand, then
its planar (Cauchy) perimeter is continuous in the parameter. This holds for an arbitrary
topological parameter space `α`; no metric/first-countability assumption is needed. -/
theorem continuous_planarPerimeter_of_angleWidth
    (K : α → ConvexBody Plane) (hK : AngleWidthContinuousFamily K) :
    Continuous fun a : α => planarPerimeter (K a) := by
  simp only [planarPerimeter_def]
  have h : Continuous (Function.uncurry fun a θ => widthFunction (K a) (circleVec θ)) := hK
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      h 0 (2 * Real.pi))

/-- **Translation corollary.** Translating each body by a (not necessarily continuous) vector field
preserves perimeter continuity, since the planar perimeter is translation invariant. -/
theorem continuous_planarPerimeter_translate_family
    (K : α → ConvexBody Plane)
    (hK : Continuous fun a => planarPerimeter (K a))
    (v : α → Plane) :
    Continuous fun a => planarPerimeter ((K a).translate (v a)) := by
  simpa only [planarPerimeter_translate] using hK

/-- **Positive scaling corollary.** Scaling each body by a continuous positive factor preserves
perimeter continuity, using `planarPerimeter (rK) = r · planarPerimeter K`. -/
theorem continuous_planarPerimeter_scalePos_family
    (K : α → ConvexBody Plane)
    (hK : Continuous fun a => planarPerimeter (K a))
    (r : α → ℝ) (hr : ∀ a, 0 < r a) (hrc : Continuous r) :
    Continuous fun a => planarPerimeter ((K a).scalePos (r a) (hr a)) := by
  simp_rw [planarPerimeter_scalePos]
  exact hrc.mul hK

end NRR.Geometry
