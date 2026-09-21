/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-5.6 Sol
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Pointwise star on `Lᵖ`

Mathlib equips `Lp R p μ` with pointwise `Star` and `InvolutiveStar` instances when the value
space has an isometric additive star, and provides `Lp.coeFn_star` for representatives.  It does
not currently install the corresponding additive or isometric star structures on `Lp` itself.
This module records the reusable consequences needed by conjugation-equivariant spectral models:
star preserves subtraction and the `Lᵖ` norm, hence is an isometry and is continuous whenever
`p ≥ 1` gives `Lp` its normed topological structure.

The algebraic and norm identities are valid for every exponent.  Only the isometry/continuity
layer carries `[Fact (1 ≤ p)]`, matching Mathlib's normed-topological `Lp` structure.

## Main results

* `TauCeti.coeFn_star_lp`: `star F` is represented by the pointwise star of a representative.
* `TauCeti.norm_star_lp`: pointwise star preserves the `Lᵖ` norm.
* `TauCeti.star_sub_lp`: pointwise star preserves subtraction on `Lᵖ`.
* `TauCeti.isometry_star_lp`: for `p ≥ 1`, pointwise star is an isometry of `Lᵖ`.
* `TauCeti.continuous_star_lp`: for `p ≥ 1`, pointwise star is continuous on `Lᵖ`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Source module: `DavisKahan/SpectralTheory/Real/RealCyclicDecomposition.lean`.
* Source declarations: `coeFn_star_lp`, `norm_star_lp`, `star_sub_lp`, `isometry_star_lp`,
  `continuous_star_lp`.
* Extraction class: **generalized during extraction** from `Lp ℂ 2 μ` to `Lp R p μ`.
* Semantic change: none for the original complex `L²` specialization; the promoted statements
  expose the value-type and exponent generality already present in the representative proofs.
* Spectra influence: **none** -- the implementation uses only Mathlib's `Lp` API.
-/

public section

open MeasureTheory

namespace TauCeti

variable {α R : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]
variable {μ : Measure α} {p : ENNReal}

/-- The `Lᵖ` class of `star F` is represented by the pointwise star of a representative of `F`. -/
theorem coeFn_star_lp (F : Lp R p μ) :
    ∀ᵐ x ∂μ, (star F : Lp R p μ) x = star ((F : Lp R p μ) x) :=
  Lp.coeFn_star F

/-- Pointwise star preserves the `Lᵖ` norm. -/
theorem norm_star_lp (F : Lp R p μ) : ‖star F‖ = ‖F‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [coeFn_star_lp F] with x hx
  rw [hx, norm_star]

/-- Pointwise star preserves subtraction on `Lᵖ`.

Mathlib gives `Lp` the pointwise `Star` operation but not a `StarAddMonoid` instance, so this law
is recorded explicitly at the `Lp` level. -/
theorem star_sub_lp (F G : Lp R p μ) : star (F - G) = star F - star G := by
  refine Lp.ext ?_
  filter_upwards [coeFn_star_lp (F - G), Lp.coeFn_sub F G,
    Lp.coeFn_sub (star F) (star G), coeFn_star_lp F, coeFn_star_lp G] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3]
  simp only [Pi.sub_apply, h4, h5, star_sub]

section Normed

variable [Fact (1 ≤ p)]

/-- Pointwise star is an isometry of `Lᵖ` for `p ≥ 1`. -/
theorem isometry_star_lp : Isometry (star : Lp R p μ → Lp R p μ) :=
  Isometry.of_dist_eq fun F G => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub_lp, norm_star_lp]

/-- Pointwise star is continuous on `Lᵖ` for `p ≥ 1`. -/
theorem continuous_star_lp : Continuous (star : Lp R p μ → Lp R p μ) :=
  isometry_star_lp.continuous

end Normed

end TauCeti
