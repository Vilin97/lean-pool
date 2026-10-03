/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


/-
Copyright (c) 2026. All rights reserved.
-/
public import LeanPool.CoarseGraining.Homogenization.Probability.EfronStein.TwoPoint
public import LeanPool.CoarseGraining.Homogenization.Probability.EfronStein.ProdDecomp
public import LeanPool.CoarseGraining.Homogenization.Probability.EfronStein.Fin

/-!
# Efron–Stein inequality on finite products

Facade module gathering the bounded-observable Efron–Stein inequality on a finite
product probability space.  The public entry point is

* `Homogenization.efronStein_pi`: for a bounded measurable `F` on `∀ i, Ω i`
  with independent coordinates `μ i`,
  `Var[F; Measure.pi μ] ≤ ½ ∑ i, ∫ x ∫ y (F (update x i y) − F x)² dμᵢ dπ`.

Supporting public lemmas:

* `Homogenization.variance_eq_half_integral_sub_sq` — two-point variance identity;
* `Homogenization.variance_prod_eq` — two-factor (law-of-total-variance) split;
* `Homogenization.efronStein_fin` — the `Fin n` version proved by induction.
-/

@[expose] public section
