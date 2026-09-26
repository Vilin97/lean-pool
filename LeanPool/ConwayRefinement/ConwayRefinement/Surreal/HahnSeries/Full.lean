/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalFormMul

import all LeanPool.ConwayRefinement.CombinatorialGames.Surreal.HahnSeries.Basic

/-!
# Conway normal forms in the full Hahn field

The Conway coefficients of a surreal number determine a Hahn series in
`ℝ⟦Surrealᵒᵈ⟧`. The order dual implements LM24's change from Conway's monomial `ω` to
`t = ω⁻¹`: nonnegative Conway exponents become nonpositive Hahn exponents.

This map preserves the full ring structure.
-/

universe u

public noncomputable section

namespace Surreal

/-- The full Hahn series with the Conway coefficients of a surreal number. -/
def toFullHahnSeries (x : Surreal.{u}) : HahnSeries Surrealᵒᵈ ℝ where
  coeff i := x.coeff i.ofDual
  isPWO_support' := by
    rw [Set.isPWO_iff_isWF]
    apply Set.WellFoundedOn.mapsTo (fun i : Surrealᵒᵈ ↦ i.ofDual) _
      x.wellFoundedOn_support
    intro i hi
    rw [mem_support_iff]
    exact hi

/-- Evaluation of the full Conway Hahn series. -/
@[simp]
theorem coeff_toFullHahnSeries (x : Surreal.{u}) (i : Surrealᵒᵈ) :
    x.toFullHahnSeries.coeff i = x.coeff i.ofDual :=
  (rfl)

/-- The support of the full Conway Hahn series is the order dual of the Conway support. -/
theorem mem_support_toFullHahnSeries {x : Surreal.{u}} {i : Surrealᵒᵈ} :
    i ∈ x.toFullHahnSeries.support ↔ i.ofDual ∈ x.support := by
  rw [HahnSeries.mem_support x.toFullHahnSeries i, coeff_toFullHahnSeries,
    mem_support_iff]

/-- The full Conway Hahn-series map sends zero to zero. -/
@[simp]
theorem toFullHahnSeries_zero : (0 : Surreal.{u}).toFullHahnSeries = 0 := by
  ext i
  rw [coeff_toFullHahnSeries, HahnSeries.coeff_zero]
  exact congrFun coeff_zero i.ofDual

/-- The full Conway Hahn-series map preserves addition. -/
@[simp]
theorem toFullHahnSeries_add (x y : Surreal.{u}) :
    (x + y).toFullHahnSeries = x.toFullHahnSeries + y.toFullHahnSeries := by
  ext i
  rw [coeff_toFullHahnSeries, HahnSeries.coeff_add, coeff_toFullHahnSeries,
    coeff_toFullHahnSeries]
  exact congrFun (coeff_add x y) i.ofDual

/-- The full Conway Hahn-series map preserves negation. -/
@[simp]
theorem toFullHahnSeries_neg (x : Surreal.{u}) :
    (-x).toFullHahnSeries = -x.toFullHahnSeries := by
  ext i
  rw [coeff_toFullHahnSeries, HahnSeries.coeff_neg, coeff_toFullHahnSeries]
  exact congrFun (coeff_neg x) i.ofDual

/-- The full Conway Hahn-series map as an additive homomorphism. -/
def toFullHahnSeriesAddMonoidHom :
    Surreal.{u} →+ HahnSeries Surrealᵒᵈ ℝ where
  toFun := toFullHahnSeries
  map_zero' := toFullHahnSeries_zero
  map_add' := toFullHahnSeries_add

/-- Evaluation of the additive full Conway Hahn-series homomorphism. -/
@[simp]
theorem toFullHahnSeriesAddMonoidHom_apply (x : Surreal.{u}) :
    toFullHahnSeriesAddMonoidHom x = x.toFullHahnSeries :=
  (rfl)

/-- The additive full Conway Hahn-series map is injective. -/
theorem toFullHahnSeries_injective :
    Function.Injective (toFullHahnSeries : Surreal.{u} → HahnSeries Surrealᵒᵈ ℝ) := by
  intro x y hxy
  rw [← toHahnSeries_inj]
  apply SurrealHahnSeries.ext
  funext i
  have hcoeff := congrArg (fun q : HahnSeries Surrealᵒᵈ ℝ ↦
    q.coeff (OrderDual.toDual i)) hxy
  simpa only [coeff_toFullHahnSeries, OrderDual.ofDual_toDual,
    coeff_toHahnSeries] using hcoeff

private theorem toFullHahnSeries_eq_ofLex_toHahnSeries (x : Surreal.{u}) :
    x.toFullHahnSeries = ofLex x.toHahnSeries.1 := by
  ext i
  rw [coeff_toFullHahnSeries, ← coeff_toHahnSeries]
  rfl

private theorem ofLex_coe_mul (x y : SurrealHahnSeries.{u}) :
    ofLex (x * y).1 = ofLex x.1 * ofLex y.1 := by
  with_unfolding_all rfl

/-- The full Conway Hahn-series map preserves arbitrary surreal products. -/
@[simp]
theorem toFullHahnSeries_mul (x y : Surreal.{u}) :
    (x * y).toFullHahnSeries = x.toFullHahnSeries * y.toFullHahnSeries := by
  calc
    (x * y).toFullHahnSeries = ofLex (x * y).toHahnSeries.1 :=
      toFullHahnSeries_eq_ofLex_toHahnSeries (x * y)
    _ = ofLex (x.toHahnSeries * y.toHahnSeries).1 := by
      rw [toHahnSeries_mul]
    _ = ofLex x.toHahnSeries.1 * ofLex y.toHahnSeries.1 :=
      ofLex_coe_mul x.toHahnSeries y.toHahnSeries
    _ = x.toFullHahnSeries * y.toFullHahnSeries := by
      rw [← toFullHahnSeries_eq_ofLex_toHahnSeries,
        ← toFullHahnSeries_eq_ofLex_toHahnSeries]

/-- The full Conway Hahn series of a real is concentrated at exponent zero. -/
@[simp]
theorem toFullHahnSeries_realCast (r : ℝ) :
    toFullHahnSeries (r : Surreal.{u}) = HahnSeries.single 0 r := by
  ext i
  rw [coeff_toFullHahnSeries, HahnSeries.coeff_single]
  have hcoeff : (r : Surreal.{u}).coeff = Pi.single 0 r := by
    rw [← coeff_toHahnSeries, toHahnSeries_realCast,
      SurrealHahnSeries.coeff_single]
  rw [hcoeff]
  by_cases hi : i = 0
  · subst i
    simp
  · have hi' : i.ofDual ≠ 0 := by
      exact fun h ↦ hi (by simpa using congrArg OrderDual.toDual h)
    simp [hi, hi']

/-- The full Conway Hahn series of `ω ^ x` is its corresponding monomial. -/
@[simp]
theorem toFullHahnSeries_wpow (x : Surreal.{u}) :
    toFullHahnSeries (ω^ x) = HahnSeries.single (OrderDual.toDual x) 1 := by
  ext i
  rw [coeff_toFullHahnSeries, coeff_wpow, HahnSeries.coeff_single]
  by_cases hi : i = OrderDual.toDual x
  · subst i
    simp
  · have hi' : i.ofDual ≠ x := by
      exact fun h ↦ hi (by simpa using congrArg OrderDual.toDual h)
    simp [hi, hi']

/-- A real scalar times a Conway monomial becomes the corresponding full Hahn monomial. -/
theorem toFullHahnSeries_realCast_mul_wpow (r : ℝ) (i : Surreal.{u}) :
    toFullHahnSeries ((r : Surreal) * ω^ i) =
      HahnSeries.single (OrderDual.toDual i) r := by
  have hcoeff : ((r : Surreal) * ω^ i).coeff = Pi.single i r := by
    rw [← coeff_toHahnSeries]
    have hnormal :
        toHahnSeries ((r : Surreal) * ω^ i) = SurrealHahnSeries.single i r := by
      rw [← SurrealHahnSeries.toSurreal_single i r,
        SurrealHahnSeries.toHahnSeries_toSurreal]
    rw [hnormal, SurrealHahnSeries.coeff_single]
  ext j
  rw [coeff_toFullHahnSeries, hcoeff, HahnSeries.coeff_single]
  by_cases hj : j = OrderDual.toDual i
  · subst j
    simp
  · have hj' : j.ofDual ≠ i := by
      exact fun h ↦ hj (by simpa using congrArg OrderDual.toDual h)
    simp [hj, hj']

/-- A surreal number with finite Conway support is the finite sum of its nonzero Conway
monomials. -/
theorem eq_sum_coeff_mul_wpow_of_support_finite {x : Surreal.{u}}
    (hx : x.support.Finite) :
    x = ∑ i ∈ hx.toFinset, (x.coeff i : Surreal) * ω^ i := by
  apply toFullHahnSeries_injective
  rw [← toFullHahnSeriesAddMonoidHom_apply x,
    ← toFullHahnSeriesAddMonoidHom_apply (∑ i ∈ hx.toFinset,
      (x.coeff i : Surreal) * ω^ i)]
  rw [map_sum]
  simp_rw [toFullHahnSeriesAddMonoidHom_apply,
    toFullHahnSeries_realCast_mul_wpow]
  ext j
  rw [coeff_toFullHahnSeries, HahnSeries.coeff_sum]
  by_cases hj : j.ofDual ∈ x.support
  · rw [Finset.sum_eq_single j.ofDual]
    · simp
    · intro b hb hne
      rw [HahnSeries.coeff_single_of_ne]
      exact fun h ↦ hne (by simpa using (congrArg OrderDual.ofDual h).symm)
    · exact fun hnot ↦ (hnot (hx.mem_toFinset.mpr hj)).elim
  · rw [Finset.sum_eq_zero]
    · exact notMem_support_iff.mp hj
    · intro b hb
      rw [HahnSeries.coeff_single_of_ne]
      exact fun h ↦ hj (by
        have hb' : b ∈ x.support := hx.mem_toFinset.mp hb
        simpa [h] using hb')

/-- The full Conway Hahn-series map preserves the product of two real scalar monomials. -/
theorem toFullHahnSeries_mul_monomials (r s : ℝ) (i j : Surreal.{u}) :
    toFullHahnSeries
        (((r : Surreal) * ω^ i) * ((s : Surreal) * ω^ j)) =
      toFullHahnSeries ((r : Surreal) * ω^ i) *
        toFullHahnSeries ((s : Surreal) * ω^ j) := by
  have hprod :
      ((r : Surreal) * ω^ i) * ((s : Surreal) * ω^ j) =
        ((r * s : ℝ) : Surreal) * ω^ (i + j) := by
    rw [wpow_add, Real.toSurreal_mul]
    ring
  rw [hprod, toFullHahnSeries_realCast_mul_wpow,
    toFullHahnSeries_realCast_mul_wpow,
    toFullHahnSeries_realCast_mul_wpow, HahnSeries.single_mul_single]
  rfl

/-- The full Conway Hahn-series map preserves multiplication when both Conway supports are
finite. -/
theorem toFullHahnSeries_mul_of_support_finite {x y : Surreal.{u}}
    (hx : x.support.Finite) (hy : y.support.Finite) :
    toFullHahnSeries (x * y) = toFullHahnSeries x * toFullHahnSeries y := by
  rw [eq_sum_coeff_mul_wpow_of_support_finite hx,
    eq_sum_coeff_mul_wpow_of_support_finite hy]
  let f (i : Surreal.{u}) := (x.coeff i : Surreal) * ω^ i
  let g (j : Surreal.{u}) := (y.coeff j : Surreal) * ω^ j
  change toFullHahnSeries ((∑ i ∈ hx.toFinset, f i) *
      (∑ j ∈ hy.toFinset, g j)) =
    toFullHahnSeries (∑ i ∈ hx.toFinset, f i) *
      toFullHahnSeries (∑ j ∈ hy.toFinset, g j)
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← toFullHahnSeriesAddMonoidHom_apply, map_sum]
  simp_rw [toFullHahnSeriesAddMonoidHom_apply]
  simp_rw [← toFullHahnSeriesAddMonoidHom_apply,
    map_sum, toFullHahnSeriesAddMonoidHom_apply]
  dsimp only [f, g]
  simp_rw [toFullHahnSeries_mul_monomials]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]

end Surreal
