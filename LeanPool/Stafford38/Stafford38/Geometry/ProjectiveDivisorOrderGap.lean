/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.FormalDivisorAxisLift
public import Mathlib.RingTheory.PowerSeries.Inverse


/-!
# The strict projective order gap at a divisor

This file formalizes the first valuation-theoretic implication in the
normalization-at-infinity argument.  Let `q₀` be the projective denominator
and let `r = q₁ / q₀` be the distinguished affine coordinate in the local
ring at a prime divisor.  If both `q₀` and `r` vanish at the divisor, then a
uniformizer `ϖ` gives

`q₀ = ϖ^a u₀`, `q₁ = ϖ^b u₁`, and `0 < a < b`.

The power-series specialization feeds this strict order gap directly into
`FormalDivisorAxisLift`.  Thus its caller no longer has to supply the
integers `a,b`, their factorizations, or the inequality `a < b`.

This does not construct the projective closure, its normalization, or the
prime divisor.  Those global existence statements are not presently
available in Mathlib's algebraic-geometry library.
-/

@[expose] public section

namespace Stafford38.Geometry.ProjectiveDivisorOrderGap

open IsLocalRing
open Stafford38.GeometryFormalDivisorAxisLift
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryPowerSeriesTangentLimit
open Stafford38.GeometryRetractionSpecialization
open Stafford38.GeometrySplitTangentMatrix

noncomputable section

universe u v w

/-! ## The DVR order calculation -/

/-- At a prime divisor, a nonzero projective denominator and a nonzero affine
coordinate which both vanish have strictly separated orders after
rehomogenization.

The equation `q₁ = q₀ * ratio` is the local-ring form of
`ratio = X₁ / X₀`; unlike division in the fraction field, it retains the
integrality needed by the formal-divisor consumer. -/
theorem exists_uniformizer_strict_orderGap
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (uniformizer : R) (huniformizer : Irreducible uniformizer)
    (q₀ ratio q₁ : R)
    (hq₀_ne : q₀ ≠ 0) (hratio_ne : ratio ≠ 0)
    (hq₀_vanish : q₀ ∈ maximalIdeal R)
    (hratio_vanish : ratio ∈ maximalIdeal R)
    (hq₁ : q₁ = q₀ * ratio) :
    ∃ (a r b : ℕ) (u₀ ur u₁ : Rˣ),
      0 < a ∧ 0 < r ∧ b = a + r ∧ a < b ∧
      q₀ = (u₀ : R) * uniformizer ^ a ∧
      ratio = (ur : R) * uniformizer ^ r ∧
      u₁ = u₀ * ur ∧
      q₁ = (u₁ : R) * uniformizer ^ b := by
  obtain ⟨a, u₀, hq₀⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq₀_ne huniformizer
  obtain ⟨r, ur, hratio⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hratio_ne huniformizer
  have hq₀_nonunit : ¬IsUnit q₀ := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hq₀_vanish
  have hratio_nonunit : ¬IsUnit ratio := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hratio_vanish
  have ha : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro ha0
    apply hq₀_nonunit
    rw [hq₀, ha0, pow_zero, mul_one]
    exact u₀.isUnit
  have hr : 0 < r := by
    apply Nat.pos_of_ne_zero
    intro hr0
    apply hratio_nonunit
    rw [hratio, hr0, pow_zero, mul_one]
    exact ur.isUnit
  let b := a + r
  let u₁ := u₀ * ur
  refine ⟨a, r, b, u₀, ur, u₁, ha, hr, rfl, ?_, hq₀, hratio, rfl, ?_⟩
  · simp only [b]
    omega
  · rw [hq₁, hq₀, hratio]
    simp only [b, u₁, Units.val_mul, pow_add]
    ring

/-! ## The completed local power-series form -/

/-- The DVR implication above specialized to the completed divisor chart.
Vanishing is expressed by zero constant coefficient.  The output is exactly
the pair of factorizations and strict inequality consumed by
`exists_formalDivisorAxisLift`. -/
theorem exists_powerSeries_strict_projectiveOrderGap
    {k : Type u} [Field k]
    (q₀ ratio q₁ : PowerSeries k)
    (hq₀_ne : q₀ ≠ 0) (hratio_ne : ratio ≠ 0)
    (hq₀_vanish : PowerSeries.constantCoeff q₀ = 0)
    (hratio_vanish : PowerSeries.constantCoeff ratio = 0)
    (hq₁ : q₁ = q₀ * ratio) :
    ∃ (a b : ℕ) (u₀ u₁ : PowerSeries k),
      0 < a ∧ a < b ∧
      q₀ = (PowerSeries.X : PowerSeries k) ^ a * u₀ ∧
      PowerSeries.constantCoeff u₀ ≠ 0 ∧
      q₁ = (PowerSeries.X : PowerSeries k) ^ b * u₁ ∧
      PowerSeries.constantCoeff u₁ ≠ 0 := by
  have hq₀_mem : q₀ ∈ IsLocalRing.maximalIdeal (PowerSeries k) := by
    rw [← PowerSeries.ker_coeff_eq_max_ideal]
    exact hq₀_vanish
  have hratio_mem : ratio ∈ IsLocalRing.maximalIdeal (PowerSeries k) := by
    rw [← PowerSeries.ker_coeff_eq_max_ideal]
    exact hratio_vanish
  obtain ⟨a, r, b, u₀, ur, u₁, ha, hr, hb, hab,
      hq₀_factor, hratio_factor, hu₁, hq₁_factor⟩ :=
    exists_uniformizer_strict_orderGap
      (PowerSeries.X : PowerSeries k) PowerSeries.X_irreducible
      q₀ ratio q₁ hq₀_ne hratio_ne hq₀_mem hratio_mem hq₁
  have hu₀_const : PowerSeries.constantCoeff (u₀ : PowerSeries k) ≠ 0 := by
    exact (PowerSeries.isUnit_iff_constantCoeff.mp u₀.isUnit).ne_zero
  have hu₁_const : PowerSeries.constantCoeff (u₁ : PowerSeries k) ≠ 0 := by
    exact (PowerSeries.isUnit_iff_constantCoeff.mp u₁.isUnit).ne_zero
  refine ⟨a, b, (u₀ : PowerSeries k), (u₁ : PowerSeries k),
    ha, hab, ?_, hu₀_const, ?_, hu₁_const⟩
  · simpa [mul_comm] using hq₀_factor
  · simpa [mul_comm] using hq₁_factor

/-! ## Direct handoff to the formal tangent producer -/

/-- A completed projective-divisor chart with vanishing denominator and
vanishing affine ratio produces the exact formal tangent annihilator whose
residue is the distinguished projective axis.

The tangent divisibility assumptions are coordinate-free order statements:
divisor-tangent derivatives of `q₀` and `q₁` remain divisible by those
coordinates.  The theorem converts them to the explicit uniformizer powers
required by `FormalDivisorAxisLift`. -/
theorem exists_formalDivisorAxisLift_of_projectiveRatio
    {k : Type u} [Field k] [CharZero k]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (q : ι → PowerSeries k)
    (Z : Matrix ι κ (PowerSeries k))
    (rows : κ ↪ ι) (chart zero axis : ι)
    (ratio : PowerSeries k)
    (hqchart : q chart = 1)
    (hZchart : ∀ j, Z chart j = 0)
    (hqzero_ne : q zero ≠ 0)
    (hratio_ne : ratio ≠ 0)
    (hqzero_vanish : PowerSeries.constantCoeff (q zero) = 0)
    (hratio_vanish : PowerSeries.constantCoeff ratio = 0)
    (hqaxis : q axis = q zero * ratio)
    (hZzero_dvd : ∀ j, q zero ∣ Z zero j)
    (hZaxis_dvd : ∀ j, q axis ∣ Z axis j)
    (hminor :
      PowerSeries.constantCoeff
        (selectedMinor Z rows).det ≠ 0) :
    ∃ (tau : ι → PowerSeries k)
      (C : Matrix (FormalTangentColumn κ) ι (PowerSeries k))
      (ell : ι → PowerSeries k),
      C * formalTangentMatrix q Z tau = 1 ∧
      rowMul ell (formalTangentMatrix q Z tau) = 0 ∧
      residueColumn ell = axisRow (k := k) axis := by
  obtain ⟨a, b, u₀, u₁, ha, hab, hqzero_factor, hu₀,
      hqaxis_factor, hu₁⟩ :=
    exists_powerSeries_strict_projectiveOrderGap
      (q zero) ratio (q axis) hqzero_ne hratio_ne
        hqzero_vanish hratio_vanish hqaxis
  have hZzero : ∀ j, ∃ w : PowerSeries k,
      Z zero j = (PowerSeries.X : PowerSeries k) ^ a * w := by
    intro j
    obtain ⟨w, hw⟩ := hZzero_dvd j
    refine ⟨u₀ * w, ?_⟩
    rw [hw, hqzero_factor]
    ring
  have hZaxis : ∀ j, ∃ w : PowerSeries k,
      Z axis j = (PowerSeries.X : PowerSeries k) ^ b * w := by
    intro j
    obtain ⟨w, hw⟩ := hZaxis_dvd j
    refine ⟨u₁ * w, ?_⟩
    rw [hw, hqaxis_factor]
    ring
  obtain ⟨lambda, c, tau, C, ell, _hlambda, _hselected,
      _htauchart, _htauselected, _hc, _hfactor, _hprimitive,
      _htauaxis, _haxiscolumns, hleft, hrow, hresidue⟩ :=
    exists_formalDivisorAxisLift q Z rows chart zero axis a b u₀ u₁
      hqchart hZchart ha hab hqzero_factor hu₀ hZzero
        hqaxis_factor hZaxis hminor
  exact ⟨tau, C, ell, hleft, hrow, hresidue⟩


end

end Stafford38.Geometry.ProjectiveDivisorOrderGap
