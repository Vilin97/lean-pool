/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.MonotonicityFinal

/-!
# Packaged monotonicity routes

This module contains the main packaged weak monotonicity routes up to the
thin-shell and primitive-cutoff interfaces.

These declarations are internal scaffolding for the proof architecture.  User
code should normally import `MainTheorem.lean` or `API.lean` instead of relying
on a particular route theorem in this file.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- End-to-end weak monotonicity route from radial stationarity, after splitting
the remaining analytic content into radius coarea formulas, one-dimensional
integration by parts, primitive cutoffs, and the final boundary-to-radius
identity. -/
theorem weakTheta_monotone_from_radial_identity_via_radius_formulas {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialStationarityIdentity Du R0)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0 :=
    weak_boundary_identity_from_radial_identity_via_radius_formulas
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hrad hflat henergy_radius hradial_radius
      hdefect_loc hibp_formula hprimitive
  exact weakTheta_monotone_on_of_formula'
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    (fun {s} {r} hs hsr hr => hderive hboundary hs hsr hr)

/-- Weak monotonicity from the scalar-cutoff radial stationarity identity and
the split analytic ingredients. -/
theorem weakTheta_monotone_from_scalar_cutoff_identity_via_radius_formulas {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0 :=
    weak_boundary_identity_from_scalar_cutoff_identity_via_radius_formulas
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hrad henergy_radius hradial_radius
      hdefect_loc hibp_formula hprimitive
  exact weakTheta_monotone_on_of_formula'
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    (fun {s} {r} hs hsr hr => hderive hboundary hs hsr hr)

/-- `W^{1,2}_{loc}` weak stationarity on the ball implies weak monotonicity,
provided the remaining standard radius/coarea, one-dimensional cutoff, and
boundary-to-radius derivative ingredients are available. -/
theorem weakTheta_monotone_from_W12_stationary_via_radius_formulas
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hrad : WeakRadialScalarCutoffStationarityIdentity Du R0 :=
    weak_radial_scalar_cutoff_identity_from_stationarity_of_W12Loc
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hstationary hW hclosedBall_subset hflat
  exact weakTheta_monotone_from_scalar_cutoff_identity_via_radius_formulas
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hrad henergy_radius hradial_radius
    hdefect_loc hibp_formula hprimitive hderive

/-- Domain-level `W^{1,2}_{loc}` weak stationarity implies weak monotonicity on
balls whose closed ball is contained in the domain, modulo the remaining
standard radius/coarea and one-dimensional cutoff ingredients. -/
theorem weakTheta_monotone_from_W12_stationaryIn_via_radius_formulas
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hstationary : WeakStationaryIn Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hball_subset : Metric.ball (0 : Domain n) R0 ⊆ Ω :=
    (Metric.ball_subset_closedBall : Metric.ball (0 : Domain n) R0 ⊆
      Metric.closedBall (0 : Domain n) R0).trans hclosedBall_subset
  have hstationary_ball :
      WeakStationaryIn Du (Metric.ball (0 : Domain n) R0) :=
    weakStationaryIn_of_subset
      (n := n) (m := m) (Du := Du)
      (Ω := Ω) (Ω' := Metric.ball (0 : Domain n) R0)
      hstationary hΩ_meas hball_subset
  exact weakTheta_monotone_from_W12_stationary_via_radius_formulas
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hstationary_ball hW hclosedBall_subset hflat
    henergy_radius hradial_radius hdefect_loc hibp_formula hprimitive hderive

/-- Final packaged weak-map interface: a `WeakStationaryMapIn` on a measurable
domain gives weak monotonicity on any centered ball whose closed ball lies in
the domain, assuming the standard radius/coarea and one-dimensional cutoff
ingredients. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radius_formulas
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hibp_formula : WeakOneDimensionalIBPFormula Du R0)
    (hprimitive : WeakOneDimensionalPrimitiveTestFamily Du R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12_stationaryIn_via_radius_formulas
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap.2 hΩ_meas hmap.1 hclosedBall_subset hflat
    henergy_radius hradial_radius hdefect_loc hibp_formula hprimitive hderive

/-- Final packaged weak-map interface with the one-dimensional IBP and
primitive-cutoff steps expanded into concrete ingredients. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_realized_ingredients
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (henergy_ibp : WeakBallEnergyIntegrationByPartsFormula Du R0)
    (hibp_int : WeakOneDimensionalIBPIntegrability Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hball_subset : Metric.ball (0 : Domain n) R0 ⊆ Ω :=
    (Metric.ball_subset_closedBall : Metric.ball (0 : Domain n) R0 ⊆
      Metric.closedBall (0 : Domain n) R0).trans hclosedBall_subset
  have hstationary_ball :
      WeakStationaryIn Du (Metric.ball (0 : Domain n) R0) :=
    weakStationaryIn_of_subset
      (n := n) (m := m) (Du := Du)
      (Ω := Ω) (Ω' := Metric.ball (0 : Domain n) R0)
      hmap.2 hΩ_meas hball_subset
  have hrad : WeakRadialScalarCutoffStationarityIdentity Du R0 :=
    weak_radial_scalar_cutoff_identity_from_stationarity_of_W12Loc
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hstationary_ball hmap.1 hclosedBall_subset hflat
  have hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0 :=
    weak_boundary_identity_from_scalar_cutoff_identity_via_realized_ingredients
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hrad henergy_radius hradial_radius hdefect_loc
      henergy_ibp hibp_int hprimitive_realize
  exact weakTheta_monotone_on_of_formula'
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    (fun {s} {r} hs hsr hr => hderive hboundary hs hsr hr)

/-- Final weak-map interface with the one-dimensional radius calculus bundled
as a single package. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_energy_calculus
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_realized_ingredients
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hflat
    henergy_radius hradial_radius hdefect_loc
    (weakBallEnergyIntegrationByPartsFormula_of_oneDimensionalCalculus
      (n := n) (m := m) (Du := Du) (R0 := R0) hcalc)
    (weakOneDimensionalIBPIntegrability_of_oneDimensionalCalculus
      (n := n) (m := m) (Du := Du) (R0 := R0) hcalc)
    hprimitive_realize hderive

/-- Final weak-map interface through primitive cutoffs only.  Unlike the older
scalar-cutoff route, this theorem does not assume all scalar cutoffs are flat
near the origin or that all radial vector fields are `C¹`; each one-dimensional
test function is realized by a primitive cutoff that is proved flat near the
origin as part of the construction. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_primitive_cutoffs
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hprimitive_realize : WeakPrimitiveCutoffRealization R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hball_subset : Metric.ball (0 : Domain n) R0 ⊆ Ω :=
    (Metric.ball_subset_closedBall : Metric.ball (0 : Domain n) R0 ⊆
      Metric.closedBall (0 : Domain n) R0).trans hclosedBall_subset
  have hstationary_ball :
      WeakStationaryIn Du (Metric.ball (0 : Domain n) R0) :=
    weakStationaryIn_of_subset
      (n := n) (m := m) (Du := Du)
      (Ω := Ω) (Ω' := Metric.ball (0 : Domain n) R0)
      hmap.2 hΩ_meas hball_subset
  have hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0 :=
    weak_boundary_identity_from_stationarity_of_W12Loc_via_primitives
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hstationary_ball hmap.1 hclosedBall_subset
      henergy_radius hradial_radius hdefect_loc hcalc hprimitive_realize
  exact weakTheta_monotone_on_of_formula'
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    (fun {s} {r} hs hsr hr => hderive hboundary hs hsr hr)

/-- Same primitive-cutoff route with the interval-integral/smooth-bump
realization supplied by the formalized construction. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_constructed_primitive_cutoffs
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_primitive_cutoffs
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    henergy_radius hradial_radius hdefect_loc hcalc
    (weakPrimitiveCutoffRealization R0) hderive

/-- Final weak-map interface where primitive cutoffs are constructed and the
only remaining one-dimensional input is the bundled energy calculus package. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_energy_calculus_and_constructed_primitive
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_energy_calculus
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hflat
    henergy_radius hradial_radius hdefect_loc
    hcalc (weakPrimitiveCutoffRealization R0) hderive

/-- Final weak-map interface using absolute continuity of the radius energy
functions as the one-dimensional calculus input.  Primitive cutoffs are
constructed from interval integrals and smooth bumps. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radius_ac
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_energy_calculus_and_constructed_primitive
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hflat
    henergy_radius hradial_radius hdefect_loc
    (weakBallEnergyOneDimensionalCalculus_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hR0_nonneg hac)
    hderive

/-- Final weak-map interface using the increment/FTC form of the radius energy
identities. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radius_increment
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hinc : WeakEnergyRadiusIncrementFormula Du R0)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_radius_ac
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hflat
    henergy_radius hradial_radius hdefect_loc
    (weakEnergyAbsolutelyContinuousOnRadii_of_increment
      (n := n) (m := m) (Du := Du) (R0 := R0) hinc)
    hderive

/-- Final weak-map interface using radius integration localized to annuli to
produce the radius increment/FTC identities. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radius_annulus
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (hderiv_int : WeakEnergyRadiusDerivativeIntegrability Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hannulus : WeakEnergyAnnulusFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_radius_increment
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hflat
    henergy_radius hradial_radius hdefect_loc
    (weakEnergyRadiusIncrementFormula_of_radiusIntegral_annulus
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hderiv_int henergy_radius hradial_radius hannulus)
    hderive

/-- Final weak-map interface using radius integration localized to annuli, with
the annulus formula generated automatically from the `W^{1,2}_{loc}` hypotheses. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radius_annulus_auto
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_radius_annulus
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hflat
    (weakEnergyRadiusDerivativeIntegrability_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hac)
    henergy_radius hradial_radius
    (weakEnergyAnnulusFormula_of_W12LocIn
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hmap.1 hclosedBall_subset)
    hdefect_loc hderive

/-- Final weak-map interface using the generic `L¹` ball-integral AC theorem
to generate radius absolute continuity from `W^{1,2}_{loc}` automatically. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radius_annulus_ballIntegralAC
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (hball_ac : BallIntegralRadiusACOfIntegrableOnBall n)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_radius_annulus_auto
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hflat
    (weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_ballIntegralAC
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hball_ac hmap.1 hclosedBall_subset)
    henergy_radius hradial_radius hdefect_loc hderive

/-- Final weak-map interface where radius absolute continuity is generated from
the thin radial-shell volume estimate. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radius_annulus_radialShellsVolume
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_radius_annulus_ballIntegralAC
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hflat
    (ballIntegralRadiusACOfIntegrableOnBall_of_radialOpenShellsVolumeTendstoZero
      (n := n) hthin)
    henergy_radius hradial_radius hdefect_loc hderive

/-- Final weak-map interface where the false global flat-cutoff assumption is
replaced by the exact radial-vector-field regularity input needed for
stationarity tests. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radialShellsVolume_vectorFieldContDiff
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hX : RadialVectorFieldContDiffForCutoffs n R0)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hball_subset : Metric.ball (0 : Domain n) R0 ⊆ Ω :=
    (Metric.ball_subset_closedBall : Metric.ball (0 : Domain n) R0 ⊆
      Metric.closedBall (0 : Domain n) R0).trans hclosedBall_subset
  have hstationary_ball :
      WeakStationaryIn Du (Metric.ball (0 : Domain n) R0) :=
    weakStationaryIn_of_subset
      (n := n) (m := m) (Du := Du)
      (Ω := Ω) (Ω' := Metric.ball (0 : Domain n) R0)
      hmap.2 hΩ_meas hball_subset
  have hrad : WeakRadialScalarCutoffStationarityIdentity Du R0 :=
    weak_radial_scalar_cutoff_identity_from_stationarity_of_W12Loc_vectorFieldContDiff
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hstationary_ball hmap.1 hclosedBall_subset hX
  have hcalc : WeakBallEnergyOneDimensionalCalculus Du R0 :=
    weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hthin hmap.1 hclosedBall_subset henergy_radius hradial_radius
  have hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0 :=
    weak_boundary_identity_from_scalar_cutoff_identity_via_realized_ingredients
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hrad henergy_radius hradial_radius hdefect_loc
      hcalc.2.1 hcalc.2.2 (weakPrimitiveCutoffRealization R0)
  exact weakTheta_monotone_on_of_formula'
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    (fun {s} {r} hs hsr hr => hderive hboundary hs hsr hr)

/-- Final packaged weak-map interface through primitive cutoffs and thin
radial-shell volume control.  This is the current `W^{1,2}_{loc}` route without
the old global `hflat` assumption and without the replacement global `hX`
assumption. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radialShellsVolume_primitiveCutoffs
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume)
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hcalc : WeakBallEnergyOneDimensionalCalculus Du R0 :=
    weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hthin hmap.1 hclosedBall_subset henergy_radius hradial_radius
  exact weakTheta_monotone_from_weakStationaryMapIn_via_constructed_primitive_cutoffs
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    henergy_radius hradial_radius hdefect_loc hcalc hderive

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
