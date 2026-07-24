/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.MonotonicityRoutes
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadiusWeightedRepresentation

/-!
# Euclidean weak monotonicity interfaces

This module contains the strongest Euclidean and restricted-weight packaged
weak monotonicity interfaces.

This file is still part of the internal proof route: it closes the Euclidean
coarea and thin-shell ingredients before `MainTheorem.lean` packages the final
user-facing statement.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Current strongest packaged weak-map monotonicity interface: primitive
cutoffs are constructed, thin radial-shell volume control supplies radius
absolute continuity, and the final boundary-to-monotonicity increment is proved
inside Lean rather than supplied as an external `hderive` input. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_radialShellsVolume_primitiveCutoffs_closed
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
        (Ioo (0 : ℝ) R0) volume) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0 :=
    weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hthin hmap.1 hclosedBall_subset
  exact weakTheta_monotone_from_weakStationaryMapIn_via_radialShellsVolume_primitiveCutoffs
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hthin
    henergy_radius hradial_radius hdefect_loc
    (fun hboundary {s} {r} hs hsr hr =>
      weakTheta_increment_eq_weakMonotonicityRhs_of_boundary
        (n := n) (m := m) (Du := Du) (R0 := R0) (s := s) (r := r)
        hboundary hac hradial_radius hs hsr hr)

/-- Restricted-weight version of the strongest packaged weak-map monotonicity
interface through primitive cutoffs and thin radial-shell volume control. -/
theorem weakTheta_monotone_from_stationaryMap_radialShells_closedForWeights
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0 :=
    weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hthin hmap.1 hclosedBall_subset
  have hball_subset : Metric.ball (0 : Domain n) R0 ⊆ Ω :=
    (Metric.ball_subset_closedBall : Metric.ball (0 : Domain n) R0 ⊆
      Metric.closedBall (0 : Domain n) R0).trans hclosedBall_subset
  have hstationary_ball :
      WeakStationaryIn Du (Metric.ball (0 : Domain n) R0) :=
    weakStationaryIn_of_subset
      (n := n) (m := m) (Du := Du)
      (Ω := Ω) (Ω' := Metric.ball (0 : Domain n) R0)
      hmap.2 hΩ_meas hball_subset
  have hcalc : WeakBallEnergyOneDimensionalCalculus Du R0 :=
    weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hthin hmap.1 hclosedBall_subset henergy_radius hradial_radius
  have hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0 :=
    weak_boundary_identity_from_stationarity_of_W12Loc_via_primitivesForWeights
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hstationary_ball hmap.1 hclosedBall_subset
      henergy_radius hradial_radius hdefect_loc hcalc
      (weakPrimitiveCutoffRealization R0)
  exact weakTheta_monotone_on_of_formula'
    (n := n) (m := m) (Du := Du) (a := (0 : Domain n)) (R0 := R0)
    (fun {s} {r} hs hsr hr =>
      weakTheta_increment_eq_weakMonotonicityRhs_of_boundary_forWeights
        (n := n) (m := m) (Du := Du) (R0 := R0) (s := s) (r := r)
        hboundary hac hradial_radius hs hsr hr)

/-- Same packaged interface as
`weakTheta_monotone_from_weakStationaryMapIn_via_radialShellsVolume_primitiveCutoffs_closed`,
but the local integrability of the sharp-cutoff defect is discharged from the
radius absolute-continuity package obtained via thin radial-shell volume
control. -/
theorem weakTheta_monotone_from_W12Loc_radialShellsVolume_closed
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0 :=
    weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hthin hmap.1 hclosedBall_subset
  have hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume :=
    weakSharpCutoffDefect_locallyIntegrableOn_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hac
  exact
    weakTheta_monotone_from_weakStationaryMapIn_via_radialShellsVolume_primitiveCutoffs_closed
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hmap hΩ_meas hclosedBall_subset hthin
      henergy_radius hradial_radius hdefect_loc

/-- Restricted-weight version of
`weakTheta_monotone_from_W12Loc_radialShellsVolume_closed`. -/
theorem weakTheta_monotone_from_W12Loc_radialShellsVolume_closedForWeights
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0 :=
    weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hthin hmap.1 hclosedBall_subset
  have hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume :=
    weakSharpCutoffDefect_locallyIntegrableOn_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hac
  exact
    weakTheta_monotone_from_stationaryMap_radialShells_closedForWeights
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hmap hΩ_meas hclosedBall_subset hthin
      henergy_radius hradial_radius hdefect_loc

/-- Strong packaged weak-map monotonicity interface where the two map-specific
radius integration formulas are discharged from one generic ball-integral
coarea/radius-derivative theorem. -/
theorem weakTheta_monotone_from_W12Loc_radialShellsVolume_coarea
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (hcoarea : BallIntegralRadiusDerivativeFormula n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hradius : WeakRadiusIntegralFormulas Du R0 :=
    weakRadiusIntegralFormulas_of_W12LocIn_coarea
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hcoarea hmap.1 hclosedBall_subset
  exact weakTheta_monotone_from_W12Loc_radialShellsVolume_closed
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hthin
    hradius.1 hradius.2

/-- Restricted-weight version of the strong packaged weak-map monotonicity
interface: the generic coarea theorem only needs to hold for measurable
essentially bounded radius weights. -/
theorem weakTheta_monotone_from_W12Loc_radialShellsVolume_coareaForWeights
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (hcoarea : BallIntegralRadiusDerivativeFormulaForWeights n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hradius : WeakRadiusIntegralFormulasForWeights Du R0 :=
    weakRadiusIntegralFormulasForWeights_of_W12LocIn_coarea
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hcoarea hmap.1 hclosedBall_subset
  exact weakTheta_monotone_from_W12Loc_radialShellsVolume_closedForWeights
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hthin
    hradius.1 hradius.2

/-- Strong packaged weak-map monotonicity interface where the thin-shell input
is reduced to absolute continuity of the Euclidean ball-volume radius function. -/
theorem weakTheta_monotone_from_W12Loc_ballVolumeAC_coarea
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hball : EuclideanBallVolumeAbsolutelyContinuous n)
    (hcoarea : BallIntegralRadiusDerivativeFormula n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12Loc_radialShellsVolume_coarea
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    (radialOpenShellsVolumeTendstoZero_of_ballVolume_ac
      (n := n) hball)
    hcoarea

/-- Restricted-weight version where the thin-shell input is reduced to absolute
continuity of the Euclidean ball-volume radius function. -/
theorem weakTheta_monotone_from_W12Loc_ballVolumeAC_coareaForWeights
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hball : EuclideanBallVolumeAbsolutelyContinuous n)
    (hcoarea : BallIntegralRadiusDerivativeFormulaForWeights n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12Loc_radialShellsVolume_coareaForWeights
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    (radialOpenShellsVolumeTendstoZero_of_ballVolume_ac
      (n := n) hball)
    hcoarea

/-- Strong packaged weak-map monotonicity interface with the Euclidean
thin-shell estimate discharged from the explicit ball-volume formula.  The only
remaining geometric analysis input is the ball-integral coarea/radius-derivative
formula. -/
theorem weakTheta_monotone_from_W12Loc_euclidean_coarea
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hcoarea : BallIntegralRadiusDerivativeFormula n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12Loc_ballVolumeAC_coarea
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    (euclideanBallVolumeAbsolutelyContinuous n) hcoarea

/-- Restricted-weight Euclidean weak-map monotonicity interface.  The remaining
coarea input only has to be proved for measurable essentially bounded radius
weights. -/
theorem weakTheta_monotone_from_W12Loc_euclidean_coareaForWeights
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hcoarea : BallIntegralRadiusDerivativeFormulaForWeights n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12Loc_ballVolumeAC_coareaForWeights
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    (euclideanBallVolumeAbsolutelyContinuous n) hcoarea

/-- Euclidean weak-map monotonicity from the concrete finite-interval
approximation bridge for bounded measurable radius weights.  This removes the
abstract coarea/radius-derivative hypothesis from the final interface; the only
remaining input for this route is a bounded interval-step approximation of each
radius weight on `(0, R0)`, with an exceptional set whose radial pullback is
null on the ball. -/
theorem weakTheta_monotone_from_W12Loc_euclidean_finiteIntervalStepApproxAE
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_pos : 0 < R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (happrox : ∀ c : ℝ → ℝ,
      RadiusWeightOn R0 c → RadiusWeightFiniteIntervalStepApproxAE R0 c) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  have hradius : WeakRadiusIntegralFormulasForWeights Du R0 :=
    weakRadiusIntegralFormulasForWeights_of_W12LocIn_finiteIntervalStepApproxAE
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_pos happrox hmap.1 hclosedBall_subset
  exact weakTheta_monotone_from_W12Loc_radialShellsVolume_closedForWeights
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_pos.le hmap hΩ_meas hclosedBall_subset
    (radialOpenShellsVolumeTendstoZero_euclidean n)
    hradius.1 hradius.2

/-- Same Euclidean weak-map monotonicity interface, but with the remaining
coarea input split into a radial density representation plus a.e. derivative
identification.  This is the next target for replacing the abstract coarea
assumption by a direct measure-theoretic proof. -/
theorem weakTheta_monotone_from_W12Loc_euclidean_radiusRepresentation
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hrep : BallIntegralRadiusDerivativeRepresentation n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12Loc_euclidean_coarea
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    (ballIntegralRadiusDerivativeFormula_of_representation (n := n) hrep)

/-- Same Euclidean weak-map monotonicity interface with the final coarea input
split into the pure weighted radial representation and the a.e. derivative
identification of the representing density. -/
theorem weakTheta_monotone_from_W12Loc_euclidean_weightedRepresentation
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hweighted : BallIntegralRadiusWeightedRepresentation n)
    (hidentify : BallIntegralRadiusDerivativeIdentification n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12Loc_euclidean_radiusRepresentation
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    (ballIntegralRadiusDerivativeRepresentation_of_weightedRepresentation
      (n := n) hweighted hidentify)

/-- Same Euclidean weak-map monotonicity interface after the unrestricted
one-dimensional derivative-identification theorem has been proved: the only
remaining coarea-side input is the pure weighted radial representation. -/
theorem weakTheta_monotone_from_W12Loc_euclidean_weightedRepresentation_identified
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hweighted : BallIntegralRadiusWeightedRepresentation n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12Loc_euclidean_radiusRepresentation
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    (ballIntegralRadiusDerivativeRepresentation_of_weightedRepresentation_identified
      (n := n) hweighted)

/-- Restricted-weight Euclidean weak-map monotonicity interface with the final
coarea input split into the restricted weighted radial representation and the
restricted a.e. derivative identification. -/
theorem weakTheta_monotone_from_W12Loc_euclidean_weightedRepresentationForWeights
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hweighted : BallIntegralRadiusWeightedRepresentationForWeights n)
    (hidentify : BallIntegralRadiusDerivativeIdentificationForWeights n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12Loc_euclidean_coareaForWeights
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    (ballIntegralRadiusDerivativeFormulaForWeights_of_weightedRepresentation
      (n := n) hweighted hidentify)

/-- Restricted-weight Euclidean weak-map monotonicity interface after the
restricted derivative-identification theorem has been proved: the only
remaining coarea-side input is the restricted weighted radial representation. -/
theorem weakTheta_monotone_from_W12Loc_euclidean_weightedRepresentationForWeights_identified
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hweighted : BallIntegralRadiusWeightedRepresentationForWeights n) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12Loc_euclidean_coareaForWeights
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    (ballIntegralRadiusDerivativeFormulaForWeights_of_weightedRepresentation_identified
      (n := n) hweighted)

/-- Fully Euclidean weak-map monotonicity interface after the radial
pushforward/coarea representation has been supplied by the Radon-Nikodym
density. -/
theorem weakTheta_monotone_from_W12Loc_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_W12Loc_euclidean_weightedRepresentationForWeights_identified
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset
    (ballIntegralRadiusWeightedRepresentationForWeights_euclidean n)

/-- Fully Euclidean weak-map increment formula in the origin-centered form.

This is the equality form of the monotonicity formula:
`weakTheta r - weakTheta s` is the annular radial-energy term
`weakMonotonicityRhs s r`. -/
theorem weakTheta_increment_eq_weakMonotonicityRhs_from_W12Loc_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 s r : ℝ}
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s < r)
    (hr_lt : r < R0) :
    weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
      weakMonotonicityRhs Du (0 : Domain n) s r := by
  have hR0_nonneg : 0 ≤ R0 := le_of_lt ((hs_pos.trans hsr).trans hr_lt)
  have hthin : RadialOpenShellsVolumeTendstoZero n :=
    radialOpenShellsVolumeTendstoZero_euclidean n
  have hcoarea : BallIntegralRadiusDerivativeFormulaForWeights n :=
    ballIntegralRadiusDerivativeFormulaForWeights_of_weightedRepresentation_identified
      (n := n) (ballIntegralRadiusWeightedRepresentationForWeights_euclidean n)
  have hradius : WeakRadiusIntegralFormulasForWeights Du R0 :=
    weakRadiusIntegralFormulasForWeights_of_W12LocIn_coarea
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hcoarea hmap.1 hclosedBall_subset
  have hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0 :=
    weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hthin hmap.1 hclosedBall_subset
  have hdefect_loc :
      LocallyIntegrableOn
        (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
        (Ioo (0 : ℝ) R0) volume :=
    weakSharpCutoffDefect_locallyIntegrableOn_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hac
  have hball_subset : Metric.ball (0 : Domain n) R0 ⊆ Ω :=
    (Metric.ball_subset_closedBall : Metric.ball (0 : Domain n) R0 ⊆
      Metric.closedBall (0 : Domain n) R0).trans hclosedBall_subset
  have hstationary_ball :
      WeakStationaryIn Du (Metric.ball (0 : Domain n) R0) :=
    weakStationaryIn_of_subset
      (n := n) (m := m) (Du := Du)
      (Ω := Ω) (Ω' := Metric.ball (0 : Domain n) R0)
      hmap.2 hΩ_meas hball_subset
  have hcalc : WeakBallEnergyOneDimensionalCalculus Du R0 :=
    weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hthin hmap.1 hclosedBall_subset hradius.1 hradius.2
  have hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0 :=
    weak_boundary_identity_from_stationarity_of_W12Loc_via_primitivesForWeights
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_nonneg hstationary_ball hmap.1 hclosedBall_subset
      hradius.1 hradius.2 hdefect_loc hcalc
      (weakPrimitiveCutoffRealization R0)
  exact
    weakTheta_increment_eq_weakMonotonicityRhs_of_boundary_forWeights
      (n := n) (m := m) (Du := Du) (R0 := R0) (s := s) (r := r)
      hboundary hac hradius.2 hs_pos hsr hr_lt

/-- Final packaged weak-map interface with the primitive-cutoff realization
constructed from interval integrals and smooth bumps.  The remaining
one-dimensional inputs are the energy IBP formula and its integrability side
conditions. -/
theorem weakTheta_monotone_from_weakStationaryMapIn_via_constructed_primitive
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
    (hderive :
      WeakBoundaryIdentity Du (0 : Domain n) R0 →
        ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
          weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
            weakMonotonicityRhs Du (0 : Domain n) s r) :
    MonotoneOn (weakTheta Du (0 : Domain n)) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_from_weakStationaryMapIn_via_realized_ingredients
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hmap hΩ_meas hclosedBall_subset hflat
    henergy_radius hradial_radius hdefect_loc henergy_ibp hibp_int
    (weakPrimitiveCutoffRealization R0) hderive

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
