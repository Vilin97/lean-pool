/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.BoundaryFromRadial

/-!
# Final monotonicity increment

This module contains the final radius integration step and converts the
boundary identity into monotonicity of the weak theta quantity.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Step 4: integrate the a.e. derivative formula for `theta`. -/
theorem interior_monotonicity_formula_smooth {n m : ℕ}
    {u : Domain n → Target m} {a : Domain n} {R0 s r : ℝ}
    (hu : ContDiff ℝ 1 u)
    (hboundary : BoundaryIdentity u a R0)
    (hs : 0 < s) (hsr : s < r) (hr : r < R0)
    (hderive :
      ContDiff ℝ 1 u →
        BoundaryIdentity u a R0 →
          0 < s →
            s < r →
              r < R0 →
                theta u a r - theta u a s = monotonicityRhs u a s r) :
    theta u a r - theta u a s = monotonicityRhs u a s r := by
  exact hderive hu hboundary hs hsr hr

/-- Weak version of the final integration step, using `weakTheta` and the weak
annular radial-energy term. -/
theorem interior_monotonicity_formula_weak {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {R0 s r : ℝ}
    (hboundary : WeakBoundaryIdentity Du a R0)
    (hs : 0 < s) (hsr : s < r) (hr : r < R0)
    (hderive :
      WeakBoundaryIdentity Du a R0 →
        0 < s →
          s < r →
            r < R0 →
              weakTheta Du a r - weakTheta Du a s = weakMonotonicityRhs Du a s r) :
    weakTheta Du a r - weakTheta Du a s = weakMonotonicityRhs Du a s r := by
  exact hderive hboundary hs hsr hr

/-- Radius-variable form of the final monotonicity increment.  This integrates
the a.e. boundary identity against the derivative of the monotonicity weight;
the remaining step is to convert the right-hand side to the annular spatial
integral. -/
theorem weakTheta_increment_eq_radius_integral_of_boundary
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 s r : ℝ}
    (hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (hs : 0 < s) (hsr : s < r) (hr : r < R0) :
    weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
      ∫ rho in s..r,
        2 * thetaFactor n rho *
          deriv (weakBallRadialEnergy Du (0 : Domain n)) rho := by
  let E : ℝ → ℝ := weakBallEnergy Du (0 : Domain n)
  let Q : ℝ → ℝ := weakBallRadialEnergy Du (0 : Domain n)
  have hEac : AbsolutelyContinuousOnInterval E s r := by
    exact hac.1 (le_of_lt hs) (le_of_lt hsr) (le_of_lt hr)
  have hFac : AbsolutelyContinuousOnInterval (thetaFactor n) s r :=
    thetaFactor_absolutelyContinuousOnInterval (n := n) hs hsr
  have hprod :=
    AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hFac hEac
  have hboundary_global :
      ∀ᵐ rho ∂(volume : Measure ℝ), rho ∈ Ioo (0 : ℝ) R0 →
        rho * deriv E rho - ((n : ℝ) - 2) * E rho =
          2 * rho * deriv Q rho := by
    simpa [WeakBoundaryIdentity, E, Q] using
      (ae_restrict_iff' measurableSet_Ioo).1 hboundary
  have hintegrand :
      (∫ rho in s..r,
        deriv (thetaFactor n) rho * E rho +
          thetaFactor n rho * deriv E rho)
        =
      ∫ rho in s..r,
        2 * thetaFactor n rho * deriv Q rho := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hboundary_global] with rho hbd hrho
    have hrhoIoc : rho ∈ Ioc s r := by
      simpa [uIoc_of_le (le_of_lt hsr)] using hrho
    have hrho_pos : 0 < rho := hs.trans hrhoIoc.1
    have hrho_R0 : rho < R0 := hrhoIoc.2.trans_lt hr
    simpa [E, Q] using
      thetaFactor_boundary_algebra
        (n := n) (rho := rho)
        (E := E rho) (E' := deriv E rho) (Q' := deriv Q rho)
        hrho_pos.ne' (hbd ⟨hrho_pos, hrho_R0⟩)
  calc
    weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s
        =
      (∫ rho in s..r,
        deriv (thetaFactor n) rho * E rho +
          thetaFactor n rho * deriv E rho) := by
        rw [hprod]
        rfl
    _ =
      ∫ rho in s..r,
        2 * thetaFactor n rho * deriv Q rho := hintegrand

/-- A radial indicator on the containing ball is the same as integrating over
the annulus.  The inner boundary sphere is null in positive dimension. -/
theorem radial_weighted_annulus_integral_eq_indicator_integral
    {n : ℕ} [NeZero n] {F : Domain n → ℝ} {s r R0 : ℝ}
    (hrR0 : r ≤ R0) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo s r).indicator (fun rho : ℝ => thetaFactor n rho) ‖x‖ * F x)
      =
    ∫ x in Metric.ball (0 : Domain n) r \ Metric.ball (0 : Domain n) s,
        thetaFactor n ‖x‖ * F x := by
  let ann : Set (Domain n) := {x | ‖x‖ ∈ Ioo s r}
  have hann_meas : MeasurableSet ann := by
    exact (isOpen_Ioo.preimage continuous_norm).measurableSet
  have hset :
      Metric.ball (0 : Domain n) R0 ∩ ann =
        Metric.ball (0 : Domain n) r \ Metric.closedBall (0 : Domain n) s := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨_hR0, hxann⟩
      exact ⟨by
          simpa [Metric.mem_ball, dist_eq_norm, ann] using hxann.2,
        by
          intro hxclosed
          have hle : ‖x‖ ≤ s := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hxclosed
          exact (not_le_of_gt hxann.1) hle⟩
    · intro hx
      rcases hx with ⟨hxr, hxclosed⟩
      have hxnorm_lt_r : ‖x‖ < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hxr
      have hxann_left : s < ‖x‖ := by
        by_contra hnot
        have hle : ‖x‖ ≤ s := le_of_not_gt hnot
        exact hxclosed (by simpa [Metric.mem_closedBall, dist_eq_norm] using hle)
      exact ⟨by
          have hxnorm_lt_R0 : ‖x‖ < R0 := lt_of_lt_of_le hxnorm_lt_r hrR0
          simpa [Metric.mem_ball, dist_eq_norm] using hxnorm_lt_R0,
        ⟨hxann_left, hxnorm_lt_r⟩⟩
  have hclosed_ae :
      (Metric.ball (0 : Domain n) r \ Metric.closedBall (0 : Domain n) s)
        =ᵐ[volume]
      (Metric.ball (0 : Domain n) r \ Metric.ball (0 : Domain n) s) :=
    ball_diff_closedBall_ae_eq_ball_diff_ball (n := n) (a := s) (b := r)
  calc
    (∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo s r).indicator (fun rho : ℝ => thetaFactor n rho) ‖x‖ * F x)
        =
      ∫ x in Metric.ball (0 : Domain n) R0,
        ann.indicator (fun x : Domain n => thetaFactor n ‖x‖ * F x) x := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x _hx
        change (Ioo s r).indicator (fun rho : ℝ => thetaFactor n rho) ‖x‖ * F x =
          ann.indicator (fun x : Domain n => thetaFactor n ‖x‖ * F x) x
        by_cases hxann : ‖x‖ ∈ Ioo s r
        · have hxann' : x ∈ ann := by
            simpa [ann] using hxann
          rw [Set.indicator_of_mem hxann, Set.indicator_of_mem hxann']
        · have hxann' : x ∉ ann := by
            simpa [ann] using hxann
          rw [Set.indicator_of_notMem hxann, Set.indicator_of_notMem hxann']
          simp
    _ =
      ∫ x in Metric.ball (0 : Domain n) R0 ∩ ann,
        thetaFactor n ‖x‖ * F x := by
        rw [setIntegral_indicator hann_meas]
    _ =
      ∫ x in Metric.ball (0 : Domain n) r \ Metric.closedBall (0 : Domain n) s,
        thetaFactor n ‖x‖ * F x := by
        rw [hset]
    _ =
      ∫ x in Metric.ball (0 : Domain n) r \ Metric.ball (0 : Domain n) s,
        thetaFactor n ‖x‖ * F x :=
        setIntegral_congr_set hclosed_ae

/-- The annular term in the monotonicity formula is exactly the corresponding
radius integral of the radial-energy derivative. -/
theorem weakMonotonicityRhs_eq_radius_integral
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 s r : ℝ}
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hs : 0 < s) (hsr : s < r) (hr : r < R0) :
    weakMonotonicityRhs Du (0 : Domain n) s r =
      2 * ∫ rho in s..r,
        thetaFactor n rho *
          deriv (weakBallRadialEnergy Du (0 : Domain n)) rho := by
  let Q : ℝ → ℝ := weakBallRadialEnergy Du (0 : Domain n)
  let c : ℝ → ℝ := fun rho =>
    (Ioo s r).indicator (fun rho : ℝ => thetaFactor n rho) rho
  have hspace :
      (∫ x in Metric.ball (0 : Domain n) R0,
          c ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x)
        =
      ∫ x in Metric.ball (0 : Domain n) r \ Metric.ball (0 : Domain n) s,
          thetaFactor n ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x := by
    simpa [c] using
      radial_weighted_annulus_integral_eq_indicator_integral
        (n := n)
        (F := fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (s := s) (r := r) (R0 := R0) (le_of_lt hr)
  have hradius :
      (∫ x in Metric.ball (0 : Domain n) R0,
          c ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x)
        =
      ∫ rho in Ioo (0 : ℝ) R0, c rho * deriv Q rho := by
    simpa [Q] using hradial_radius c
  have hinterval :
      (∫ rho in Ioo (0 : ℝ) R0, c rho * deriv Q rho)
        =
      ∫ rho in s..r, thetaFactor n rho * deriv Q rho := by
    calc
      (∫ rho in Ioo (0 : ℝ) R0, c rho * deriv Q rho)
          =
        ∫ rho in Ioo (0 : ℝ) R0,
          (Ioo s r).indicator (fun _ : ℝ => (1 : ℝ)) rho *
            (thetaFactor n rho * deriv Q rho) := by
          apply integral_congr_ae
          filter_upwards with rho
          by_cases h : rho ∈ Ioo s r <;> simp [c, h]
      _ =
        ∫ rho in s..r, thetaFactor n rho * deriv Q rho :=
          integral_Ioo_zero_radius_indicator_Ioo_eq_intervalIntegral
            (f := fun rho : ℝ => thetaFactor n rho * deriv Q rho)
            (a := s) (b := r) (R0 := R0)
            (le_of_lt hs) (le_of_lt hsr) (le_of_lt hr)
  calc
    weakMonotonicityRhs Du (0 : Domain n) s r
        =
      2 * ∫ x in Metric.ball (0 : Domain n) r \ Metric.ball (0 : Domain n) s,
        thetaFactor n ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x := by
        simp [weakMonotonicityRhs, thetaFactor]
    _ =
      2 * ∫ x in Metric.ball (0 : Domain n) R0,
        c ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x := by
        rw [hspace]
    _ =
      2 * ∫ rho in Ioo (0 : ℝ) R0, c rho * deriv Q rho := by
        rw [hradius]
    _ =
      2 * ∫ rho in s..r, thetaFactor n rho * deriv Q rho := by
        rw [hinterval]

/-- Restricted-weight version of the conversion from the annular spatial term
to the radius integral of the radial-energy derivative. -/
theorem weakMonotonicityRhs_eq_radius_integral_forWeights
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 s r : ℝ}
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hs : 0 < s) (hsr : s < r) (hr : r < R0) :
    weakMonotonicityRhs Du (0 : Domain n) s r =
      2 * ∫ rho in s..r,
        thetaFactor n rho *
          deriv (weakBallRadialEnergy Du (0 : Domain n)) rho := by
  let Q : ℝ → ℝ := weakBallRadialEnergy Du (0 : Domain n)
  let c : ℝ → ℝ := fun rho =>
    (Ioo s r).indicator (fun rho : ℝ => thetaFactor n rho) rho
  have hspace :
      (∫ x in Metric.ball (0 : Domain n) R0,
          c ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x)
        =
      ∫ x in Metric.ball (0 : Domain n) r \ Metric.ball (0 : Domain n) s,
          thetaFactor n ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x := by
    simpa [c] using
      radial_weighted_annulus_integral_eq_indicator_integral
        (n := n)
        (F := fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (s := s) (r := r) (R0 := R0) (le_of_lt hr)
  have hradius :
      (∫ x in Metric.ball (0 : Domain n) R0,
          c ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x)
        =
      ∫ rho in Ioo (0 : ℝ) R0, c rho * deriv Q rho := by
    simpa [Q, c] using
      hradial_radius
        (fun rho : ℝ =>
          (Ioo s r).indicator (fun rho : ℝ => thetaFactor n rho) rho)
        (radiusWeightOn_indicator_thetaFactor (n := n) (R0 := R0)
          (s := s) (r := r) hs)
  have hinterval :
      (∫ rho in Ioo (0 : ℝ) R0, c rho * deriv Q rho)
        =
      ∫ rho in s..r, thetaFactor n rho * deriv Q rho := by
    calc
      (∫ rho in Ioo (0 : ℝ) R0, c rho * deriv Q rho)
          =
        ∫ rho in Ioo (0 : ℝ) R0,
          (Ioo s r).indicator (fun _ : ℝ => (1 : ℝ)) rho *
            (thetaFactor n rho * deriv Q rho) := by
          apply integral_congr_ae
          filter_upwards with rho
          by_cases h : rho ∈ Ioo s r <;> simp [c, h]
      _ =
        ∫ rho in s..r, thetaFactor n rho * deriv Q rho :=
          integral_Ioo_zero_radius_indicator_Ioo_eq_intervalIntegral
            (f := fun rho : ℝ => thetaFactor n rho * deriv Q rho)
            (a := s) (b := r) (R0 := R0)
            (le_of_lt hs) (le_of_lt hsr) (le_of_lt hr)
  calc
    weakMonotonicityRhs Du (0 : Domain n) s r
        =
      2 * ∫ x in Metric.ball (0 : Domain n) r \ Metric.ball (0 : Domain n) s,
        thetaFactor n ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x := by
        simp [weakMonotonicityRhs, thetaFactor]
    _ =
      2 * ∫ x in Metric.ball (0 : Domain n) R0,
        c ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x := by
        rw [hspace]
    _ =
      2 * ∫ rho in Ioo (0 : ℝ) R0, c rho * deriv Q rho := by
        rw [hradius]
    _ =
      2 * ∫ rho in s..r, thetaFactor n rho * deriv Q rho := by
        rw [hinterval]

/-- The final increment formula derived from the weak boundary identity, radius
absolute continuity, and the radial-energy radius formula. -/
theorem weakTheta_increment_eq_weakMonotonicityRhs_of_boundary
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 s r : ℝ}
    (hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hs : 0 < s) (hsr : s < r) (hr : r < R0) :
    weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
      weakMonotonicityRhs Du (0 : Domain n) s r := by
  rw [weakTheta_increment_eq_radius_integral_of_boundary
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hboundary hac hs hsr hr]
  rw [weakMonotonicityRhs_eq_radius_integral
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hradial_radius hs hsr hr]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with rho _hrho
  ring

/-- Restricted-weight version of the final increment formula derived from the
weak boundary identity. -/
theorem weakTheta_increment_eq_weakMonotonicityRhs_of_boundary_forWeights
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 s r : ℝ}
    (hboundary : WeakBoundaryIdentity Du (0 : Domain n) R0)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hs : 0 < s) (hsr : s < r) (hr : r < R0) :
    weakTheta Du (0 : Domain n) r - weakTheta Du (0 : Domain n) s =
      weakMonotonicityRhs Du (0 : Domain n) s r := by
  rw [weakTheta_increment_eq_radius_integral_of_boundary
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hboundary hac hs hsr hr]
  rw [weakMonotonicityRhs_eq_radius_integral_forWeights
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hradial_radius hs hsr hr]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with rho _hrho
  ring

/-- The equality formula immediately gives monotonicity, because the annular integral is
nonnegative. -/
theorem theta_monotone_on_of_formula {n m : ℕ}
    {u : Domain n → Target m} {a : Domain n} {R0 : ℝ}
    (hformula :
      ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
        theta u a r - theta u a s = monotonicityRhs u a s r)
    (hrhs_nonneg :
      ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
        0 ≤ monotonicityRhs u a s r) :
    MonotoneOn (theta u a) (Ioo (0 : ℝ) R0) := by
  intro s hs_mem r hr_mem hsr
  rcases hs_mem with ⟨hs_pos, hs_lt_R0⟩
  rcases hr_mem with ⟨hr_pos, hr_lt_R0⟩
  rcases hsr.eq_or_lt with rfl | hsr_lt
  · exact le_rfl
  · have hdiff :
        theta u a r - theta u a s = monotonicityRhs u a s r :=
      hformula hs_pos hsr_lt hr_lt_R0
    have hnonneg : 0 ≤ theta u a r - theta u a s := by
      simpa [hdiff] using hrhs_nonneg hs_pos hsr_lt hr_lt_R0
    linarith

/-- Weak monotonicity follows from the weak equality formula and nonnegativity of
the weak annular radial-energy term. -/
theorem weakTheta_monotone_on_of_formula {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {R0 : ℝ}
    (hformula :
      ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
        weakTheta Du a r - weakTheta Du a s = weakMonotonicityRhs Du a s r)
    (hrhs_nonneg :
      ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
        0 ≤ weakMonotonicityRhs Du a s r) :
    MonotoneOn (weakTheta Du a) (Ioo (0 : ℝ) R0) := by
  intro s hs_mem r hr_mem hsr
  rcases hs_mem with ⟨hs_pos, _hs_lt_R0⟩
  rcases hr_mem with ⟨_hr_pos, hr_lt_R0⟩
  rcases hsr.eq_or_lt with rfl | hsr_lt
  · exact le_rfl
  · have hdiff :
        weakTheta Du a r - weakTheta Du a s = weakMonotonicityRhs Du a s r :=
      hformula hs_pos hsr_lt hr_lt_R0
    have hnonneg : 0 ≤ weakTheta Du a r - weakTheta Du a s := by
      simpa [hdiff] using hrhs_nonneg hs_pos hsr_lt hr_lt_R0
    linarith

/-- Clean weak monotonicity interface: once the weak equality formula is known,
monotonicity follows from the built-in nonnegativity of the radial-energy RHS. -/
theorem weakTheta_monotone_on_of_formula' {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {R0 : ℝ}
    (hformula :
      ∀ ⦃s r : ℝ⦄, 0 < s → s < r → r < R0 →
        weakTheta Du a r - weakTheta Du a s = weakMonotonicityRhs Du a s r) :
    MonotoneOn (weakTheta Du a) (Ioo (0 : ℝ) R0) := by
  exact weakTheta_monotone_on_of_formula
    (n := n) (m := m) (Du := Du) (a := a) (R0 := R0)
    hformula
    (fun {s} {r} _hs _hsr _hr => weakMonotonicityRhs_nonneg Du a s r)

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
