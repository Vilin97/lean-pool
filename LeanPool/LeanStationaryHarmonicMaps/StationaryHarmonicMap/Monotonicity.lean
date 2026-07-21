/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.CenterTranslation

/-!
# Stationary Sobolev map monotonicity

This file records the original weak-map monotonicity endpoint used by the
newer public witness API.  The proof is split across smaller modules below
this import.

The current proved endpoint is
`weakTheta_le_of_arbitrary_center_W12Loc_euclidean`.  Future Sobolev bridge
modules should discharge its `WeakStationaryMapIn` hypothesis and then call this
theorem, rather than reopening the radial monotonicity proof chain.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Euclidean-target weak monotonicity in interval form for domain-variation
stationary Sobolev maps. -/
theorem weakTheta_le_of_W12Loc_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 s r : ℝ}
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s ≤ r)
    (hr_lt : r < R0) :
    weakTheta Du (0 : Domain n) s ≤ weakTheta Du (0 : Domain n) r := by
  have hR0_pos : 0 < R0 := by
    exact (lt_of_lt_of_le hs_pos hsr).trans hr_lt
  have hs_mem : s ∈ Ioo (0 : ℝ) R0 :=
    ⟨hs_pos, lt_of_le_of_lt hsr hr_lt⟩
  have hr_mem : r ∈ Ioo (0 : ℝ) R0 :=
    ⟨lt_of_lt_of_le hs_pos hsr, hr_lt⟩
  exact
    (weakTheta_monotone_from_W12Loc_euclidean
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hR0_pos.le hmap hΩ_meas hclosedBall_subset)
      hs_mem hr_mem hsr

/-- Auxiliary arbitrary-center Euclidean weak monotonicity in interval form for
an already recentered weak stationary map package.  The public theorem below
automatically builds this recentered package from `WeakStationaryMapIn u Du Ω`. -/
theorem weakTheta_le_of_centered_W12Loc_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hmap_centered :
      WeakStationaryMapIn
        (fun x : Domain n => u (a + x))
        (translateGradient a Du)
        (centeredDomain a Ω))
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s ≤ r)
    (hr_lt : r < R0) :
    weakTheta Du a s ≤ weakTheta Du a r := by
  have hR0_pos : 0 < R0 := by
    exact (lt_of_lt_of_le hs_pos hsr).trans hr_lt
  have hs_mem : s ∈ Ioo (0 : ℝ) R0 :=
    ⟨hs_pos, lt_of_le_of_lt hsr hr_lt⟩
  have hr_mem : r ∈ Ioo (0 : ℝ) R0 :=
    ⟨lt_of_lt_of_le hs_pos hsr, hr_lt⟩
  exact
    (weakTheta_monotone_from_centered_W12Loc_euclidean
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
      hR0_pos.le hmap_centered hΩ_meas hclosedBall_subset)
      hs_mem hr_mem hsr

/-- Auxiliary arbitrary-center Euclidean weak increment formula for an already
recentered weak stationary map package. -/
theorem weakTheta_increment_eq_weakMonotonicityRhs_of_centered_W12Loc_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hmap_centered :
      WeakStationaryMapIn
        (fun x : Domain n => u (a + x))
        (translateGradient a Du)
        (centeredDomain a Ω))
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s < r)
    (hr_lt : r < R0) :
    weakTheta Du a r - weakTheta Du a s =
      weakMonotonicityRhs Du a s r := by
  have hzero :
      weakTheta (translateGradient a Du) (0 : Domain n) r -
          weakTheta (translateGradient a Du) (0 : Domain n) s =
        weakMonotonicityRhs (translateGradient a Du) (0 : Domain n) s r :=
    weakTheta_increment_eq_weakMonotonicityRhs_from_W12Loc_euclidean
      (n := n) (m := m)
      (u := fun x : Domain n => u (a + x))
      (Du := translateGradient a Du)
      (Ω := centeredDomain a Ω) (R0 := R0) (s := s) (r := r)
      hmap_centered
      (measurableSet_centeredDomain (a := a) hΩ_meas)
      (closedBall_subset_centeredDomain_of_closedBall_subset
        (a := a) hclosedBall_subset)
      hs_pos hsr hr_lt
  calc
    weakTheta Du a r - weakTheta Du a s
        =
      weakTheta (translateGradient a Du) (0 : Domain n) r -
        weakTheta (translateGradient a Du) (0 : Domain n) s := by
        simp [weakTheta_translateGradient_zero (Du := Du) (a := a)]
    _ =
      weakMonotonicityRhs (translateGradient a Du) (0 : Domain n) s r := hzero
    _ =
      weakMonotonicityRhs Du a s r :=
        weakMonotonicityRhs_translateGradient_zero Du a s r

/-- Frozen public endpoint for the current custom weak interface: arbitrary-
center Euclidean weak monotonicity in interval form, directly from the
original-coordinate weak stationary map package. -/
theorem weakTheta_le_of_arbitrary_center_W12Loc_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s ≤ r)
    (hr_lt : r < R0) :
    weakTheta Du a s ≤ weakTheta Du a r := by
  exact
    weakTheta_le_of_centered_W12Loc_euclidean
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
      (s := s) (r := r)
      (weakStationaryMapIn_centeredDomain (a := a) hmap hΩ_meas)
      hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

/-- Frozen public endpoint for the current custom weak interface: arbitrary-
center Euclidean weak monotonicity formula in increment form, directly from the
original-coordinate weak stationary map package. -/
theorem weakTheta_increment_eq_weakMonotonicityRhs_of_arbitrary_center_W12Loc_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s < r)
    (hr_lt : r < R0) :
    weakTheta Du a r - weakTheta Du a s =
      weakMonotonicityRhs Du a s r :=
  weakTheta_increment_eq_weakMonotonicityRhs_of_centered_W12Loc_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
    (s := s) (r := r)
    (weakStationaryMapIn_centeredDomain (a := a) hmap hΩ_meas)
    hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
