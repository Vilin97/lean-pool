/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.StationaryMap

/-!
# Main monotonicity theorem

This file exports the witness-style public theorem.  All radial, coarea,
cutoff, and boundary routes are internal scaffolding hidden behind the
stationary Sobolev map package.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Main witness-style public monotonicity formula.

This is the equality form of the monotonicity theorem: the increment of
`weakTheta` is the nonnegative annular radial-energy term
`weakMonotonicityRhs`. -/
theorem stationaryW12LocMonotonicityFormula_euclidean
    {n m : Nat} [NeZero n]
    {u : Domain n -> Target m} {Omega : Set (Domain n)}
    (hmap : StationaryW12LocMap u Omega)
    {a : Domain n} {R0 s r : Real}
    (hOmega_meas : MeasurableSet Omega)
    (hclosedBall_subset : Set.Subset (Metric.closedBall a R0) Omega)
    (hs_pos : 0 < s)
    (hsr : s < r)
    (hr_lt : r < R0) :
    weakTheta hmap.w12.weakGrad a r - weakTheta hmap.w12.weakGrad a s =
      weakMonotonicityRhs hmap.w12.weakGrad a s r :=
  weakTheta_increment_eq_weakMonotonicityRhs_of_stationary_sobolev_map_euclidean
    (n := n) (m := m) (u := u) (Du := hmap.w12.weakGrad)
    (a := a) (R0 := R0) (s := s) (r := r)
    hmap.toStationarySobolevMapIn hOmega_meas hclosedBall_subset
    hs_pos hsr hr_lt

/-- Main witness-style public monotonicity theorem.

The chosen weak gradient is part of the stationary Sobolev witness, and the
conclusion uses that same gradient in `weakTheta`. -/
theorem stationaryW12LocMonotonicity_euclidean
    {n m : Nat} [NeZero n]
    {u : Domain n -> Target m} {Omega : Set (Domain n)}
    (hmap : StationaryW12LocMap u Omega)
    {a : Domain n} {R0 s r : Real}
    (hOmega_meas : MeasurableSet Omega)
    (hclosedBall_subset : Set.Subset (Metric.closedBall a R0) Omega)
    (hs_pos : 0 < s)
    (hsr : s <= r)
    (hr_lt : r < R0) :
    weakTheta hmap.w12.weakGrad a s <= weakTheta hmap.w12.weakGrad a r :=
  weakTheta_le_of_stationary_sobolev_map_euclidean
    (n := n) (m := m) (u := u) (Du := hmap.w12.weakGrad)
    (a := a) (R0 := R0) (s := s) (r := r)
    hmap.toStationarySobolevMapIn hOmega_meas hclosedBall_subset
    hs_pos hsr hr_lt

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
