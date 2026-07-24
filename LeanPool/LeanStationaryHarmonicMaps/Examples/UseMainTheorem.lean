/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.MainTheorem

/-!
# Using the main theorem directly

This example imports only `MainTheorem.lean`.  A caller supplies a
`StationaryW12LocMap` package and immediately obtains both the monotonicity
formula and the monotonicity inequality for the weak energy density associated
with the package's displayed weak gradient.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

example
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
  stationaryW12LocMonotonicityFormula_euclidean
    (n := n) (m := m) (u := u) (Omega := Omega) hmap
    (a := a) (R0 := R0) (s := s) (r := r)
    hOmega_meas hclosedBall_subset hs_pos hsr hr_lt

example
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
  stationaryW12LocMonotonicity_euclidean
    (n := n) (m := m) (u := u) (Omega := Omega) hmap
    (a := a) (R0 := R0) (s := s) (r := r)
    hOmega_meas hclosedBall_subset hs_pos hsr hr_lt

/-- Component hypotheses can still be assembled into the package expected by
the main theorem. -/
example
    {n m : Nat} [NeZero n]
    {u : Domain n -> Target m} {Du : Domain n -> Gradient n m}
    {Omega : Set (Domain n)} {a : Domain n} {R0 s r : Real}
    (hu_memLp : LocallyMemLpTwoIn u Omega)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Omega)
    (hDu_memLp : LocallyMemLpTwoIn Du Omega)
    (hweakGradient : DistributionalWeakGradientIn u Du Omega)
    (hfirstVariation : DomainVariationStationaryIn u Du Omega)
    (hOmega_meas : MeasurableSet Omega)
    (hclosedBall_subset : Set.Subset (Metric.closedBall a R0) Omega)
    (hs_pos : 0 < s)
    (hsr : s <= r)
    (hr_lt : r < R0) :
    weakTheta Du a s <= weakTheta Du a r := by
  let hmap : StationaryW12LocMap u Omega :=
    StationaryW12LocMap.ofComponents
      (u := u) (Du := Du) (Omega := Omega)
      hu_memLp hDu_aesm hDu_memLp hweakGradient hfirstVariation
  exact
    stationaryW12LocMonotonicity_euclidean
      (n := n) (m := m) (u := u) (Omega := Omega) hmap
      (a := a) (R0 := R0) (s := s) (r := r)
      hOmega_meas hclosedBall_subset hs_pos hsr hr_lt

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
