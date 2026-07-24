/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.API

/-!
# Minimal use of the public monotonicity API

This file is intentionally small: it checks that an external caller can import
the public API and apply both the witness-style stationary Sobolev monotonicity
formula/theorem and the older componentwise convenience wrappers.
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

/-- The componentwise calling style remains available as a convenience wrapper
around the witness-style formula. -/
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
    (hsr : s < r)
    (hr_lt : r < R0) :
    weakTheta Du a r - weakTheta Du a s = weakMonotonicityRhs Du a s r :=
  stationarySobolevMonotonicityFormula_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Omega := Omega)
    (a := a) (R0 := R0) (s := s) (r := r)
    hu_memLp hDu_aesm hDu_memLp hweakGradient hfirstVariation
    hOmega_meas hclosedBall_subset hs_pos hsr hr_lt

/-- The componentwise calling style also remains available as a convenience
wrapper around the witness-style inequality theorem. -/
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
    weakTheta Du a s <= weakTheta Du a r :=
  stationarySobolevMonotonicity_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Omega := Omega)
    (a := a) (R0 := R0) (s := s) (r := r)
    hu_memLp hDu_aesm hDu_memLp hweakGradient hfirstVariation
    hOmega_meas hclosedBall_subset hs_pos hsr hr_lt

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
