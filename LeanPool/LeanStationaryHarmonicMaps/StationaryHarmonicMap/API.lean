/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.Euclidean
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.MainTheorem

/-!
# Public API for stationary Sobolev map monotonicity

This module is the intended public entry point for the stationary
`W^{1,2}_{loc}` monotonicity theorem.  The proof is target independent: it
uses the displayed weak gradient and the domain-variation first-variation
identity, but no target-manifold structure.

The main user-facing objects are:

* `LocallyMemLpTwoIn`
* `GradientLocallyMemLpTwoIn`
* `CompactlySupportedC1In`
* `DistributionalWeakGradientIn`
* `DomainVariationStationaryIn`
* `W12LocMapWitness`
* `StationaryW12LocMap`
* `stationaryW12LocMonotonicityFormula_euclidean`
* `stationaryW12LocMonotonicity_euclidean`
* `stationarySobolevMonotonicityFormula_euclidean`
* `stationarySobolevMonotonicity_euclidean`

Implementation-route theorems in the radial/coarea files should normally be
treated as internal scaffolding.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Componentwise convenience wrapper for the witness-style monotonicity
formula.

The preferred public API is `stationaryW12LocMonotonicityFormula_euclidean`,
where the chosen weak gradient is bundled in a `StationaryW12LocMap`.  This
theorem keeps the old componentwise calling style by constructing that witness
package first. -/
theorem stationarySobolevMonotonicityFormula_euclidean
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
    weakTheta Du a r - weakTheta Du a s =
      weakMonotonicityRhs Du a s r :=
  stationaryW12LocMonotonicityFormula_euclidean
    (n := n) (m := m) (u := u) (Omega := Omega)
    (StationaryW12LocMap.ofComponents
      (u := u) (Du := Du) (Omega := Omega)
      hu_memLp hDu_aesm hDu_memLp hweakGradient hfirstVariation)
    (a := a) (R0 := R0) (s := s) (r := r)
    hOmega_meas hclosedBall_subset hs_pos hsr hr_lt

/-- Componentwise convenience wrapper for the witness-style monotonicity
theorem.

The preferred public API is `stationaryW12LocMonotonicity_euclidean`, where the
chosen weak gradient is bundled in a `StationaryW12LocMap`.  This theorem keeps
the old componentwise calling style by constructing that witness package first. -/
theorem stationarySobolevMonotonicity_euclidean
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
  stationaryW12LocMonotonicity_euclidean
    (n := n) (m := m) (u := u) (Omega := Omega)
    (StationaryW12LocMap.ofComponents
      (u := u) (Du := Du) (Omega := Omega)
      hu_memLp hDu_aesm hDu_memLp hweakGradient hfirstVariation)
    (a := a) (R0 := R0) (s := s) (r := r)
    hOmega_meas hclosedBall_subset hs_pos hsr hr_lt

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
