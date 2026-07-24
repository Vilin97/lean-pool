/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.SobolevWitness
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.StationarityBridge

/-!
# Stationary Sobolev map package

This file adds stationarity to the Sobolev witness layer.  The package is the
paper-facing input for the monotonicity theorem: a local Sobolev map with an
explicit weak gradient, plus vanishing domain first variation.

The target-manifold constraint is intentionally absent.  The monotonicity proof
uses only this stationary package.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- A stationary local `W^{1,2}` map witness.

The stationarity field is exactly the domain-variation first-variation
identity. No target-manifold structure is used by the monotonicity proof. -/
structure StationaryW12LocMap {n m : Nat}
    (u : Domain n -> Target m) (Omega : Set (Domain n)) where
  /-- Sobolev data together with the displayed weak gradient. -/
  w12 : W12LocMapWitness u Omega
  /-- Vanishing domain first variation for the displayed weak gradient. -/
  stationary : DomainVariationStationaryIn u w12.weakGrad Omega

namespace StationaryW12LocMap

/-- Build a stationary Sobolev witness from component hypotheses. -/
def ofComponents {n m : Nat}
    {u : Domain n -> Target m} {Du : Domain n -> Gradient n m}
    {Omega : Set (Domain n)}
    (hu_memLp : LocallyMemLpTwoIn u Omega)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Omega)
    (hDu_memLp : LocallyMemLpTwoIn Du Omega)
    (hweakGradient : DistributionalWeakGradientIn u Du Omega)
    (hfirstVariation : DomainVariationStationaryIn u Du Omega) :
    StationaryW12LocMap u Omega where
  w12 :=
    W12LocMapWitness.ofComponents
      (u := u) (Du := Du) (Omega := Omega)
      hu_memLp hDu_aesm hDu_memLp hweakGradient
  stationary := hfirstVariation

/-- Forget the witness package to the earlier paper-facing stationary Sobolev
package. -/
theorem toStationarySobolevMapIn {n m : Nat}
    {u : Domain n -> Target m} {Omega : Set (Domain n)}
    (h : StationaryW12LocMap u Omega) :
    StationarySobolevMapIn u h.w12.weakGrad Omega :=
  ⟨h.w12.toSobolevW12LocIn, h.stationary⟩

/-- Forget the witness package to the custom weak stationary map interface used
inside the proof. -/
theorem toWeakStationaryMapIn {n m : Nat}
    {u : Domain n -> Target m} {Omega : Set (Domain n)}
    (h : StationaryW12LocMap u Omega) :
    WeakStationaryMapIn u h.w12.weakGrad Omega :=
  h.toStationarySobolevMapIn.toWeakStationaryMapIn

end StationaryW12LocMap

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
