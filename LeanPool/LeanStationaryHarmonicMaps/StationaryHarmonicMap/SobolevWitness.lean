/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.SobolevBridge

/-!
# Sobolev witnesses

This file is the DGM-style Sobolev witness layer.  It bundles a map together
with the displayed weak gradient and the local `W^{1,2}` data needed by the
monotonicity proof.

No stationarity or monotonicity theorem is defined here; those live in
`StationaryMap.lean` and `MainTheorem.lean`.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- A local `W^{1,2}` witness for a map, carrying the chosen weak gradient.

This is intentionally a `Type`, not a `Prop`: the weak gradient is data that the
public monotonicity theorem must use in the monotonicity quantity. -/
structure W12LocMapWitness {n m : Nat}
    (u : Domain n -> Target m) (Omega : Set (Domain n)) where
  /-- The displayed weak gradient. -/
  weakGrad : Domain n -> Gradient n m
  /-- Local `L^2` control of the map. -/
  map_memLpTwo_loc : LocallyMemLpTwoIn u Omega
  /-- A.e. strong measurability of the displayed weak gradient. -/
  grad_aestronglyMeasurable : GradientAEStronglyMeasurableIn weakGrad Omega
  /-- Local `L^2` control of the displayed weak gradient. -/
  grad_memLpTwo_loc : LocallyMemLpTwoIn weakGrad Omega
  /-- The displayed gradient is the distributional weak gradient of the map. -/
  isWeakGradient : DistributionalWeakGradientIn u weakGrad Omega

namespace W12LocMapWitness

/-- Build a local Sobolev witness from its component hypotheses. -/
def ofComponents {n m : Nat}
    {u : Domain n -> Target m} {Du : Domain n -> Gradient n m}
    {Omega : Set (Domain n)}
    (hu_memLp : LocallyMemLpTwoIn u Omega)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Omega)
    (hDu_memLp : LocallyMemLpTwoIn Du Omega)
    (hweakGradient : DistributionalWeakGradientIn u Du Omega) :
    W12LocMapWitness u Omega where
  weakGrad := Du
  map_memLpTwo_loc := hu_memLp
  grad_aestronglyMeasurable := hDu_aesm
  grad_memLpTwo_loc := hDu_memLp
  isWeakGradient := hweakGradient

/-- Forget the explicit witness package to the earlier Sobolev bridge. -/
theorem toSobolevW12LocIn {n m : Nat}
    {u : Domain n -> Target m} {Omega : Set (Domain n)}
    (h : W12LocMapWitness u Omega) :
    SobolevW12LocIn u h.weakGrad Omega :=
  sobolevW12LocIn_of_components
    h.map_memLpTwo_loc h.grad_aestronglyMeasurable h.grad_memLpTwo_loc
    h.isWeakGradient

/-- Forget the explicit witness package to the custom weak `W^{1,2}_{loc}`
interface used internally by the monotonicity proof. -/
theorem toW12LocIn {n m : Nat}
    {u : Domain n -> Target m} {Omega : Set (Domain n)}
    (h : W12LocMapWitness u Omega) :
    W12LocIn u h.weakGrad Omega :=
  h.toSobolevW12LocIn.toW12LocIn

end W12LocMapWitness

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
