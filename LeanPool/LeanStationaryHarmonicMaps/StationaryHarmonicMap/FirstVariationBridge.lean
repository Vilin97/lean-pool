/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.WeakGradientBridge

/-!
# First-variation bridge

This module gives the domain-variation stationarity identity a paper-facing
name.  The integrand is the current weak-gradient stress-energy integrand; the
map `u` is included in the package parameters so the statement reads like a
stationary Sobolev map hypothesis, even though the formula only depends on
`Du`.  Vector-field variations use the same bundled compactly supported `C¹`
test-function interface as the distributional weak-gradient bridge.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Vanishing domain-variation first variation for a Sobolev map with chosen
weak gradient. -/
structure DomainVariationStationaryIn {n m : ℕ}
    (u : Domain n → Target m) (Du : Domain n → Gradient n m)
    (Ω : Set (Domain n)) : Prop where
  firstVariation_zero :
    ∀ X : CompactlySupportedC1In Ω (Domain n),
      (∫ x in Ω, weakStationarityIntegrand Du X x) = 0

/-- Domain-variation stationarity implies the custom weak stationarity
interface used by the monotonicity proof. -/
theorem DomainVariationStationaryIn.toWeakStationaryIn {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : DomainVariationStationaryIn u Du Ω) :
    WeakStationaryIn Du Ω := by
  intro X hX hX_compact hX_support
  exact
    h.firstVariation_zero
      { toFun := X
        contDiff := hX
        hasCompactSupport := hX_compact
        tsupport_subset := hX_support }

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
