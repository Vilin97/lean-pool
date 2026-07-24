/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.Monotonicity
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.WeakGradientBridge

/-!
# Sobolev bridge for stationary Sobolev map monotonicity

This module is the controlled entry point for replacing the custom
`WeakStationaryMapIn` hypothesis by progressively more standard Sobolev
interfaces.  The radial monotonicity proof is already frozen in
`weakTheta_le_of_arbitrary_center_W12Loc_euclidean`; bridge modules should prove
that their preferred Sobolev assumptions imply `WeakStationaryMapIn`, then call
that theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- A named Sobolev-style local `W^{1,2}` package for a map with a chosen weak
gradient.  It is split into local `L²` data and the distributional weak-gradient
relation so each part can be replaced by more mathlib-native assumptions
independently. -/
structure SobolevW12LocIn {n m : ℕ}
    (u : Domain n → Target m) (Du : Domain n → Gradient n m)
    (Ω : Set (Domain n)) : Prop where
  l2 : LocalL2DataIn u Du Ω
  weakGradient : DistributionalWeakGradientIn u Du Ω

/-- Constructor for the Sobolev-style package from its natural component
hypotheses: local `L²` control of `u`, local `L²` control and a.e.
measurability of `Du`, and the distributional weak-gradient identity. -/
theorem sobolevW12LocIn_of_components {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (hu_memLp : LocallyMemLpTwoIn u Ω)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Ω)
    (hDu_memLp : LocallyMemLpTwoIn Du Ω)
    (hweakGradient : DistributionalWeakGradientIn u Du Ω) :
    SobolevW12LocIn u Du Ω :=
  ⟨⟨hu_memLp, ⟨hDu_aesm, hDu_memLp⟩⟩, hweakGradient⟩

/-- The bridge from the Sobolev-style package to the custom weak `W^{1,2}_{loc}`
interface used by the proved monotonicity theorem. -/
theorem SobolevW12LocIn.toW12LocIn {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : SobolevW12LocIn u Du Ω) :
    W12LocIn u Du Ω :=
  ⟨h.l2.toMapLocallyL2In, h.l2.toGradientAEStronglyMeasurableIn,
    h.l2.toGradientLocallyL2In, h.weakGradient.toHasWeakGradientIn⟩

/-- A Sobolev-style weak stationary map package: local `W^{1,2}` control plus
the domain-variation stationarity identity. -/
structure SobolevWeakStationaryMapIn {n m : ℕ}
    (u : Domain n → Target m) (Du : Domain n → Gradient n m)
    (Ω : Set (Domain n)) : Prop where
  sobolev : SobolevW12LocIn u Du Ω
  stationary : WeakStationaryIn Du Ω

/-- The bridge from the Sobolev-style stationary package to the custom weak
stationary package used by the monotonicity theorem. -/
theorem SobolevWeakStationaryMapIn.toWeakStationaryMapIn {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : SobolevWeakStationaryMapIn u Du Ω) :
    WeakStationaryMapIn u Du Ω :=
  ⟨h.sobolev.toW12LocIn, h.stationary⟩

/-- Arbitrary-center Euclidean weak monotonicity from the Sobolev bridge
package.  This theorem is the next public entry point above
`WeakStationaryMapIn`: all monotonicity work is delegated to the frozen endpoint
in `Monotonicity.lean`. -/
theorem weakTheta_le_of_sobolev_bridge_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hmap : SobolevWeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s ≤ r)
    (hr_lt : r < R0) :
    weakTheta Du a s ≤ weakTheta Du a r := by
  exact
    weakTheta_le_of_arbitrary_center_W12Loc_euclidean
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
      (s := s) (r := r)
      hmap.toWeakStationaryMapIn hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

/-- Convenience variant when the Sobolev local package and stationarity
identity are supplied separately. -/
theorem weakTheta_le_of_sobolev_bridge_euclidean'
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hsob : SobolevW12LocIn u Du Ω)
    (hstationary : WeakStationaryIn Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s ≤ r)
    (hr_lt : r < R0) :
    weakTheta Du a s ≤ weakTheta Du a r :=
  weakTheta_le_of_sobolev_bridge_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
    (s := s) (r := r)
    ⟨hsob, hstationary⟩ hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
