/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.SobolevBridge
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.FirstVariationBridge

/-!
# Stationarity bridge for the monotonicity theorem

This module provides a paper-facing package name for stationary Sobolev maps.
Its first-variation field is now the paper-facing
`DomainVariationStationaryIn u Du Ω`, whose vector-field variations are bundled
compactly supported `C¹` tests. It bridges to the custom `WeakStationaryIn Du Ω`
interface used by the proved monotonicity theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Paper-facing stationary Sobolev map package.

It consists of the local Sobolev bridge package together with vanishing
domain-variation first variation. -/
structure StationarySobolevMapIn {n m : ℕ}
    (u : Domain n → Target m) (Du : Domain n → Gradient n m)
    (Ω : Set (Domain n)) : Prop where
  sobolev : SobolevW12LocIn u Du Ω
  firstVariation_zero : DomainVariationStationaryIn u Du Ω

/-- Constructor for the final stationary Sobolev package from the five natural
inputs used by the monotonicity proof: local `L²` control of the map, a.e.
measurability and local `L²` control of the weak gradient, the distributional
weak-gradient identity, and vanishing domain first variation. -/
theorem stationarySobolevMapIn_of_components {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (hu_memLp : LocallyMemLpTwoIn u Ω)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Ω)
    (hDu_memLp : LocallyMemLpTwoIn Du Ω)
    (hweakGradient : DistributionalWeakGradientIn u Du Ω)
    (hfirstVariation : DomainVariationStationaryIn u Du Ω) :
    StationarySobolevMapIn u Du Ω :=
  ⟨sobolevW12LocIn_of_components hu_memLp hDu_aesm hDu_memLp hweakGradient,
    hfirstVariation⟩

/-- A stationary Sobolev map is a Sobolev weak stationary map in the bridge
interface. -/
theorem StationarySobolevMapIn.toSobolevWeakStationaryMapIn {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : StationarySobolevMapIn u Du Ω) :
    SobolevWeakStationaryMapIn u Du Ω :=
  ⟨h.sobolev, h.firstVariation_zero.toWeakStationaryIn⟩

/-- A stationary Sobolev map is a custom weak stationary map, after unpacking
the bundled Sobolev and first-variation bridge data. -/
theorem StationarySobolevMapIn.toWeakStationaryMapIn {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : StationarySobolevMapIn u Du Ω) :
    WeakStationaryMapIn u Du Ω :=
  h.toSobolevWeakStationaryMapIn.toWeakStationaryMapIn

/-- Final paper-facing arbitrary-center Euclidean monotonicity theorem for the
current stationary Sobolev bridge package. -/
theorem weakTheta_le_of_stationary_sobolev_map_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hmap : StationarySobolevMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s ≤ r)
    (hr_lt : r < R0) :
    weakTheta Du a s ≤ weakTheta Du a r :=
  weakTheta_le_of_arbitrary_center_W12Loc_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
    (s := s) (r := r)
    hmap.toWeakStationaryMapIn hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

/-- Final paper-facing arbitrary-center Euclidean monotonicity formula for the
current stationary Sobolev bridge package. -/
theorem weakTheta_increment_eq_weakMonotonicityRhs_of_stationary_sobolev_map_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hmap : StationarySobolevMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s < r)
    (hr_lt : r < R0) :
    weakTheta Du a r - weakTheta Du a s =
      weakMonotonicityRhs Du a s r :=
  weakTheta_increment_eq_weakMonotonicityRhs_of_arbitrary_center_W12Loc_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
    (s := s) (r := r)
    hmap.toWeakStationaryMapIn hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

/-- Final componentwise entry point: the monotonicity theorem stated directly
from the five stationary `W^{1,2}_{loc}` hypotheses, without asking callers to
manually assemble the intermediate packages. -/
theorem weakTheta_le_of_stationary_sobolev_map_components_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hu_memLp : LocallyMemLpTwoIn u Ω)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Ω)
    (hDu_memLp : LocallyMemLpTwoIn Du Ω)
    (hweakGradient : DistributionalWeakGradientIn u Du Ω)
    (hfirstVariation : DomainVariationStationaryIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s ≤ r)
    (hr_lt : r < R0) :
    weakTheta Du a s ≤ weakTheta Du a r :=
  weakTheta_le_of_stationary_sobolev_map_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
    (s := s) (r := r)
    (stationarySobolevMapIn_of_components
      hu_memLp hDu_aesm hDu_memLp hweakGradient hfirstVariation)
    hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

/-- Final componentwise entry point for the monotonicity increment formula,
stated directly from the five stationary `W^{1,2}_{loc}` hypotheses. -/
theorem weakTheta_increment_eq_weakMonotonicityRhs_of_stationary_sobolev_map_components_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hu_memLp : LocallyMemLpTwoIn u Ω)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Ω)
    (hDu_memLp : LocallyMemLpTwoIn Du Ω)
    (hweakGradient : DistributionalWeakGradientIn u Du Ω)
    (hfirstVariation : DomainVariationStationaryIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s < r)
    (hr_lt : r < R0) :
    weakTheta Du a r - weakTheta Du a s =
      weakMonotonicityRhs Du a s r :=
  weakTheta_increment_eq_weakMonotonicityRhs_of_stationary_sobolev_map_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
    (s := s) (r := r)
    (stationarySobolevMapIn_of_components
      hu_memLp hDu_aesm hDu_memLp hweakGradient hfirstVariation)
    hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
