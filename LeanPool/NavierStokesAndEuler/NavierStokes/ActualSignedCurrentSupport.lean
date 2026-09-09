/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCyclePreservation
public import LeanPool.NavierStokesAndEuler.NavierStokes.CurrentSignedCurl

@[expose] public section

/-!
# Omitted labels in the actual current signed fields

The current potential and pressure are constructed from the same signed
copy sum as the correction cycle.  Their support implies membership in the
actual active-label set, before any physical pullback or finite sum.
-/

noncomputable section

namespace NavierStokes.ActualSignedCurrentSupport

open Set Function Filter CorrectionState CorrectionStep HarmonicCalculus
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

abbrev Point := ActualSignedCoherence.Point
abbrev FullPoint := ActualSignedCoherence.FullPoint
abbrev Index := ActualInitialization.Index

variable {B N0 : ℕ}

theorem outside_core (l : Index B N0) (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    x ∉ ActualCoreSupport.refinedCarrier l n :=
  fun hc => hn (ActualCyclePreservation.core_active l n hx hc)

/-- Zero values of the literal common coefficient, with arbitrary current
state and no smoothness or residual bound hypothesis. -/
theorem common_zero (l : Index B N0) (u : State Point) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    (ActualSignedCoherence.copies l u).common.amplitude n x = 0 ∧
      (ActualSignedCoherence.copies l u).common.pressure n x = 0 :=
  ActualCycleAssembly.refined_signed_common_zero l ActualInitialization.geometry.strip
    (ActualSignedCoherence.request B u) n hx (outside_core l n hx hn)

theorem potentialCoefficient_zero (l : Index B N0) (u : State Point) (n : ℕ)
    {x : FullPoint} (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    ActualSignedPotentialCoherence.potentialCoefficient l u n x = 0 := by
  simp only [ActualSignedPotentialCoherence.potentialCoefficient, (common_zero l u n hx hn).1,
    CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross, map_zero, smul_zero]

theorem potential_zero (l : Index B N0) (u : State Point) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    ActualSignedPotentialCoherence.potential l u n x = 0 := by
  rw [ActualSignedPotentialCoherence.potential_eq_mode]
  funext i
  simp only [vectorMode, mode, potentialCoefficient_zero l u n hx hn, Pi.zero_apply, zero_mul]

theorem pressureMode_zero (l : Index B N0) (u : State Point) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    ActualSignedPotentialCoherence.pressureMode l u n x = 0 := by
  simp only [ActualSignedPotentialCoherence.pressureMode, mode,
    (common_zero l u n hx hn).2, zero_mul]

theorem native_zero_germs (l : Index B N0) (u : State Point) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    (ActualSignedPotentialCoherence.potential l u n =ᶠ[𝓝 x] fun _ => 0) ∧
      (ActualSignedPotentialCoherence.pressureMode l u n =ᶠ[𝓝 x] fun _ => 0) := by
  have hU : {y : FullPoint | y.1 ∈ ActualInitialization.geometry.domain} ∈ 𝓝 x :=
    (ActualInitialization.geometry.domain_open.preimage continuous_fst).mem_nhds hx
  constructor
  · filter_upwards [hU] with y hy
    exact potential_zero l u n hy hn
  · filter_upwards [hU] with y hy
    exact pressureMode_zero l u n hy hn

theorem cylindrical_zero (l : Index B N0) (u : State Point) (n : ℕ)
    {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualSignedPotentialCoherence.physicalDomain n)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    ActualSignedPotentialCoherence.cylindricalPotential l u n z = 0 ∧
      ActualSignedPotentialCoherence.cylindricalPressureMode l u n z = 0 := by
  constructor
  · simp only [ActualSignedPotentialCoherence.cylindricalPotential,
      ActualSignedPotentialCoherence.rescaledPotential, potential_zero l u n hz.2 hn, smul_zero]
  · simp only [ActualSignedPotentialCoherence.cylindricalPressureMode,
      ActualSignedPotentialCoherence.rescaledPressureMode, pressureMode_zero l u n hz.2 hn,
        smul_zero]

theorem physicalDomain_of_source (n : ℕ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.source n) :
    z ∈ ActualSignedPotentialCoherence.physicalDomain n :=
  ⟨hz.1, (CurrentSignedCurl.nativePoint_mem n hz).1.1⟩

theorem currentPotential_zero (l : Index B N0) (u : State Point) (n : ℕ)
    {qbig a : ℝ} {i : PolarCharts.Index} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    CurrentSignedCurl.currentPotential l u n a i z = 0 := by
  have hp := (cylindrical_zero l u n (physicalDomain_of_source n hz.2.2) hn).1
  have hzero : PhysicalCurlCovariance.realVector (0 : ComplexVector) = 0 := by
    ext j
    simp
  simp only [CurrentSignedCurl.currentPotential, PhysicalCurlCovariance.cartesianPotential,
    hp, hzero, map_zero]

theorem currentPressure_zero (l : Index B N0) (u : State Point) (n : ℕ)
    {qbig a : ℝ} {i : PolarCharts.Index} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    CurrentSignedCurl.currentPressure l u n a i z = 0 := by
  have hp := (cylindrical_zero l u n (physicalDomain_of_source n hz.2.2) hn).2
  simp only [CurrentSignedCurl.currentPressure, hp, Complex.zero_re]

theorem currentPotential_zero_germ (l : Index B N0) (u : State Point) (n : ℕ)
    {qbig a : ℝ} (ha : 0 < a) {i : PolarCharts.Index} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    CurrentSignedCurl.currentPotential l u n a i =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [(ActualPhysicalPrefixFields.cartesianChartDomain_open qbig n ha i).mem_nhds hz]
    with w hw
  exact currentPotential_zero l u n hw hn

theorem currentPressure_zero_germ (l : Index B N0) (u : State Point) (n : ℕ)
    {qbig a : ℝ} (ha : 0 < a) {i : PolarCharts.Index} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    CurrentSignedCurl.currentPressure l u n a i =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [(ActualPhysicalPrefixFields.cartesianChartDomain_open qbig n ha i).mem_nhds hz]
    with w hw
  exact currentPressure_zero l u n hw hn

/-! ## The canonical sum is the finite current active-label sum -/

theorem finsum_eq_active_sum {E : Type*} [AddCommMonoid E] (n : ℕ)
    (f : Index B N0 → E)
    (hz : ∀ l, l ∉ activeLabels standardRegion B N0 n → f l = 0) :
    (∑ᶠ l, f l) = ∑ l ∈ activeLabels standardRegion B N0 n, f l := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro l hl
  by_contra hn
  exact hl (hz l hn)

theorem finsum_eq_labels_sum {E : Type*} [AddCommMonoid E]
    (v : CycleCoefficients (Index B N0))
    (hv : v.labels = activeLabels standardRegion B N0) (n : ℕ)
    (f : Index B N0 → E)
    (hz : ∀ l, l ∉ activeLabels standardRegion B N0 n → f l = 0) :
    (∑ᶠ l, f l) = ∑ l ∈ v.labels n, f l := by
  rw [hv]
  exact finsum_eq_active_sum n f hz

theorem potential_finsum (u : State Point) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ ActualInitialization.geometry.domain) :
    (∑ᶠ l : Index B N0, ActualSignedPotentialCoherence.potential l u n x) =
      ∑ l ∈ activeLabels standardRegion B N0 n, ActualSignedPotentialCoherence.potential l u n x :=
  finsum_eq_active_sum n _ (fun l hn => potential_zero l u n hx hn)

theorem pressureMode_finsum (u : State Point) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ ActualInitialization.geometry.domain) :
    (∑ᶠ l : Index B N0, ActualSignedPotentialCoherence.pressureMode l u n x) =
      ∑ l ∈ activeLabels standardRegion B N0 n, ActualSignedPotentialCoherence.pressureMode l u n x
        :=
  finsum_eq_active_sum n _ (fun l hn => pressureMode_zero l u n hx hn)

theorem currentPotential_finsum (u : State Point) (n : ℕ)
    {qbig a : ℝ} {i : PolarCharts.Index} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    (∑ᶠ l : Index B N0, CurrentSignedCurl.currentPotential l u n a i z) =
      ∑ l ∈ activeLabels standardRegion B N0 n, CurrentSignedCurl.currentPotential l u n a i z :=
  finsum_eq_active_sum n _ (fun l hn => currentPotential_zero l u n hz hn)

theorem currentPressure_finsum (u : State Point) (n : ℕ)
    {qbig a : ℝ} {i : PolarCharts.Index} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    (∑ᶠ l : Index B N0, CurrentSignedCurl.currentPressure l u n a i z) =
      ∑ l ∈ activeLabels standardRegion B N0 n, CurrentSignedCurl.currentPressure l u n a i z :=
  finsum_eq_active_sum n _ (fun l hn => currentPressure_zero l u n hz hn)

theorem currentPotential_finsum_germ (u : State Point) (n : ℕ)
    {qbig a : ℝ} (ha : 0 < a) {i : PolarCharts.Index} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    (fun w => ∑ᶠ l : Index B N0, CurrentSignedCurl.currentPotential l u n a i w) =ᶠ[𝓝 z]
      fun w => ∑ l ∈ activeLabels standardRegion B N0 n, CurrentSignedCurl.currentPotential l u n a
        i w := by
  filter_upwards [(ActualPhysicalPrefixFields.cartesianChartDomain_open qbig n ha i).mem_nhds hz]
    with w hw
  exact currentPotential_finsum u n hw

theorem currentPressure_finsum_germ (u : State Point) (n : ℕ)
    {qbig a : ℝ} (ha : 0 < a) {i : PolarCharts.Index} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    (fun w => ∑ᶠ l : Index B N0, CurrentSignedCurl.currentPressure l u n a i w) =ᶠ[𝓝 z]
      fun w => ∑ l ∈ activeLabels standardRegion B N0 n, CurrentSignedCurl.currentPressure l u n a
        i w := by
  filter_upwards [(ActualPhysicalPrefixFields.cartesianChartDomain_open qbig n ha i).mem_nhds hz]
    with w hw
  exact currentPressure_finsum u n hw

theorem current_finsums_eq_labels (u : State Point) (v : CycleCoefficients (Index B N0))
    (hv : v.labels = activeLabels standardRegion B N0) (n : ℕ)
    {qbig a : ℝ} {i : PolarCharts.Index} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    (∑ᶠ l : Index B N0, CurrentSignedCurl.currentPotential l u n a i z) =
        ∑ l ∈ v.labels n, CurrentSignedCurl.currentPotential l u n a i z ∧
      (∑ᶠ l : Index B N0, CurrentSignedCurl.currentPressure l u n a i z) =
        ∑ l ∈ v.labels n, CurrentSignedCurl.currentPressure l u n a i z := by
  rw [hv]
  exact ⟨currentPotential_finsum u n hz, currentPressure_finsum u n hz⟩

end NavierStokes.ActualSignedCurrentSupport
