/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentParticularPhysical
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhysicalPrefixFields

@[expose] public section

/-!
# The Cartesian curl of the actual finite particular-wave sum

The potential and pressure are the literal current-band sums constructed in
`ActualCurrentParticularPhysical`.  Their modes are identified with the same
canonical solver used by the correction cycle.  On a valid current polar chart,
the curl is therefore the actual particular velocity increment, with its physical
scale and moving frame.  No output representation is an input to these identities.
-/

noncomputable section

namespace NavierStokes.ActualCurrentParticularAssembly

open Set Function Filter ProblemStatement CorrectionState CorrectionStep CorrectionInitialization
open ActualCurrentParticularPhysical
open scoped ContDiff Topology BigOperators


variable {B N0 : ℕ}

theorem space_sum_apply {ι : Type*} (s : Finset ι) (v : ι → Space) (k : Fin 3) :
    (∑ b ∈ s, v b) k = ∑ b ∈ s, v b k :=
  map_sum (PiLp.proj 2 (fun _ : Fin 3 => ℝ) k : Space →L[ℝ] ℝ) v s

theorem localPotential_eq_sum (x : CycleState (ActualInitialization.Index B N0)) (n : ℕ) :
    localPotential (ActualCycleParameters.particularState x) n = fun w =>
      ∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        localPotentialMode (ActualCycleParameters.particularState x) (l.2,l.1) j n w := by
  classical
  funext w
  simp only [localPotential, ActualCycleParameters.particularState,
    ActualCycleParameters.reindexState, ActualCycleParameters.reindexCoefficients,
    Equiv.symm_symm, Finset.sum_map, Equiv.toEmbedding_apply,
    ActualCycleParameters.swap_apply]

theorem localPressure_eq_sum (x : CycleState (ActualInitialization.Index B N0)) (n : ℕ) :
    localPressure (ActualCycleParameters.particularState x) n = fun w =>
      ∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        localPressureMode (ActualCycleParameters.particularState x) (l.2,l.1) j n w := by
  classical
  funext w
  simp only [localPressure, ActualCycleParameters.particularState,
    ActualCycleParameters.reindexState, ActualCycleParameters.reindexCoefficients,
    Equiv.symm_symm, Finset.sum_map, Equiv.toEmbedding_apply,
    ActualCycleParameters.swap_apply]

theorem nativeMode_eq (x : CycleState (ActualInitialization.Index B N0))
    (l : ActualInitialization.Index B N0) (j : ℤ) (n : ℕ)
    (z : PhysicalResidualBridge.Cylinder) (k : Fin 3) :
    ActualParticularCycleData.nativeMode x l j n z k =
      (nativeVelocity (ActualCycleParameters.particularState x) (l.2,l.1) j n
        (ActualWaveRegularity.particularChart z) k).re := rfl

theorem particularVelocity_eq_sum {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x) (n : ℕ)
    (z : PhysicalResidualBridge.Cylinder) (k : Fin 3) :
    (ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
        (CorrectionInitialization.ActualPrimary.commonContext B) x.state n z k =
      ∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        (nativeVelocity (ActualCycleParameters.particularState x) (l.2,l.1) j n
          (ActualWaveRegularity.particularChart z) k).re := by
  classical
  change (∑ l ∈ x.coefficients.labels n, (ActualParticularCycleData.block x l).oscillation n z k) =
    _
  apply Finset.sum_congr rfl
  intro l _
  rw [ActualParticularCycleData.block_eq_modes H l]
  rfl

theorem particularPressure_eq_sum {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x) (n : ℕ)
    (z : PhysicalResidualBridge.Cylinder) :
    (ActualCycleParameters.fixedParameters B N0).particularPressure x.coefficients
        (CorrectionInitialization.ActualPrimary.commonContext B) x.state n z =
      ∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        (nativePressure (ActualCycleParameters.particularState x) (l.2,l.1) j n
          (ActualWaveRegularity.particularChart z)).re := by
  classical
  change (∑ l ∈ x.coefficients.labels n, (ActualParticularCycleData.block x l).oscillatoryPressure
    n z) = _
  apply Finset.sum_congr rfl
  intro l _
  rw [ActualParticularCycleData.particularBlock_pressure_eq_modes _ _ _ _ _ (H.frequency l)]
  rfl

theorem nativeMap_eq_graph (n : ℕ) (z : SpaceTime) :
    PhysicalParticularWave.nativeMap CorrectionInitialization.ActualPrimary.h
      (ChartScales.Q n) (CommonWindow.index CorrectionInitialization.ActualPrimary.h n) z =
    ActualWaveRegularity.particularChart
      (PhysicalResidualTZ.graphMapTZ (ActualCycleResidualBounds.actualBandGraph n) z) := rfl

theorem velocityMap_apply (n : ℕ) (v : PhysicalResidualBridge.Cylinder → Fin 3 → ℝ)
    (z : SpaceTime) (k : Fin 3) :
    CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n) v z k =
      (ChartScales.Q n) ^ (-CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
        v (PhysicalResidualTZ.graphMapTZ (ActualCycleResidualBounds.actualBandGraph n) z) k := by
  change (ActualCycleResidualBounds.actualBandGraph n).velocity
    (fun x => v (PhysicalResidualTZ.swapCylinder x)) z k = _
  rw [PhysicalResidualBridge.ScaledGraph.velocity_apply]
  rfl

theorem pressureMap_apply (n : ℕ) (p : PhysicalResidualBridge.Cylinder → ℝ) (z : SpaceTime) :
    CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n) p z =
      (ChartScales.Q n) ^ (-2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
        p (PhysicalResidualTZ.graphMapTZ (ActualCycleResidualBounds.actualBandGraph n) z) := by
  change ((ChartScales.Q n) ^ (-CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h)) ^ 2
    * _ = _
  rw [← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
  congr 2
  ring

theorem localPotential_curl_eq_sum
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hm : nativePoint n w ∈ nativeDomain) :
    SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n) w =
      ∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        SpatialCurl.spatialCurl
          (localPotentialMode (ActualCycleParameters.particularState x) (l.2,l.1) j n) w := by
  classical
  rw [localPotential_eq_sum]
  have hd (l : ActualInitialization.Index B N0) (j : ℤ)
      (hj : j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand) :
      DifferentiableAt ℝ
        (localPotentialMode (ActualCycleParameters.particularState x) (l.2,l.1) j n) w :=
    ((localModes_contDiffAt_of_invariant H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 n ha i hw hm).1).differentiableAt (by simp)
  rw [PhysicalParticularWave.spatialCurl_finset_sum _ _ (fun l _ =>
    DifferentiableAt.fun_sum (fun j hj => hd l j hj))]
  exact Finset.sum_congr rfl (fun l _ =>
    PhysicalParticularWave.spatialCurl_finset_sum _ _ (hd l))

theorem localPotential_curl_components
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical a i)
    (hm : PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
      (CommonWindow.index ActualPrimary.h n) z ∈ nativeDomain) (k : Fin 3) :
    CylindricalResidual.frame (-(z.2 1))
      (SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n)
        (z.1, CylindricalResidual.chart z.2)) k =
    (ChartScales.Q n) ^ (-CoordinateAlgebra.A ActualPrimary.h) *
      (ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
        (ActualPrimary.commonContext B) x.state n
        (PhysicalResidualTZ.graphMapTZ (ActualCycleResidualBounds.actualBandGraph n) z) k := by
  classical
  have hw : (z.1, CylindricalResidual.chart z.2) ∈
      ActualMeanPotentialRealization.cartesianDomain a i := by
    simpa [ActualMeanPotentialRealization.cartesianDomain,
      PhysicalGraphBounds.radialProjection_apply,
      CylindricalResidual.chart, PolarCharts.polar] using hz.2.2
  have hm' : nativePoint n (z.1, CylindricalResidual.chart z.2) ∈ nativeDomain := by
    apply (nativeMap_polar_mem_iff n a i _).mp
    rwa [PhysicalCurlCovariance.polarCoordinates_forward ha i hz]
  rw [localPotential_curl_eq_sum H hN n ha i hw hm', particularVelocity_eq_sum H]
  simp only [map_sum, space_sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [nativeMap_eq_graph] using localPotentialMode_curl_of_invariant H hN l j
    ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 n ha i hz hm k

theorem localPotential_curl_forward
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {z : SpaceTime}
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical a i)
    (hm : PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
      (CommonWindow.index ActualPrimary.h n) z ∈ nativeDomain) :
    SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n)
        (z.1, CylindricalResidual.chart z.2) =
      CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
            (ActualPrimary.commonContext B) x.state n))
        (z.1, CylindricalResidual.chart z.2) := by
  have he : CylindricalResidual.frame (-(z.2 1))
      (SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n)
        (z.1, CylindricalResidual.chart z.2)) =
      CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
        ((ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
          (ActualPrimary.commonContext B) x.state n) z := by
    ext k
    rw [velocityMap_apply]
    exact localPotential_curl_components H hN n ha i hz hm k
  rw [ActualMeanPotentialRealization.polar_forward ha i _ hz]
  simpa only [CylindricalResidual.frame_inverse'] using
    congrArg (CylindricalResidual.frame (z.2 1)) he

theorem localPotential_curl
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i)
    (hm : nativePoint n w ∈ nativeDomain) :
    SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n) w =
      CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
            (ActualPrimary.commonContext B) x.state n)) w := by
  have he := localPotential_curl_forward H hN n ha i
    (ActualMeanPotentialRealization.polarCoordinates_valid ha i hw)
    ((nativeMap_polar_mem_iff n a i w).mpr hm)
  simpa only [ActualMeanPotentialRealization.polarCoordinates_back ha i hw] using he

theorem localPressure_eq
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    localPressure (ActualCycleParameters.particularState x) n w =
      CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).particularPressure x.coefficients
            (ActualPrimary.commonContext B) x.state n)) w := by
  classical
  rw [localPressure_eq_sum]
  change (∑ l ∈ x.coefficients.labels n, ∑ j ∈ ParticularWaveAssembly.modes
    x.coefficients.residualBand,
    localPressureMode (ActualCycleParameters.particularState x) (l.2,l.1) j n w) =
    CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n) _
      (PhysicalCurlCovariance.polarCoordinates a i w)
  rw [pressureMap_apply, particularPressure_eq_sum H]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  rw [localPressureMode_eq_chart _ _ _
    (ActualParticularDynamics.carrier_frequency (ActualParticularCycleData.preservesCarriers H)
      (l.2,l.1))
    n ha i hw]
  change (ChartScales.Q n) ^ (-2 * CoordinateAlgebra.A ActualPrimary.h) *
    (nativePressure (ActualCycleParameters.particularState x) (l.2,l.1) j n
      (PhysicalParticularWave.nativeMap ActualPrimary.h (ChartScales.Q n)
        (CommonWindow.index ActualPrimary.h n) (PhysicalCurlCovariance.polarCoordinates a i w))).re
          = _
  rw [nativeMap_eq_graph]

theorem nativePoint_mem_of_chartDomain {qbig : ℝ} {n : ℕ} {a : ℝ} {i : PolarCharts.Index}
    {w : SpaceTime} (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    nativePoint n w ∈ nativeDomain := by
  apply (nativeMap_polar_mem_iff n a i w).mp
  change _ ∈ ActualPrimary.standardRegion.carrier ∧ True
  exact ⟨hw.2.2.2.1.1, trivial⟩

/-- The literal finite potential has exactly the physical curl required by the
particular stage of the correction cycle, throughout each valid current chart. -/
theorem localPotential_curl_eqOn
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (qbig : ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (localPotential (ActualCycleParameters.particularState x) n))
      (CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
            (ActualPrimary.commonContext B) x.state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  intro w hw
  exact localPotential_curl H hN n ha i hw.2.1 (nativePoint_mem_of_chartDomain hw)

/-- The pressure uses the same finite harmonic and label sums and the square of
the physical velocity scale. -/
theorem localPressure_eqOn
    {x : CycleState (ActualInitialization.Index B N0)} {σ : ℝ}
    (H : ActualParticularCycleData.Invariant σ x) (qbig : ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (localPressure (ActualCycleParameters.particularState x) n)
      (CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).particularPressure x.coefficients
            (ActualPrimary.commonContext B) x.state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  intro w hw
  exact localPressure_eq H n ha i hw.2.1

end NavierStokes.ActualCurrentParticularAssembly
