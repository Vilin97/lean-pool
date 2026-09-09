/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryCoherence
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhaseDefect
import LeanPool.NavierStokesAndEuler.NavierStokes.NormalScaling

/-!
# Exact dynamics of the selected primary pulses

The native equation uses the same selected frame, covariance amplitude and
pressure as `CorrectionInitialization.ActualPrimary`.  Its homogeneous
equation is localized to the Gaussian support: the outer attachment cutoff
is deliberately differentiated outside that support.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualPrimaryDynamics

open Set Function Filter HarmonicCalculus
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped ContDiff Topology InnerProductSpace BigOperators


/-- Native: an abbreviation for `ActualSignedGeometry.Native`. -/
abbrev Native := ActualSignedGeometry.Native
/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space

section Frame

variable {I : Type*} {U : PhaseJetBounds.Domain I PhaseCalculus.Slow}

theorem frame_tail_ne (P : PrimaryPulseBounds.PhaseConstruction U) (i : I)
    {z : PhaseCalculus.Slow × ℝ} (hz : z ∈ (U.slot P.V P.openV).carrier i) :
    MovingFrameODE.tail (P.phase.normal i z) ≠ 0 := by
  have hB : 0 < P.B i := lt_of_lt_of_le (by linarith [P.b_pos]) (P.B_bound i).1
  exact (PhaseEstimates.normal_lower_bounds hB (P.K_unit i)
    (P.error_small i z hz) (P.normal_close i z hz)).2.2.1

theorem frame_normal (P : PrimaryPulseBounds.PhaseConstruction U) (i : I)
    {z : PhaseCalculus.Slow × ℝ} (hz : z ∈ (U.slot P.V P.openV).carrier i) :
    (P.frame i).normal z = P.phase.normal i z :=
  PrimaryODE.FrameData.ofNormalLocal_normal _ _ _ _ _ _ _ _ (frame_tail_ne P i hz)

theorem frame_motion (P : PrimaryPulseBounds.PhaseConstruction U) (i : I)
    {z : PhaseCalculus.Slow × ℝ} (hz : z ∈ (U.slot P.V P.openV).carrier i) :
    (P.frame i).normalMotion z = P.phase.velocity i z := by
  have hF := ((P.baseF.smooth i).contDiffAt ((U.isOpen i).mem_nhds hz.1)).differentiableAt (by simp)
  have hG := ((P.baseG.smooth i).contDiffAt ((U.isOpen i).mem_nhds hz.1)).differentiableAt (by simp)
  exact PrimaryODE.FrameData.ofNormalLocal_normalMotion _ _ _ _ _ _ _ _
    (PhaseCalculus.hasDerivAt_phaseNormal_slot _ _ _ _ _ _ _ _ _ (P.epsilon_ne i) hF hG)
    (frame_tail_ne P i hz)

end Frame

section NativeDynamics

variable {B N0 : ℕ}

theorem rawVelocity_hasDerivAt (j : Fin 2) (L : Label B N0) {x : Native}
    (hp : x.1 ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (ht : x.2.2 ∈ Ioo 0 ((phases B N0 j).L L)) :
    HasDerivAt (fun t => rawVelocity j L (x.1, (x.2.1,t)))
      (TangentProjection.projectedRhs
        ((phases B N0 j).phase.normal L (phasePoint L x))
        ((phases B N0 j).phase.velocity L (phasePoint L x))
        (rawVelocity j L x)
        (PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L x.1)
          ((phases B N0 j).phase.shear L (phasePoint L x)) (rawVelocity j L x))
        0 (((phases B N0 j).frame L).viscosity (phasePoint L x))) x.2.2 := by
  let P := phases B N0 j
  let ell := P.L L
  let a := PartitionedCovariance.amplitude (ChartScales.epsilon h (BaseChartJets.cellBand L))
    (spatialMask L x.1 * PartitionedCovariance.cutoff slots.radius x.2.1)
    (covariance B N0 L x.1) (fun k => PrimaryTargetBounds.actualTarget modulation x.1 k) j
  have hL : 0 < ell := P.L_pos L
  have hθ : x.2.2 / ell ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ht.1 hL, (div_lt_one hL).mpr ht.2⟩
  have hd := PrimaryPulseBounds.normalizedPulse_hasDerivAt (P.frame L) (P.lam L) (P.u L) hL
    ((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    ((sourcePair L x.1 hp).coefficient_continuous j) hp ((sourcePair L x.1 hp).kinematics j) hθ
  have hv : ell * (x.2.2 / ell) = x.2.2 := mul_div_cancel₀ _ hL.ne'
  have hz : phasePoint L x ∈
      ((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).slot P.V P.openV).carrier
          L :=
    ⟨hp, P.interval L ⟨ht.1.le, ht.2.le⟩⟩
  have hd' := (hd.scomp x.2.2 ((hasDerivAt_id x.2.2).div_const ell)).const_smul a
  simp only [hv, one_div, smul_smul, inv_mul_cancel₀ hL.ne', one_smul] at hd'
  have he (t : ℝ) : rawVelocity j L (x.1,(x.2.1,t)) =
      a • PrimaryPulseBounds.normalizedPulse (P.frame L) (P.lam L) (P.u L) ell (x.1,t/ell) := by
    simp only [rawVelocity, pulseCoordinates, a, ell, P, length_sign]
  simp only [he]
  convert! hd' using 1
  rw [show (P.frame L).normal (x.1,x.2.2) = P.phase.normal L (phasePoint L x) from
    frame_normal P L hz,
    show (P.frame L).normalMotion (x.1,x.2.2) = P.phase.velocity L (phasePoint L x) from
    frame_motion P L hz, map_smul, SignedWaveUpdate.projectedRhs_smul]
  rfl

theorem frame_viscosity (j : Fin 2) (L : Label B N0) (x : Native) :
    ((phases B N0 j).frame L).viscosity (phasePoint L x) =
      ChartScales.epsilon h (BaseChartJets.cellBand L) *
        (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ)^2 *
        ‖(phases B N0 j).phase.normal L (phasePoint L x)‖^2 := rfl

theorem rawVelocity_hasDerivAt_on_slot (j : Fin 2) (L : Label B N0) {x : Native}
    (hT : 0 < x.1.2.2) (ht : x.2.2 ∈ Ioo 0 ((phases B N0 j).L L)) :
    HasDerivAt (fun t => rawVelocity j L (x.1, (x.2.1,t)))
      (TangentProjection.projectedRhs
        ((phases B N0 j).phase.normal L (phasePoint L x))
        ((phases B N0 j).phase.velocity L (phasePoint L x))
        (rawVelocity j L x)
        (PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L x.1)
          ((phases B N0 j).phase.shear L (phasePoint L x)) (rawVelocity j L x))
        0 (ChartScales.epsilon h (BaseChartJets.cellBand L) *
          (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ)^2 *
          ‖(phases B N0 j).phase.normal L (phasePoint L x)‖^2)) x.2.2 := by
  by_cases hm : spatialMask L x.1 = 0
  · have hz (t : ℝ) : rawVelocity j L (x.1,(x.2.1,t)) = 0 := by
      simp [rawVelocity, PartitionedCovariance.amplitude, hm]
    have hz' : rawVelocity j L x = 0 := by simpa only [Prod.mk.eta] using hz x.2.2
    simp only [hz, map_zero]
    simpa [TangentProjection.projectedRhs, TangentProjection.tangentProj] using
      hasDerivAt_const x.2.2 (0 : Space)
  · simpa only [frame_viscosity] using
      rawVelocity_hasDerivAt j L (spatialMask_carrier L hT hm) ht

theorem gaussian_slot (L : Label B N0) {x : Native} (hg : gaussian L x ≠ 0) :
    x.2.2 ∈ Ioo 0 ((phases B N0 0).L L) := by
  have hb : |x.2.2 / (phases B N0 0).L L - 1/2| < 1/3 := by
    by_contra hn
    exact hg (GaussianTailFlat.profile_zero (le_of_not_gt hn))
  have hL := (phases B N0 0).L_pos L
  have h0 : 0 < x.2.2 / (phases B N0 0).L L := by linarith [(abs_lt.mp hb).1]
  have h1 : x.2.2 / (phases B N0 0).L L < 1 := by linarith [(abs_lt.mp hb).2]
  exact ⟨(div_pos_iff.mp h0).resolve_right (by rintro ⟨_, hz⟩; linarith) |>.1,
    (div_lt_one hL).mp h1⟩

theorem outerCutoff_one_germ (L : Label B N0) {x : Native} (hg : gaussian L x ≠ 0) :
    (fun t : ℝ => PrimaryCopyBounds.outerCutoff (t / (phases B N0 0).L L)) =ᶠ[𝓝 x.2.2]
      fun _ => 1 := by
  have hb : |x.2.2 / (phases B N0 0).L L - 1/2| < 1/3 := by
    by_contra hn
    exact hg (GaussianTailFlat.profile_zero (le_of_not_gt hn))
  have hc : Continuous (fun t : ℝ => |t / (phases B N0 0).L L - 1/2|) := by fun_prop
  filter_upwards [hc.continuousAt.eventually (isOpen_Iio.mem_nhds hb)] with t ht
  exact PrimaryCopyBounds.outerCutoff_one ht.le

theorem attachedVelocity_hasDerivAt (j : Fin 2) (L : Label B N0) {x : Native}
    (hT : 0 < x.1.2.2) (hg : gaussian L x ≠ 0) :
    HasDerivAt (fun t => attachedRawVelocity j L (x.1, (x.2.1,t)))
      (TangentProjection.projectedRhs
        ((phases B N0 j).phase.normal L (phasePoint L x))
        ((phases B N0 j).phase.velocity L (phasePoint L x))
        (attachedRawVelocity j L x)
        (PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L x.1)
          ((phases B N0 j).phase.shear L (phasePoint L x)) (attachedRawVelocity j L x))
        0 (ChartScales.epsilon h (BaseChartJets.cellBand L) *
          (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ)^2 *
          ‖(phases B N0 j).phase.normal L (phasePoint L x)‖^2)) x.2.2 := by
  by_cases hr : WaveEdgeExtension.nativeRadius h x ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · have he : (fun t => attachedRawVelocity j L (x.1,(x.2.1,t))) =ᶠ[𝓝 x.2.2]
        fun t => rawVelocity j L (x.1,(x.2.1,t)) := by
      filter_upwards [outerCutoff_one_germ L hg] with t ht
      have hr' : WaveEdgeExtension.nativeRadius h (x.1,(x.2.1,t)) ∈
          Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) :=
              hr
      rw [attachedRawVelocity, WaveEdgeExtension.nativeExtension_inside nominal _ hr']
      simp only [outerRawVelocity, pulseCoordinates, ht, one_smul]
    have hv := he.eq_of_nhds
    simp only [Prod.mk.eta] at hv
    rw [hv]
    exact (rawVelocity_hasDerivAt_on_slot j L hT (by
        simpa only [length_sign] using gaussian_slot L hg)).congr_of_eventuallyEq he
  · have hz (t : ℝ) : attachedRawVelocity j L (x.1,(x.2.1,t)) = 0 :=
      WaveEdgeExtension.nativeExtension_outside nominal _ hr
    have hz' : attachedRawVelocity j L x = 0 := by simpa only [Prod.mk.eta] using hz x.2.2
    simp only [hz, map_zero]
    simpa [TangentProjection.projectedRhs, TangentProjection.tangentProj] using
      hasDerivAt_const x.2.2 (0 : Space)

theorem attachedPressure_eq (j : Fin 2) (L : Label B N0) {x : Native}
    (hg : gaussian L x ≠ 0) :
    attachedRawPressure j L x = Complex.I *
      (TangentProjection.pressureCoefficient
        ((phases B N0 j).phase.normal L (phasePoint L x))
        ((phases B N0 j).phase.velocity L (phasePoint L x))
        (attachedRawVelocity j L x)
        (PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L x.1)
          ((phases B N0 j).phase.shear L (phasePoint L x)) (attachedRawVelocity j L x)) 0 : ℂ) /
          (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) := by
  have ho := (outerCutoff_one_germ L hg).eq_of_nhds
  by_cases hr : WaveEdgeExtension.nativeRadius h x ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · simp only [attachedRawPressure, attachedRawVelocity,
      WaveEdgeExtension.nativeExtension_inside nominal _ hr,
      outerRawPressure, outerRawVelocity, pulseCoordinates, ho, one_smul]
    rfl
  · simp only [attachedRawPressure, attachedRawVelocity,
      WaveEdgeExtension.nativeExtension_outside nominal _ hr, map_zero]
    simp [TangentProjection.pressureCoefficient]

end NativeDynamics

section Coordinates

variable {B N0 : ℕ}

theorem geometry_radial (j : Fin 2) (L : Label B N0) :
    (geometry j L).coordinateLinear radialVector =
      (ChartScales.Lambda ^ ChartScales.nativeIndex h (BaseChartJets.cellBand L), 0) :=
  ActualSignedGeometry.slot_coordinate_radial slots
    (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) _

theorem geometry_temporal (j : Fin 2) (L : Label B N0) :
    (geometry j L).coordinateLinear temporalVector =
      (0, (ChartScales.Q (BaseChartJets.cellBand L) ^ (1+h))⁻¹) := by
  let g := geometry j L
  let n := BaseChartJets.cellBand L
  have hb : g.basis (0, (ChartScales.timeCoefficient h n)⁻¹) = temporalVector := by
    change (TorusAverages.slotChart radialVector temporalVector vectors_det)
      ((TorusAverages.transverseChart (ChartScales.timeCoefficient h n)
        (ChartScales.timeCoefficient_pos h n).ne') (0, (ChartScales.timeCoefficient h n)⁻¹)) = _
    simp [TorusAverages.transverseChart_apply, TorusAverages.slotChart_apply,
      (ChartScales.timeCoefficient_pos h n).ne']
  have he : g.basis.symm temporalVector = (0, (ChartScales.timeCoefficient h n)⁻¹) :=
    (g.basis.symm_apply_eq).mpr hb.symm
  change g.basis.symm (CommonCoverSolve.coverPower (ChartScales.nativeIndex h n) temporalVector) = _
  rw [show CommonCoverSolve.coverPower (ChartScales.nativeIndex h n) temporalVector =
      ChartScales.Tg ^ ChartScales.nativeIndex h n • temporalVector from
        CommonBaseContext.coverPower_temporal _, map_smul, he]
  simp only [Prod.smul_mk, smul_eq_mul]
  ext <;> simp [ChartScales.timeCoefficient, mul_inv_rev, n,
    ne_of_gt (pow_pos ChartScales.Tg_pos (ChartScales.nativeIndex h (BaseChartJets.cellBand L))),
    mul_left_comm]

/-- Absolute native linear, bundling `toFun`, `map_add`, `map_smul`, `cont`. -/
noncomputable def absoluteNativeLinear (j : Fin 2) (L : Label B N0) :
    ActualPrimaryCoherence.Absolute →L[ℝ] Native where
  toFun x := (nativeSlow L x.1, (geometry j L).coordinateLinear x.1.2)
  map_add' x y := by
    ext <;> simp [nativeSlow, add_div, map_add]
  map_smul' c x := by
    ext <;> simp [nativeSlow, mul_div_assoc, map_smul]
  cont := ((nativeSlow_smooth L).continuous.comp continuous_fst).prodMk
    ((geometry j L).coordinateLinear.continuous.comp continuous_fst.snd)

/-- Copy linear, given by `(absoluteNativeLinear j L).comp (ActualPrimaryCoherence.absoluteChart
n).toContinuousLinearMap`. -/
noncomputable def copyLinear (j : Fin 2) (L : Label B N0) (n : ℕ) : FullPoint →L[ℝ] Native :=
  (absoluteNativeLinear j L).comp (ActualPrimaryCoherence.absoluteChart n).toContinuousLinearMap

/-- Copy point, given by `(nativeSlow L (toAbsolute n x.1), (geometry j L).coordinates k
(toAbsolute n x.1).2)`. -/
noncomputable def copyPoint (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : Native :=
  (nativeSlow L (toAbsolute n x.1), (geometry j L).coordinates k (toAbsolute n x.1).2)

theorem copyPoint_affine (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) :
    copyPoint j L n k x = copyLinear j L n x + (0,(geometry j L).coordinates k 0) := by
  apply Prod.ext
  · simp [copyPoint, copyLinear, absoluteNativeLinear]
  · change (geometry j L).coordinates k _ = _ + _
    rw [CommonCoverSolve.Geometry.coordinates_eq_affine, add_comm]
    rfl

theorem copyPoint_hasFDerivAt (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) :
    HasFDerivAt (copyPoint j L n k) (copyLinear j L n) x := by
  simpa only [← copyPoint_affine] using
    (copyLinear j L n).hasFDerivAt.add_const (0,(geometry j L).coordinates k 0)

theorem copyPoint_smooth (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) : ContDiff ℝ ∞ (copyPoint j L n k) := by
  simpa only [← copyPoint_affine] using
    (copyLinear j L n).contDiff.add
      (contDiff_const (c := (0,(geometry j L).coordinates k 0)))

/-- Clock scale, given by `ChartScales.Q n ^ (1+h) / ChartScales.Q (BaseChartJets.cellBand L) ^
(1+h)`. -/
noncomputable def clockScale (L : Label B N0) (n : ℕ) : ℝ :=
  ChartScales.Q n ^ (1+h) / ChartScales.Q (BaseChartJets.cellBand L) ^ (1+h)

/-- Radial scale, given by `Real.sqrt (ChartScales.Q n) / Real.sqrt (ChartScales.Q
(BaseChartJets.cellBand L))`. -/
noncomputable def radialScale (L : Label B N0) (n : ℕ) : ℝ :=
  Real.sqrt (ChartScales.Q n) / Real.sqrt (ChartScales.Q (BaseChartJets.cellBand L))

/-- Velocity scale, given by `ChartScales.Q n ^ CoordinateAlgebra.A h / ChartScales.Q
(BaseChartJets.cellBand L) ^ CoordinateAlgebra.A h`. -/
noncomputable def velocityScale (L : Label B N0) (n : ℕ) : ℝ :=
  ChartScales.Q n ^ CoordinateAlgebra.A h /
    ChartScales.Q (BaseChartJets.cellBand L) ^ CoordinateAlgebra.A h

theorem copyLinear_fast (j : Fin 2) (L : Label B N0) (n : ℕ) (x : FullPoint) :
    copyLinear j L n ((PrimaryResidualClass.directions (commonContext B)).fastField n x) =
      (0,(0,clockScale L n)) := by
  change absoluteNativeLinear j L (ActualPrimaryCoherence.absoluteChart n
    ((PrimaryResidualClass.directions (commonContext B)).fastField n x)) = _
  rw [ActualPrimaryCoherence.absoluteChart_fast, map_smul]
  change ChartScales.Q n ^ (1+h) •
    (nativeSlow L ((0,(0,0)),temporalVector), (geometry j L).coordinateLinear temporalVector) = _
  rw [geometry_temporal]
  simp [nativeSlow, clockScale, div_eq_mul_inv]

theorem copyPoint_fast_line (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) (t : ℝ) :
    copyPoint j L n k (x+t • (PrimaryResidualClass.directions (commonContext B)).fastField n x) =
      ((copyPoint j L n k x).1,
        ((copyPoint j L n k x).2.1, (copyPoint j L n k x).2.2+t*clockScale L n)) := by
  rw [copyPoint_affine, map_add, map_smul, copyLinear_fast]
  rw [copyPoint_affine]
  ext <;> simp
  all_goals ring

/-- Slot linear as an element of `FullPoint →L[ℝ] PhaseCalculus.Slot`. -/
noncomputable def slotLinear (j : Fin 2) (L : Label B N0) (n : ℕ) :
    FullPoint →L[ℝ] PhaseCalculus.Slot :=
  ((ContinuousLinearMap.fst ℝ PhaseCalculus.Slow TorusInverse.Plane).comp (copyLinear j L n)).prod
    ((ContinuousLinearMap.snd ℝ LocalSignedRequest.Point ℝ).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ PhaseCalculus.Slow TorusInverse.Plane).comp (copyLinear j L
            n))))

/-- Slot point, given by `((copyPoint j L n k x).1,(x.2,(copyPoint j L n k x).2.2))`. -/
noncomputable def slotPoint (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : PhaseCalculus.Slot :=
  ((copyPoint j L n k x).1,(x.2,(copyPoint j L n k x).2.2))

theorem slotLinear_apply (j : Fin 2) (L : Label B N0) (n : ℕ) (x : FullPoint) :
    slotLinear j L n x = ((copyLinear j L n x).1,(x.2,(copyLinear j L n x).2.2)) := rfl

theorem slotPoint_hasFDerivAt (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) :
    HasFDerivAt (slotPoint j L n k) (slotLinear j L n) x :=
  (copyPoint_hasFDerivAt j L n k x).fst.prodMk
    (hasFDerivAt_snd.prodMk (copyPoint_hasFDerivAt j L n k x).snd.snd)

theorem slotLinear_radial (j : Fin 2) (L : Label B N0) (n : ℕ) (x : FullPoint) :
    slotLinear j L n ((PrimaryResidualClass.directions (commonContext B)).radialField n x) =
      radialScale L n • PhaseCalculus.eR := by
  have he := ActualPrimaryCoherence.absoluteChart_radial B n x
  rw [slotLinear_apply]
  have hz : ((PrimaryResidualClass.directions (commonContext B)).radialField n x).2 = 0 := by
    simp [LinearWaveBounds.GraphDirections.radialField, PrimaryResidualClass.directions]
  rw [hz]
  change ((absoluteNativeLinear j L (ActualPrimaryCoherence.absoluteChart n
      ((PrimaryResidualClass.directions (commonContext B)).radialField n x))).1,
    (0,(absoluteNativeLinear j L (ActualPrimaryCoherence.absoluteChart n
      ((PrimaryResidualClass.directions (commonContext B)).radialField n x))).2.2)) = _
  rw [he]
  simp only [map_smul]
  change ((Real.sqrt (ChartScales.Q n) • nativeSlow L
      ((1,(0,0)), RadialPullback.radialJacobian (ChartScales.radialExponent h)
        (toAbsolute n x.1).1.1 • radialVector)),
    (0,(Real.sqrt (ChartScales.Q n) • (geometry j L).coordinateLinear
      (RadialPullback.radialJacobian (ChartScales.radialExponent h) (toAbsolute n x.1).1.1 •
          radialVector)).2)) = _
  rw [map_smul, geometry_radial]
  simp [nativeSlow, radialScale, PhaseCalculus.eR, div_eq_mul_inv]

theorem slotLinear_angular (j : Fin 2) (L : Label B N0) (n : ℕ) (x : FullPoint) :
    slotLinear j L n (PrimaryResidualClass.directions (commonContext B)).angular =
      PhaseCalculus.eTheta := by
  have he := ActualPrimaryCoherence.absoluteChart_angular B n x
  change ((absoluteNativeLinear j L (ActualPrimaryCoherence.absoluteChart n
      (PrimaryResidualClass.directions (commonContext B)).angular)).1,
    (1,(absoluteNativeLinear j L (ActualPrimaryCoherence.absoluteChart n
      (PrimaryResidualClass.directions (commonContext B)).angular)).2.2)) = _
  rw [he]
  simp [absoluteNativeLinear, ActualPrimaryCoherence.absoluteAngular, nativeSlow,
      PhaseCalculus.eTheta]

theorem radialScale_epsilon (L : Label B N0) (n : ℕ) :
    radialScale L n * ChartScales.epsilon h (BaseChartJets.cellBand L) =
      Real.sqrt (ChartScales.Q n) / ChartScales.Q (BaseChartJets.cellBand L) ^ CoordinateAlgebra.D
          h := by
  unfold radialScale ChartScales.epsilon
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [div_mul_eq_mul_div, mul_div_assoc, ← Real.rpow_sub (ChartScales.Q_pos _)]
  rw [show h - 1/2 = -CoordinateAlgebra.D h by unfold CoordinateAlgebra.D; ring,
    Real.rpow_neg (ChartScales.Q_pos _).le]
  ring

theorem slotLinear_axial (j : Fin 2) (L : Label B N0) (n : ℕ)
    (U : LocalSignedRequest.SlowRegion (2 * h)) (x : FullPoint) :
    slotLinear j L n ((PrimaryResidualClass.directions (commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n x) =
      (radialScale L n * ChartScales.epsilon h (BaseChartJets.cellBand L)) • PhaseCalculus.eZ := by
  have he := ActualPrimaryCoherence.absoluteChart_axial B n U x
  rw [slotLinear_apply]
  have hz : ((PrimaryResidualClass.directions (commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n x).2 = 0
          := by
    simp [LinearWaveBounds.GraphDirections.axialField, PrimaryResidualClass.directions]
  rw [hz]
  change ((absoluteNativeLinear j L (ActualPrimaryCoherence.absoluteChart n
      ((PrimaryResidualClass.directions (commonContext B)).axialField
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n x))).1,
    (0,(absoluteNativeLinear j L (ActualPrimaryCoherence.absoluteChart n
      ((PrimaryResidualClass.directions (commonContext B)).axialField
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n
            x))).2.2)) = _
  rw [he, map_smul, radialScale_epsilon]
  simp [absoluteNativeLinear, ActualPrimaryCoherence.absoluteAxial, nativeSlow,
    PhaseCalculus.eZ, div_eq_mul_inv]

theorem slotPoint_radius (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) :
    (slotPoint j L n k x).1.1 = radialScale L n * x.1.1 := by
  simp [slotPoint, copyPoint, nativeSlow, toAbsolute, radialScale]
  ring

theorem copyPoint_time_pos (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint} (hT : 0 < x.1.2.1.1) :
    0 < (copyPoint j L n k x).1.2.2 :=
  div_pos (mul_pos (ChartScales.Q_pos n) hT) (ChartScales.Q_pos _)

/-- Transport of an actual native time derivative.  This also applies to
the unweighted fundamental and to later signed amplitudes. -/
theorem along_copy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Fin 2) (L : Label B N0) (n : ℕ) (k : TorusInverse.Frequency)
    (f : Native → E) {x : FullPoint} {v : E}
    (hd : HasDerivAt (fun t => f ((copyPoint j L n k x).1,
      ((copyPoint j L n k x).2.1, t))) v (copyPoint j L n k x).2.2)
    (hf : DifferentiableAt ℝ (fun y => f (copyPoint j L n k y)) x) :
    along ((PrimaryResidualClass.directions (commonContext B)).fastField n)
      (fun y => f (copyPoint j L n k y)) x = clockScale L n • v := by
  have ht : HasDerivAt (fun t : ℝ => (copyPoint j L n k x).2.2+t*clockScale L n)
      (clockScale L n) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (clockScale L n)).const_add
      (copyPoint j L n k x).2.2
  have hp := hd.scomp_of_eq (0 : ℝ) ht (by simp)
  have hl : HasDerivAt (fun t : ℝ => x+t •
      (PrimaryResidualClass.directions (commonContext B)).fastField n x)
      ((PrimaryResidualClass.directions (commonContext B)).fastField n x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      ((PrimaryResidualClass.directions (commonContext B)).fastField n x)).const_add x
  have hh := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  simp only [Function.comp_def, copyPoint_fast_line] at hh hp
  exact hh.unique hp

end Coordinates

section CopyGerms

variable {B N0 : ℕ}

/-- Coefficient point, given by `(nativeSlow L (toAbsolute n x.1), (toAbsolute n x.1).2)`. -/
noncomputable def coefficientPoint (L : Label B N0) (n : ℕ) (x : FullPoint) : Native :=
  (nativeSlow L (toAbsolute n x.1), (toAbsolute n x.1).2)

theorem coefficientPoint_smooth (L : Label B N0) (n : ℕ) :
    ContDiff ℝ ∞ (coefficientPoint L n) :=
  ((nativeSlow_smooth L).comp ((toAbsolute_smooth n).comp contDiff_fst)).prodMk
    (((toAbsolute_smooth n).comp contDiff_fst).snd)

/-- Native phase, constructed using `PhaseCalculus.phase`. -/
noncomputable def nativePhase (j : Fin 2) (L : Label B N0) : PhaseCalculus.Slot → ℝ :=
  PhaseCalculus.phase ((phases B N0 j).phase.epsilon L)
    ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
    ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L)

theorem phase_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core) :
    (chartCoefficients j L).phase n =ᶠ[𝓝 x]
      fun y => ((ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) /
        (ChartScales.carrier h n : ℝ)) * nativePhase j L (slotPoint j L n k y) := by
  have he := PeriodicPhaseAssembly.periodicClock_germ (geometry j L) (clockWindow L)
    (clockWindow_injective j L) k (z := coefficientPoint L n x) hc
  have hp := PrimaryGeometryAssembly.carrier_mul_phase_p certificate modulation
    (choice B N0).prepared slots.radius_pos j L
  change (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) *
    (phases B N0 j).phase.p L = _ at hp
  filter_upwards [(coefficientPoint_smooth L n).continuous.continuousAt.eventually he] with y hy
  simp only [chartCoefficients, absolutePhase, periodicPhase]
  change (_ + (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) *
    (_ + _ - PeriodicPhaseAssembly.periodicClock (geometry j L) (clockWindow L).cutoff
      (coefficientPoint L n y).2 * _)) / (ChartScales.carrier h n : ℝ) = _
  rw [hy, ← hp]
  simp only [nativePhase, PhaseCalculus.phase, slotPoint, copyPoint, coefficientPoint]
  ring

theorem cutoff_eq_copy (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core) :
    chartCutoff j L n x = gaussian L (copyPoint j L n k x) :=
  periodicGaussian_eq_on_core j L (coefficientPoint L n x).1
    (coefficientPoint L n x).2 k hc

theorem velocityScale_eq (L : Label B N0) (n : ℕ) :
    velocityScale L n = ChartScales.Q n ^ CoordinateAlgebra.A h *
      ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h) := by
  rw [Real.rpow_neg (ChartScales.Q_pos _).le]
  rfl

theorem pressureScale_eq (L : Label B N0) (n : ℕ) :
    velocityScale L n ^ 2 = ChartScales.Q n ^ (2 * CoordinateAlgebra.A h) *
      ChartScales.Q (BaseChartJets.cellBand L) ^ (-(2 * CoordinateAlgebra.A h)) := by
  unfold velocityScale
  rw [div_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le,
    ← Real.rpow_mul_natCast (ChartScales.Q_pos (BaseChartJets.cellBand L)).le]
  norm_num only [Nat.cast_ofNat]
  rw [mul_comm (CoordinateAlgebra.A h) 2, Real.rpow_neg (ChartScales.Q_pos _).le]
  rfl

/-- Copy amplitude, given by `velocityScale L n • CurlClassBounds.complexify
(attachedRawVelocity j L (copyPoint j L n k x))`. -/
noncomputable def copyAmplitude (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : ComplexVector :=
  velocityScale L n • CurlClassBounds.complexify (attachedRawVelocity j L (copyPoint j L n k x))

/-- Copy pressure, given by `velocityScale L n ^ 2 • attachedRawPressure j L (copyPoint j L n k
x)`. -/
noncomputable def copyPressure (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : ℂ :=
  velocityScale L n ^ 2 • attachedRawPressure j L (copyPoint j L n k x)

theorem amplitude_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core) :
    (chartCoefficients j L).amplitude n =ᶠ[𝓝 x] copyAmplitude j L n k := by
  let f : TorusInverse.Frequency → Native → ComplexVector := fun l z =>
    CurlClassBounds.complexify (attachedRawVelocity j L (z.1,(geometry j L).coordinates l z.2))
  have hs (l) : support (f l) ⊆ (copyCells j L).carrier 0 l := by
    intro z hz
    change (geometry j L).coordinates l z.2 ∈ (clockWindow L).core
    apply attachedRawVelocity_core j L (z.1,(geometry j L).coordinates l z.2)
    intro he
    exact hz (by simp only [f, he, map_zero])
  have he := PeriodizedWaveBounds.copySum_germ (copyCells j L) 0 f hs
    (x := coefficientPoint L n x) hc
  filter_upwards [(coefficientPoint_smooth L n).continuous.continuousAt.eventually he] with y hy
  change ChartScales.Q n ^ CoordinateAlgebra.A h •
    (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h) •
      PeriodizedWaveBounds.copySum f (coefficientPoint L n y)) = _
  rw [hy, smul_smul, ← velocityScale_eq]
  rfl

theorem pressure_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core) :
    (chartCoefficients j L).pressure n =ᶠ[𝓝 x] copyPressure j L n k := by
  let f : TorusInverse.Frequency → Native → ℂ := fun l z =>
    attachedRawPressure j L (z.1,(geometry j L).coordinates l z.2)
  have hs (l) : support (f l) ⊆ (copyCells j L).carrier 0 l :=
    fun z hz => attachedRawPressure_core j L _ hz
  have he := PeriodizedWaveBounds.copySum_germ (copyCells j L) 0 f hs
    (x := coefficientPoint L n x) hc
  filter_upwards [(coefficientPoint_smooth L n).continuous.continuousAt.eventually he] with y hy
  change ChartScales.Q n ^ (2 * CoordinateAlgebra.A h) •
    (ChartScales.Q (BaseChartJets.cellBand L) ^ (-(2 * CoordinateAlgebra.A h)) •
      PeriodizedWaveBounds.copySum f (coefficientPoint L n y)) = _
  rw [hy, smul_smul, ← pressureScale_eq]
  rfl

theorem coefficient_zero_germs (j : Fin 2) (L : Label B N0) (n : ℕ) {x : FullPoint}
    (hc : ∀ k : TorusInverse.Frequency, (copyPoint j L n k x).2 ∉ (clockWindow L).core) :
    ((chartCoefficients j L).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      ((chartCoefficients j L).pressure n =ᶠ[𝓝 x] fun _ => 0) := by
  have hA := PeriodizedWaveBounds.copySum_zero_germ (copyCells j L) 0
    (fun l (z : Native) => CurlClassBounds.complexify
      (attachedRawVelocity j L (z.1,(geometry j L).coordinates l z.2)))
    (fun l z hz => attachedRawVelocity_core j L (z.1,(geometry j L).coordinates l z.2) (by
      intro he
      exact hz (by simp only [he, map_zero]))) (x := coefficientPoint L n x) hc
  have hP := PeriodizedWaveBounds.copySum_zero_germ (copyCells j L) 0
    (fun l (z : Native) => attachedRawPressure j L (z.1,(geometry j L).coordinates l z.2))
    (fun l z hz => attachedRawPressure_core j L (z.1,(geometry j L).coordinates l z.2) hz)
    (x := coefficientPoint L n x) hc
  constructor
  · filter_upwards [(coefficientPoint_smooth L n).continuous.continuousAt.eventually hA] with y hy
    have hh := congrArg (fun z : ComplexVector => ChartScales.Q n ^ CoordinateAlgebra.A h •
      (ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h) • z)) hy
    simpa only [smul_zero, coefficientPoint, PeriodizedWaveBounds.copySum, chartCoefficients,
      absoluteAmplitude, uncutAmplitude] using hh
  · filter_upwards [(coefficientPoint_smooth L n).continuous.continuousAt.eventually hP] with y hy
    have hh := congrArg (fun z : ℂ => ChartScales.Q n ^ (2 * CoordinateAlgebra.A h) •
      (ChartScales.Q (BaseChartJets.cellBand L) ^ (-(2 * CoordinateAlgebra.A h)) • z)) hy
    simpa only [smul_zero, coefficientPoint, PeriodizedWaveBounds.copySum, chartCoefficients,
      absolutePressure, uncutPressure] using hh

end CopyGerms

section PhaseNormal

variable {B N0 : ℕ}

theorem radialScale_pos (L : Label B N0) (n : ℕ) : 0 < radialScale L n :=
  div_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) (Real.sqrt_pos.mpr (ChartScales.Q_pos _))

theorem velocityScale_pos (L : Label B N0) (n : ℕ) : 0 < velocityScale L n :=
  div_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) (Real.rpow_pos_of_pos (ChartScales.Q_pos
      _) _)

theorem clockScale_eq (L : Label B N0) (n : ℕ) : clockScale L n =
    PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand
        L)) := by
  unfold clockScale PhysicalParticularWave.clockWeight PhysicalParticularWave.ratioPower
  congr 2 <;> unfold CoordinateAlgebra.A <;> ring

theorem radialScale_eq (L : Label B N0) (n : ℕ) : radialScale L n =
    PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand L))
        (1/2) := by
  simp only [radialScale, PhysicalParticularWave.ratioPower, Real.sqrt_eq_rpow]

theorem clockScale_factor (L : Label B N0) (n : ℕ) :
    clockScale L n = velocityScale L n * radialScale L n := by
  rw [clockScale_eq, radialScale_eq]
  exact ActualPhaseDefect.clock_eq_velocity_radial (ChartScales.Q_pos n) (ChartScales.Q_pos _) h

theorem copyPoint_radius_pos (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint} (hR : 0 < x.1.1) :
    0 < (copyPoint j L n k x).1.1 := by
  change 0 < (slotPoint j L n k x).1.1
  rw [slotPoint_radius]
  exact mul_pos (radialScale_pos L n) hR

theorem native_base_differentiable (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1) :
    DifferentiableAt ℝ ((phases B N0 j).phase.F L) (copyPoint j L n k x).1 ∧
      DifferentiableAt ℝ ((phases B N0 j).phase.G L) (copyPoint j L n k x).1 := by
  rw [phase_frequency, phase_axial]
  exact ⟨(ActualPrimaryCoherence.frequencySlow_smoothAt B _ (copyPoint_radius_pos j L n k hR)
      (copyPoint_time_pos j L n k hT)).differentiableAt (by simp),
    (ActualPrimaryCoherence.axialSlow_smoothAt B _ (copyPoint_time_pos j L n k
        hT)).differentiableAt (by
        simp)⟩

/-- Normal scale, given by `((ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) /
(ChartScales.carrier h n : ℝ)) * radialScale L n`. -/
noncomputable def normalScale (L : Label B N0) (n : ℕ) : ℝ :=
  ((ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) / (ChartScales.carrier h n : ℝ)) *
    radialScale L n

theorem normalScale_pos (L : Label B N0) (n : ℕ) : 0 < normalScale L n :=
  mul_pos (div_pos (chartCoefficients_frequency_pos (B := B) (N0 := N0) 0 L _)
    (chartCoefficients_frequency_pos (B := B) (N0 := N0) 0 L _)) (radialScale_pos L n)

theorem normal_eq_copy (j : Fin 2) (L : Label B N0) (n : ℕ)
    (U : LocalSignedRequest.SlowRegion (2 * h)) (k : TorusInverse.Frequency) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1)
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core) :
    (chartCoefficients j L).normal
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
      (PrimaryResidualClass.directions (commonContext B)) n x =
      normalScale L n • (phases B N0 j).phase.normal L (phasePoint L (copyPoint j L n k x)) := by
  obtain ⟨hF,hG⟩ := native_base_differentiable j L n k hR hT
  have hp := PrimaryMaterialDefect.differentiableAt_phase
    ((phases B N0 j).phase.epsilon L) ((phases B N0 j).phase.p L)
    ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
    ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L) (slotPoint j L n k x) hF hG
  have hd := (((hp.hasFDerivAt.comp x (slotPoint_hasFDerivAt j L n k x)).const_mul
    ((ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) / (ChartScales.carrier h n :
        ℝ)))).congr_of_eventuallyEq
      (phase_germ j L n k hc)
  have htheta : PhaseCalculus.phaseNormal ((phases B N0 j).phase.epsilon L)
      ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
      ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L) (slotPoint j L n k x) =
        (phases B N0 j).phase.normal L (phasePoint L (copyPoint j L n k x)) := by
    rw [PhaseCalculus.phaseNormal_formula _ _ _ _ _ _ (slotPoint j L n k x)
      ((phases B N0 j).epsilon_ne L) hF hG]
    unfold PhaseJetBounds.PhaseFamily.normal
    simp only [phasePoint]
    rw [PhaseCalculus.phaseNormal_formula _ _ _ _ _ _
      ((copyPoint j L n k x).1, ((phases B N0 j).phase.theta L, (copyPoint j L n k x).2.2))
      ((phases B N0 j).epsilon_ne L) hF hG]
    rfl
  rw [← htheta]
  have hrad : (chartCoefficients j L).radius n x = x.1.1 := rfl
  have heps : (phases B N0 j).phase.epsilon L = ChartScales.epsilon h (BaseChartJets.cellBand L) :=
      rfl
  ext i
  fin_cases i <;>
    simp only [LinearWaveBounds.WaveCoefficients.normal, phaseNormal, along, hd.fderiv, heps,
        smul_apply, ContinuousLinearMap.comp_apply, slotLinear_radial, map_smul, smul_eq_mul,
            slotLinear_angular j L n x, hrad, slotLinear_axial, Fin.zero_eta, Fin.isValue,
                Matrix.cons_val_zero, normalScale, PhaseCalculus.phaseNormal, PiLp.smul_apply,
                    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
  · ring
  · rw [slotPoint_radius]
    field_simp [(radialScale_pos L n).ne', hR.ne']
  · ring

end PhaseNormal

section BaseAction

variable {B N0 : ℕ}

theorem frequency_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint} (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1) :
    (chartCoefficients j L).frequencyBase n =ᶠ[𝓝 x]
      fun y => clockScale L n * (phases B N0 j).phase.F L (copyPoint j L n k y).1 := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst.fst).mem_nhds hR,
    (isOpen_lt continuous_const continuous_fst.snd.fst.fst).mem_nhds hT] with y hyR hyT
  change BaseContextAssembly.frequencySlow certificate modulation upper B n
    (BaseContextAssembly.slowCoordinates y.1) = _
  rw [phase_frequency, clockScale_eq]
  change _ = _ * BaseContextAssembly.frequencySlow certificate modulation upper B _
    (nativeSlow L (toAbsolute n y.1))
  rw [nativeSlow_toAbsolute_eq_slowChange]
  exact ActualPhaseDefect.frequencySlow_change certificate modulation upper B n _ hyT hyR

theorem axial_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint} (hT : 0 < x.1.2.1.1) :
    (chartCoefficients j L).axialBase n =ᶠ[𝓝 x]
      fun y => velocityScale L n * (phases B N0 j).phase.G L (copyPoint j L n k y).1 := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst.snd.fst.fst).mem_nhds hT] with y hyT
  change BaseContextAssembly.axialSlow certificate modulation upper B n
    (BaseContextAssembly.slowCoordinates y.1) = _
  rw [phase_axial]
  change _ = _ * BaseContextAssembly.axialSlow certificate modulation upper B _
    (nativeSlow L (toAbsolute n y.1))
  rw [nativeSlow_toAbsolute_eq_slowChange]
  exact ActualPhaseDefect.axialSlow_change certificate modulation upper B n _ hyT

theorem slow_radial_derivative (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (a : ℝ) (f : PhaseCalculus.Slow → ℝ) {x : FullPoint}
    (hf : DifferentiableAt ℝ f (copyPoint j L n k x).1) :
    along ((PrimaryResidualClass.directions (commonContext B)).radialField n)
      (fun y => a * f (copyPoint j L n k y).1) x =
      a * radialScale L n * PhaseCalculus.slowR f (copyPoint j L n k x).1 := by
  have hd := ((hf.hasFDerivAt.comp x (copyPoint_hasFDerivAt j L n k x).fst).const_mul a).fderiv
  simp only [Function.comp_def] at hd
  have hr := congrArg Prod.fst (slotLinear_radial j L n x)
  change (copyLinear j L n ((PrimaryResidualClass.directions (commonContext B)).radialField n x)).1
      =
    radialScale L n • (1,(0,0)) at hr
  simp only [along, hd, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', hr, map_smul, smul_eq_mul, PhaseCalculus.slowR]
  ring

theorem copy_shear_function (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (v : Native → Space) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1) :
    LinearWaveResidual.shear ((chartCoefficients j L).radius n)
      ((chartCoefficients j L).frequencyBase n) ((chartCoefficients j L).axialBase n)
      ((PrimaryResidualClass.directions (commonContext B)).radialField n)
      (fun y => velocityScale L n • CurlClassBounds.complexify (v (copyPoint j L n k y))) x =
    (clockScale L n * velocityScale L n) • CurlClassBounds.complexify
      (PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L (copyPoint j L n k x).1)
        ((phases B N0 j).phase.shear L (phasePoint L (copyPoint j L n k x)))
        (v (copyPoint j L n k x))) := by
  obtain ⟨hF,hG⟩ := native_base_differentiable j L n k hR hT
  have hf := frequency_germ j L n k hR hT
  have hg := axial_germ j L n k hT
  have hfr := (ParticularWaveAssembly.along_germ hf
    ((PrimaryResidualClass.directions (commonContext B)).radialField n)).eq_of_nhds
  have hgr := (ParticularWaveAssembly.along_germ hg
    ((PrimaryResidualClass.directions (commonContext B)).radialField n)).eq_of_nhds
  rw [slow_radial_derivative j L n k _ _ hF] at hfr
  rw [slow_radial_derivative j L n k _ _ hG, ← clockScale_factor] at hgr
  have hr := slotPoint_radius j L n k x
  change (copyPoint j L n k x).1.1 = radialScale L n * x.1.1 at hr
  unfold LinearWaveResidual.shear
  rw [hfr, hgr, hf.eq_of_nhds]
  have hrad : (chartCoefficients j L).radius n x = x.1.1 := rfl
  ext i
  fin_cases i <;>
    simp [hrad, PrimaryCopyBridge.baseOperator_apply, MovingFrameODE.baseAction,
      PhaseJetBounds.PhaseFamily.shear, PhaseEstimates.shearVector,
      MovingFrameODE.pack, MovingFrameODE.tail, MovingFrameODE.unitTheta,
      CurlClassBounds.complexify_apply, phasePoint, hr, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_neg] <;> ring

theorem copy_shear (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint} (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1) :
    LinearWaveResidual.shear ((chartCoefficients j L).radius n)
      ((chartCoefficients j L).frequencyBase n) ((chartCoefficients j L).axialBase n)
      ((PrimaryResidualClass.directions (commonContext B)).radialField n)
      (copyAmplitude j L n k) x =
    (clockScale L n * velocityScale L n) • CurlClassBounds.complexify
      (PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L (copyPoint j L n k x).1)
        ((phases B N0 j).phase.shear L (phasePoint L (copyPoint j L n k x)))
        (attachedRawVelocity j L (copyPoint j L n k x))) :=
  copy_shear_function j L n k (attachedRawVelocity j L) hR hT

end BaseAction

section ScaledDynamics

variable {B N0 : ℕ}

theorem epsilon_scale (L : Label B N0) (n : ℕ) :
    ChartScales.epsilon h n * radialScale L n ^ 2 =
      clockScale L n * ChartScales.epsilon h (BaseChartJets.cellBand L) := by
  unfold radialScale clockScale ChartScales.epsilon
  rw [div_pow, Real.sq_sqrt (ChartScales.Q_pos n).le,
    Real.sq_sqrt (ChartScales.Q_pos (BaseChartJets.cellBand L)).le,
    Real.rpow_add (ChartScales.Q_pos n),
    Real.rpow_add (ChartScales.Q_pos (BaseChartJets.cellBand L)),
    Real.rpow_one, Real.rpow_one]
  field_simp [(ChartScales.Q_pos (BaseChartJets.cellBand L)).ne',
    (Real.rpow_pos_of_pos (ChartScales.Q_pos (BaseChartJets.cellBand L)) h).ne']

theorem damping_scale (L : Label B N0) (n : ℕ) (N : Space) :
    ChartScales.epsilon h n * (ChartScales.carrier h n : ℝ)^2 * ‖normalScale L n • N‖^2 =
      clockScale L n * (ChartScales.epsilon h (BaseChartJets.cellBand L) *
        (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ)^2 * ‖N‖^2) := by
  have hk : (ChartScales.carrier h n : ℝ) ≠ 0 := (chartCoefficients_frequency_pos 0 L n).ne'
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold normalScale
  rw [mul_pow, div_pow]
  calc
    _ = (ChartScales.epsilon h n * radialScale L n ^ 2) *
        (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ)^2 * ‖N‖^2 := by field_simp
    _ = _ := by rw [epsilon_scale]; ring

/-- Copy velocity, given by `velocityScale L n • attachedRawVelocity j L (copyPoint j L n k x)`. -/
noncomputable def copyVelocity (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : Space :=
  velocityScale L n • attachedRawVelocity j L (copyPoint j L n k x)

/-- Copy motion, given by `(normalScale L n * clockScale L n) • (phases B N0 j).phase.velocity L
(phasePoint L (copyPoint j L n k x))`. -/
noncomputable def copyMotion (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : Space :=
  (normalScale L n * clockScale L n) •
    (phases B N0 j).phase.velocity L (phasePoint L (copyPoint j L n k x))

/-- Copy action as an element of `Space`. -/
noncomputable def copyAction (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : Space :=
  (clockScale L n * velocityScale L n) •
    PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L (copyPoint j L n k x).1)
      ((phases B N0 j).phase.shear L (phasePoint L (copyPoint j L n k x)))
      (attachedRawVelocity j L (copyPoint j L n k x))

theorem copyVelocity_differentiable (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint} (hT : 0 < x.1.2.1.1) :
    DifferentiableAt ℝ (copyVelocity j L n k) x :=
  (((attachedRawVelocity_smooth B N0 j L).contDiffAt
    (WaveEdgeExtension.nativeSlowDomain_open.mem_nhds (copyPoint_time_pos j L n k
        hT))).differentiableAt
      (by simp) |>.comp x (copyPoint_hasFDerivAt j L n k x).differentiableAt).fun_const_smul _

theorem copyVelocity_ode (j : Fin 2) (L : Label B N0) (n : ℕ)
    (U : LocalSignedRequest.SlowRegion (2 * h)) (k : TorusInverse.Frequency) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1)
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core)
    (hg : chartCutoff j L n x ≠ 0) :
    along ((PrimaryResidualClass.directions (commonContext B)).fastField n)
      (copyVelocity j L n k) x =
      TangentProjection.projectedRhs
        ((chartCoefficients j L).normal
          (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
          (PrimaryResidualClass.directions (commonContext B)) n x)
        (copyMotion j L n k x) (copyVelocity j L n k x) (copyAction j L n k x) 0
        (ChartScales.epsilon h n * (ChartScales.carrier h n : ℝ)^2 *
          ‖(chartCoefficients j L).normal
            (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
            (PrimaryResidualClass.directions (commonContext B)) n x‖^2) := by
  let z := copyPoint j L n k x
  have hgz : gaussian L z ≠ 0 := by rwa [cutoff_eq_copy j L n k hc] at hg
  have hd := attachedVelocity_hasDerivAt j L (copyPoint_time_pos j L n k hT) hgz
  have htime : HasDerivAt (fun t : ℝ => z.2.2 + t * clockScale L n) (clockScale L n) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (clockScale L n)).const_add z.2.2
  have hd' := (hd.scomp_of_eq (0 : ℝ) htime (by simp [z])).const_smul (velocityScale L n)
  have hline : HasDerivAt
      (fun t : ℝ => x+t • (PrimaryResidualClass.directions (commonContext B)).fastField n x)
      ((PrimaryResidualClass.directions (commonContext B)).fastField n x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      ((PrimaryResidualClass.directions (commonContext B)).fastField n x)).const_add x
  have hh := (copyVelocity_differentiable j L n k hT).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hline (by simp)
  simp only [Function.comp_def, copyVelocity, copyPoint_fast_line] at hh
  simp only [Function.comp_def, z] at hd'
  have he := hh.unique hd'
  change along ((PrimaryResidualClass.directions (commonContext B)).fastField n) (copyVelocity j L
      n k) x = _ at he
  rw [he, normal_eq_copy j L n U k hR hT hc, damping_scale]
  have hs := NormalScaling.projectedRhs_rescale
    ((phases B N0 j).phase.normal L (phasePoint L z))
    ((phases B N0 j).phase.velocity L (phasePoint L z))
    (attachedRawVelocity j L z)
    (PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L z.1)
      ((phases B N0 j).phase.shear L (phasePoint L z)) (attachedRawVelocity j L z))
    (0 : Space) (clockScale L n) (velocityScale L n)
    (ChartScales.epsilon h (BaseChartJets.cellBand L) *
      (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ)^2 *
      ‖(phases B N0 j).phase.normal L (phasePoint L z)‖^2) (normalScale_pos L n).ne'
  simpa only [copyVelocity, copyMotion, copyAction, smul_zero, smul_smul, mul_comm, z] using hs.symm

theorem pressure_scale_algebra {K Kr r : ℝ} (hK : K ≠ 0) (hKr : Kr ≠ 0)
    (hr : r ≠ 0) (b c : ℝ) :
    b ^ 2 • (Complex.I * (c : ℂ) / (Kr : ℂ)) =
      Complex.I * (((b * r * b / ((Kr / K) * r)) * c : ℝ) : ℂ) / (K : ℂ) := by
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow]
  field_simp [Complex.ofReal_ne_zero.mpr hK, Complex.ofReal_ne_zero.mpr hKr,
    Complex.ofReal_ne_zero.mpr hr]

theorem copyPressure_projected (j : Fin 2) (L : Label B N0) (n : ℕ)
    (U : LocalSignedRequest.SlowRegion (2 * h)) (k : TorusInverse.Frequency) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1)
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core)
    (hg : chartCutoff j L n x ≠ 0) :
    copyPressure j L n k x =
      ParticularWaveBounds.projectedPressure (ChartScales.carrier h n)
        ((chartCoefficients j L).normal
          (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
          (PrimaryResidualClass.directions (commonContext B)) n)
        (copyMotion j L n k) (copyVelocity j L n k) (copyAction j L n k) (fun _ => 0) x := by
  have hgz : gaussian L (copyPoint j L n k x) ≠ 0 := by rwa [cutoff_eq_copy j L n k hc] at hg
  have hk : (ChartScales.carrier h n : ℝ) ≠ 0 := (chartCoefficients_frequency_pos 0 L n).ne'
  have hkr : (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) ≠ 0 :=
    (chartCoefficients_frequency_pos 0 L _).ne'
  unfold copyPressure ParticularWaveBounds.projectedPressure
  rw [attachedPressure_eq j L hgz, normal_eq_copy j L n U k hR hT hc]
  simp only [copyMotion, copyVelocity, copyAction]
  rw [show (0 : Space) = (clockScale L n * velocityScale L n) • (0 : Space) by simp,
    NormalScaling.pressureCoefficient_rescale _ _ _ _ _ _ _ (normalScale_pos L n).ne']
  rw [clockScale_factor]
  simpa only [smul_zero, normalScale] using
    pressure_scale_algebra hk hkr (radialScale_pos L n).ne' (velocityScale L n)
      (TangentProjection.pressureCoefficient
        ((phases B N0 j).phase.normal L (phasePoint L (copyPoint j L n k x)))
        ((phases B N0 j).phase.velocity L (phasePoint L (copyPoint j L n k x)))
        (attachedRawVelocity j L (copyPoint j L n k x))
        (PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L (copyPoint j L n k x).1)
          ((phases B N0 j).phase.shear L (phasePoint L (copyPoint j L n k x)))
          (attachedRawVelocity j L (copyPoint j L n k x))) 0)

theorem copy_principal_zero (j : Fin 2) (L : Label B N0) (n : ℕ)
    (U : LocalSignedRequest.SlowRegion (2 * h)) (k : TorusInverse.Frequency) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1)
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core)
    (hg : chartCutoff j L n x ≠ 0) :
    LinearWaveResidual.principal (ChartScales.epsilon h n) (ChartScales.carrier h n)
      ((chartCoefficients j L).radius n) ((chartCoefficients j L).frequencyBase n)
      ((chartCoefficients j L).axialBase n)
      ((PrimaryResidualClass.directions (commonContext B)).radialField n)
      (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
      ((PrimaryResidualClass.directions (commonContext B)).axialField
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n)
      ((PrimaryResidualClass.directions (commonContext B)).fastField n)
      ((chartCoefficients j L).phase n) (copyAmplitude j L n k) (copyPressure j L n k) x = 0 := by
  have ha : CurlClassBounds.complexify (copyAction j L n k x) =
      LinearWaveResidual.shear ((chartCoefficients j L).radius n)
        ((chartCoefficients j L).frequencyBase n) ((chartCoefficients j L).axialBase n)
        ((PrimaryResidualClass.directions (commonContext B)).radialField n)
        (fun y => CurlClassBounds.complexify (copyVelocity j L n k y)) x := by
    have he := (copy_shear j L n k hR hT).symm
    simp only [copyAction, copyVelocity, map_smul] at he ⊢
    exact he
  have hh := ParticularWaveBounds.principal_eq_neg_source_of_projected
    (ChartScales.epsilon h n) (ChartScales.carrier h n) (chartCoefficients_frequency_pos j L n).ne'
    ((chartCoefficients j L).radius n) ((chartCoefficients j L).frequencyBase n)
    ((chartCoefficients j L).axialBase n) ((chartCoefficients j L).phase n)
    ((PrimaryResidualClass.directions (commonContext B)).radialField n)
    (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
    ((PrimaryResidualClass.directions (commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n)
    ((PrimaryResidualClass.directions (commonContext B)).fastField n)
    (copyVelocity j L n k) (copyMotion j L n k) (copyAction j L n k) (fun _ => 0)
    (copyVelocity_differentiable j L n k hT) (copyVelocity_ode j L n U k hR hT hc hg) ha
  have hp := copyPressure_projected j L n U k hR hT hc hg
  dsimp only [LinearWaveBounds.WaveCoefficients.normal] at hp
  ext i
  have hi := congrFun hh i
  simp only [LinearWaveResidual.principal] at hi
  rw [← hp] at hi
  simp only [LinearWaveResidual.principal, copyVelocity, map_smul, copyAmplitude,
    map_zero, Pi.neg_apply, Pi.zero_apply, neg_zero] at hi ⊢
  exact hi

/-- The global attachment only satisfies the homogeneous equation on the
actual Gaussian support.  No band-nearness or global slot premise occurs. -/
theorem principal_zero_on_cutoff (j : Fin 2) (L : Label B N0) (n : ℕ)
    (U : LocalSignedRequest.SlowRegion (2 * h)) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1) (hg : chartCutoff j L n x ≠ 0) :
    (chartCoefficients j L).principal
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
      (PrimaryResidualClass.directions (commonContext B)) n x = 0 := by
  classical
  by_cases hc : ∃ k : TorusInverse.Frequency, (copyPoint j L n k x).2 ∈ (clockWindow L).core
  · obtain ⟨k,hk⟩ := hc
    have he := (PeriodizedWaveBounds.principal_germ (amplitude_germ j L n k hk)
      (pressure_germ j L n k hk) (ChartScales.epsilon h n) (ChartScales.carrier h n)
      ((chartCoefficients j L).radius n) ((chartCoefficients j L).frequencyBase n)
      ((chartCoefficients j L).axialBase n) ((chartCoefficients j L).phase n)
      ((PrimaryResidualClass.directions (commonContext B)).radialField n)
      (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
      ((PrimaryResidualClass.directions (commonContext B)).axialField
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n)
      ((PrimaryResidualClass.directions (commonContext B)).fastField n)).eq_of_nhds
    exact he.trans (copy_principal_zero j L n U k hR hT hk hg)
  · obtain ⟨hA,hP⟩ := coefficient_zero_germs j L n (not_exists.mp hc)
    have he := (PeriodizedWaveBounds.principal_germ hA hP
      (ChartScales.epsilon h n) (ChartScales.carrier h n)
      ((chartCoefficients j L).radius n) ((chartCoefficients j L).frequencyBase n)
      ((chartCoefficients j L).axialBase n) ((chartCoefficients j L).phase n)
      ((PrimaryResidualClass.directions (commonContext B)).radialField n)
      (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
      ((PrimaryResidualClass.directions (commonContext B)).axialField
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)) n)
      ((PrimaryResidualClass.directions (commonContext B)).fastField n)).eq_of_nhds
    exact he.trans (by simp [])

end ScaledDynamics

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact cutoff and curl algebra only needs the localized principal
equation.  The actual primary application below supplies every hypothesis. -/
theorem localLinearIdentity (a : LinearWaveBounds.WaveCoefficients E)
    (s : WeightedClasses.StripData E) (d : LinearWaveBounds.GraphDirections E)
    (ψ : ℕ → E → ℝ) (f : ℕ → E → ComplexVector) (n : ℕ)
    {Ω : Set E} (hg : LocalizedWaveBounds.ExactOn ((a.withCutoff ψ).addAmplitude f) s d n Ω)
    {x : E} (hx : x ∈ Ω)
    (hA : ∀ i, DifferentiableAt ℝ (fun y => a.amplitude n y i) x)
    (hψ : DifferentiableAt ℝ (ψ n) x)
    (hf : ∀ i, DifferentiableAt ℝ (fun y => f n y i) x)
    (hz : ψ n x • a.principal s d n x = 0) (i : Fin 3) :
    (((a.withCutoff ψ).addAmplitude f).harmonicResidual s d n x i).re =
      (vectorMode (a.frequency n) (a.phase n) (a.goodCoefficient s d ψ f n) x i).re +
      (vectorMode (a.frequency n) (a.phase n)
        (LinearWaveBounds.excludedSlotError d ψ a.amplitude 0 n) x i).re := by
  have hcut := LocalizedWaveBounds.principal_cutoff_at a s d ψ 0 n x hA hψ
  simp only [Pi.zero_apply, add_zero, hz, zero_add] at hcut
  have hadd := LocalizedWaveBounds.principal_add_at (a.withCutoff ψ) s d f n x
    (fun i => hψ.smul (hA i)) hf
  have he : ((a.withCutoff ψ).addAmplitude f).principal s d n x +
      ((a.withCutoff ψ).addAmplitude f).remainder s d n x =
      a.goodCoefficient s d ψ f n x + LinearWaveBounds.excludedSlotError d ψ a.amplitude 0 n x := by
    rw [hadd, hcut]
    change _ + a.principalVelocity s d f n x + _ =
      (a.principalVelocity s d f n x + _) + _
    abel
  rw [LocalizedWaveBounds.harmonicResidual_eq_on hg hx]
  change ((((a.withCutoff ψ).addAmplitude f).principal s d n x +
    ((a.withCutoff ψ).addAmplitude f).remainder s d n x) i *
      carrier (a.frequency n) (a.phase n) x).re = _
  rw [he]
  simp only [Pi.add_apply, add_mul, Complex.add_re]
  rfl

end Algebra

section Residual

variable {B N0 : ℕ}

theorem absoluteChart_positive (n : ℕ) {x : FullPoint}
    (hx : x ∈ ActualPrimaryCoherence.positiveRadialChart) :
    ActualPrimaryCoherence.absoluteChart n x ∈ ActualPrimaryCoherence.positiveRadialAbsolute :=
  ⟨mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n)) hx.1, mul_pos (ChartScales.Q_pos n) hx.2⟩

theorem amplitude_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((chartCoefficients j L).amplitude n) ActualPrimaryCoherence.positiveRadialChart
        := by
  exact (((ActualPrimaryCoherence.absoluteAmplitude_smooth j L).comp
    (ActualPrimaryCoherence.absoluteChart n).contDiff.contDiffOn
    (fun _ hx => (absoluteChart_positive n hx).2)).const_smul
      (ChartScales.Q n ^ CoordinateAlgebra.A h))

theorem pressure_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((chartCoefficients j L).pressure n) ActualPrimaryCoherence.positiveRadialChart
        := by
  exact (((ActualPrimaryCoherence.absolutePressureCoefficient_smooth j L).comp
    (ActualPrimaryCoherence.absoluteChart n).contDiff.contDiffOn
    (fun _ hx => (absoluteChart_positive n hx).2)).const_smul
      (ChartScales.Q n ^ (2 * CoordinateAlgebra.A h)))

theorem cutoff_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiff ℝ ∞ (chartCutoff j L n) :=
  (periodicGaussian_smooth j L).comp (((toAbsolute_smooth n).comp contDiff_fst).snd)

theorem phase_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((chartCoefficients j L).phase n) ActualPrimaryCoherence.positiveRadialChart :=
        by
  rw [ActualPrimaryCoherence.phase_representation]
  exact contDiffOn_const.mul ((ActualPrimaryCoherence.absolutePhase_smooth j L).comp
    (ActualPrimaryCoherence.absoluteChart n).contDiff.contDiffOn
    (fun _ hx => absoluteChart_positive n hx))

theorem exactAmplitude_smooth (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((piece U j L).exactCoefficients.amplitude n)
        ActualPrimaryCoherence.positiveRadialChart := by
  have he : (piece U j L).exactCoefficients.amplitude n = fun x =>
      ChartScales.Q n ^ CoordinateAlgebra.A h •
        ActualPrimaryCoherence.absoluteExactAmplitude j L (ActualPrimaryCoherence.absoluteChart n
            x) :=
    funext (ActualPrimaryCoherence.exactAmplitude_representation U j L n)
  rw [he]
  exact ((ActualPrimaryCoherence.absoluteExactAmplitude_smooth j L).comp
    (ActualPrimaryCoherence.absoluteChart n).contDiff.contDiffOn
    (fun _ hx => absoluteChart_positive n hx)).const_smul _

theorem curl_smooth (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (((chartCoefficients j L).withCutoff (chartCutoff j L)).curlCorrection
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
      (PrimaryResidualClass.directions (commonContext B)) n)
          ActualPrimaryCoherence.positiveRadialChart := by
  have hc := (cutoff_smooth j L n).contDiffOn.smul (amplitude_smooth j L n)
  apply ((exactAmplitude_smooth U j L n).sub hc).congr
  intro x _
  change _ = (chartCutoff j L n x • (chartCoefficients j L).amplitude n x +
    ((chartCoefficients j L).withCutoff (chartCutoff j L)).curlCorrection
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
      (PrimaryResidualClass.directions (commonContext B)) n x) -
        chartCutoff j L n x • (chartCoefficients j L).amplitude n x
  rw [add_sub_cancel_left]

theorem base_smooth (j : Fin 2) (L : Label B N0) (n : ℕ) {x : FullPoint}
    (hx : x ∈ ActualPrimaryCoherence.positiveRadialChart) :
    ContDiffAt ℝ ∞ ((chartCoefficients j L).radialBase n) x ∧
    ContDiffAt ℝ ∞ ((chartCoefficients j L).frequencyBase n) x ∧
    ContDiffAt ℝ ∞ ((chartCoefficients j L).axialBase n) x := by
  have hs : ContDiffAt ℝ ∞ (fun y : FullPoint => BaseContextAssembly.slowCoordinates y.1) x :=
    BaseContextAssembly.slowCoordinates.contDiff.contDiffAt.comp x contDiffAt_fst
  exact ⟨(BaseContextAssembly.radialSlow_smoothAt certificate modulation upper B n hx.2).comp x hs,
    (ActualPrimaryCoherence.frequencySlow_smoothAt B n hx.1 hx.2).comp x hs,
    (ActualPrimaryCoherence.axialSlow_smoothAt B n hx.2).comp x hs⟩

theorem exactOn (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) :
    LocalizedWaveBounds.ExactOn (piece U j L).exactCoefficients
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
      (PrimaryResidualClass.directions (commonContext B)) n
          ActualPrimaryCoherence.positiveRadialChart := by
  let ha := chartCoefficients_angular j L
  have hp : ContDiffOn ℝ ∞ ((piece U j L).exactCoefficients.pressure n)
      ActualPrimaryCoherence.positiveRadialChart :=
    (cutoff_smooth j L n).contDiffOn.smul (pressure_smooth j L n)
  have hA := exactAmplitude_smooth U j L n
  have hΦ := phase_smooth j L n
  refine ⟨ActualPrimaryCoherence.positiveRadialChart_open, ?_, hΦ,
    (fun i => (contDiffOn_pi.mp hA) i), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hh : ContDiffAt ℝ ∞ (fun y : FullPoint =>
        RadialPullback.radialJacobian (ChartScales.radialExponent h) y.1.1) x :=
      contDiffAt_const.mul (contDiffAt_fst.fst.rpow_const_of_ne hx.1.ne')
    exact hh.contDiffWithinAt
  · intro x _
    exact differentiableAt_fst.fst
  · intro x hx
    exact (base_smooth j L n hx).1.differentiableAt (by simp)
  · intro x hx
    exact (base_smooth j L n hx).2.1.differentiableAt (by simp)
  · intro x hx
    exact (base_smooth j L n hx).2.2.differentiableAt (by simp)
  · intro x hx
    exact (hp.contDiffAt (ActualPrimaryCoherence.positiveRadialChart_open.mem_nhds
        hx)).differentiableAt (by
        simp)
  · intro x hx
    exact hx.1.ne'
  · intro x hx
    change fderiv ℝ (fun y : FullPoint => y.1.1) x
      ((PrimaryResidualClass.directions (commonContext B)).radialField n x) = 1
    rw [(hasFDerivAt_fst.fst (x := x)).fderiv]
    simp [LinearWaveBounds.GraphDirections.radialField, PrimaryResidualClass.directions,
      commonContext, CommonBaseContext.context, CommonBaseContext.operators,
      CorrectionState.graphOperators, CommonBaseContext.reconstruction]
  · intro x hx i
    exact ((CopyAngularInvariance.base_invariant (ha.radius n) (ha.radialBase n)
      (ha.frequencyBase n) (ha.axialBase n)).component i).along_zero x
  · intro i x hx
    exact ((ha.corrected_amplitude (BaseContextAssembly.nativeStrip nominal U) (commonContext B)
        n).component i).along_zero x
  · obtain ⟨m,hm⟩ := ha.phase n
    exact ⟨m, fun x hx => hm.directional_eq
      ((hΦ.contDiffAt (ActualPrimaryCoherence.positiveRadialChart_open.mem_nhds
          hx)).differentiableAt (by
          simp))⟩
  · intro x hx
    exact (ha.corrected_pressure (BaseContextAssembly.nativeStrip nominal U) (commonContext B)
        n).along_zero x

/-- Exact decomposition of the same selected, attached, periodized and
curl-corrected primary piece.  The Gaussian derivative is retained. -/
theorem linearResidual_eq (U : LocalSignedRequest.SlowRegion (2 * h))
    (j : Fin 2) (L : Label B N0) (n : ℕ) {x : FullPoint}
    (hx : x ∈ ActualPrimaryCoherence.positiveRadialChart) (i : Fin 3) :
    (piece U j L).linearResidual n x i =
      (piece U j L).linearGoodField n x i + (piece U j L).excluded n x i := by
  let a := chartCoefficients j L
  let s := HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U)
  let d := PrimaryResidualClass.directions (commonContext B)
  let ψ := chartCutoff j L
  let f := (a.withCutoff ψ).curlCorrection s d
  have hA : ∀ i, DifferentiableAt ℝ (fun y => a.amplitude n y i) x := fun i =>
    (((contDiffOn_pi.mp (amplitude_smooth j L n)) i).contDiffAt
      (ActualPrimaryCoherence.positiveRadialChart_open.mem_nhds hx)).differentiableAt (by simp)
  have hψ : DifferentiableAt ℝ (ψ n) x := (cutoff_smooth j L n).differentiable (by simp) x
  have hf : ∀ i, DifferentiableAt ℝ (fun y => f n y i) x := fun i =>
    (((contDiffOn_pi.mp (curl_smooth U j L n)) i).contDiffAt
      (ActualPrimaryCoherence.positiveRadialChart_open.mem_nhds hx)).differentiableAt (by simp)
  have hz : ψ n x • a.principal s d n x = 0 := by
    by_cases hh : ψ n x = 0
    · rw [hh, zero_smul]
    · rw [principal_zero_on_cutoff j L n U hx.1 hx.2 hh, smul_zero]
  exact localLinearIdentity a s d ψ f n (exactOn U j L n) hx hA hψ hf hz i

theorem linearResidual_eq_on_strip (j : Fin 2) (L : Label B N0) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) (i : Fin 3) :
    (piece standardRegion j L).linearResidual n x i =
      (piece standardRegion j L).linearGoodField n x i +
        (piece standardRegion j L).excluded n x i :=
  linearResidual_eq standardRegion j L n
    ⟨BaseContextAssembly.nativeStrip_radius nominal standardRegion hx,
      BaseContextAssembly.nativeStrip_time nominal standardRegion hx⟩ i

end Residual

end NavierStokes.ActualPrimaryDynamics
