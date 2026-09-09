/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedNativeRegularity

@[expose] public section

/-!
# Zeros of the actual signed physical coefficients

The native dyadic mask vanishes at both faces and outside the open native
band.  This file transfers that literal zero to the canonical physical
copy family and to every current-band representation of the same label.
The current state and the native reference requests are arbitrary.
-/

noncomputable section

namespace NavierStokes.ActualSignedPhysicalZeros

open Set Function Filter ProblemStatement PhysicalWaveSum PhysicalCopyBounds
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualSignedExterior
open scoped Topology ContDiff BigOperators


abbrev Label := ActualSignedPhysicalBinding.Label
abbrev Point := ActualSignedCoherence.Point
abbrev FullPoint := ActualSignedCoherence.FullPoint
abbrev Frequency := TorusInverse.Frequency

variable {B N0 : ℕ}

theorem physicalLift_coordinateQ (n : ℕ) {w : SpaceTime} (hw : w ∈ preterminal) :
    SimilarityCoordinates.coordinateQ (2 * h)
      ((ActualSignedPhysicalData.cylinderZero (PhysicalGraphBounds.physicalLift h n w)).1.2.1.2,
       (ActualSignedPhysicalData.cylinderZero (PhysicalGraphBounds.physicalLift h n w)).1.2.1.1) =
      physicalQ h w / ChartScales.Q n := by
  have he := congrArg (fun p : PhaseCalculus.Slow => (p.2.2, p.2.1))
    (physicalLift_slow n w)
  change _ = (PhysicalMeanJetBounds.graph h n 0 w).2.1 at he
  dsimp only at he
  rw [he]
  exact PhysicalMeanJetBounds.graph_q_eq outgoing.data.h_pos outgoing.data.h_lt_half n 0 hw

theorem primary_mask_physicalLift_zero (l : Label B N0) (m n : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q n ∉ Ioo (1 / 2 : ℝ) 2) :
    (ActualSignedPhysicalBinding.primary l).mask m
      (ActualSignedPhysicalData.cylinderZero (PhysicalGraphBounds.physicalLift h n w)) = 0 := by
  apply ActualSignedNativeRegularity.primary_mask_zero_outside
  rwa [physicalLift_coordinateQ n hw]

section CanonicalFamily

variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)

theorem canonical_potential_amplitude_zero_of_nativeQ (l : Label B N0) (i : Fin 3)
    (k : Frequency) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).potentialCopies slots outgoing.data.h_pos.le i).amplitude k
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l))
      (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l) w) = 0 := by
  classical
  change ((family s).copyAt (fun L => ActualSignedPhysicalData.potentialFamily
    slots outgoing.data.h_pos.le ((family s).singleton L) i) (nativeLabel l)).amplitude k _ _ = 0
  erw [DependentSignedPhysicalFamily.Family.copyAt_active]
  by_contra hn
  obtain ⟨_, _, hm, _⟩ := ActualSignedPhysicalData.potential_amplitude_inputs
    slots outgoing.data.h_pos.le ((family s).singleton (nativeLabel l)) i k _ _ hn
  apply hm
  change (ActualSignedPhysicalBinding.primary (actualLabel (nativeLabel l))).mask
    (ActualSignedPhysicalBinding.reference l) _ = 0
  rw [actualLabel_nativeLabel]
  exact primary_mask_physicalLift_zero l _ _ hw hq

theorem canonical_pressure_amplitude_zero_of_nativeQ (l : Label B N0)
    (k : Frequency) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).pressureCopies slots outgoing.data.h_pos.le).amplitude k
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l))
      (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l) w) = 0 := by
  classical
  change ((family s).copyAt (fun L => ActualSignedPhysicalData.pressureFamily
    slots outgoing.data.h_pos.le ((family s).singleton L)) (nativeLabel l)).amplitude k _ _ = 0
  erw [DependentSignedPhysicalFamily.Family.copyAt_active]
  by_contra hn
  obtain ⟨_, _, hm, _⟩ := ActualSignedPhysicalData.pressure_amplitude_inputs
    slots outgoing.data.h_pos.le ((family s).singleton (nativeLabel l)) k _ _ hn
  apply hm
  change (ActualSignedPhysicalBinding.primary (actualLabel (nativeLabel l))).mask
    (ActualSignedPhysicalBinding.reference l) _ = 0
  rw [actualLabel_nativeLabel]
  exact primary_mask_physicalLift_zero l _ _ hw hq

theorem canonical_potential_term_zero_of_nativeQ (l : Label B N0) (i : Fin 3)
    (k : Frequency) (a r0 : ℝ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).potentialCopies slots outgoing.data.h_pos.le i).term a h r0
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l)) k w = 0 := by
  apply globalWave_eq_zero
  change ((family s).potentialCopies slots outgoing.data.h_pos.le i).amplitude k
    (ActualSignedPhysicalData.positiveIndex (nativeLabel l))
    (commonLift h (ActualSignedPhysicalBinding.reference l)
      (((family s).potentialCopies slots outgoing.data.h_pos.le i).gap (nativeLabel l)) w) = 0
  rw [potential_gap, ActualSignedPhysicalData.commonLift_zero]
  exact canonical_potential_amplitude_zero_of_nativeQ s l i k hw hq

theorem canonical_pressure_term_zero_of_nativeQ (l : Label B N0)
    (k : Frequency) (a r0 : ℝ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).pressureCopies slots outgoing.data.h_pos.le).term a h r0
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l)) k w = 0 := by
  apply globalWave_eq_zero
  change ((family s).pressureCopies slots outgoing.data.h_pos.le).amplitude k
    (ActualSignedPhysicalData.positiveIndex (nativeLabel l))
    (commonLift h (ActualSignedPhysicalBinding.reference l)
      (((family s).pressureCopies slots outgoing.data.h_pos.le).gap (nativeLabel l)) w) = 0
  rw [pressure_gap, ActualSignedPhysicalData.commonLift_zero]
  exact canonical_pressure_amplitude_zero_of_nativeQ s l k hw hq

theorem canonical_potential_periodized_zero_of_nativeQ (l : Label B N0) (i : Fin 3)
    (a r0 : ℝ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).potentialCopies slots outgoing.data.h_pos.le i).periodized a h r0
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l)) w = 0 := by
  simp only [CopyFamily.periodized, canonical_potential_term_zero_of_nativeQ s l i _ a r0 hw hq,
    tsum_zero]

theorem canonical_pressure_periodized_zero_of_nativeQ (l : Label B N0)
    (a r0 : ℝ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).pressureCopies slots outgoing.data.h_pos.le).periodized a h r0
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l)) w = 0 := by
  simp only [CopyFamily.periodized, canonical_pressure_term_zero_of_nativeQ s l _ a r0 hw hq,
    tsum_zero]

end CanonicalFamily

/-! ## The same native slow point in every current band -/

theorem current_nativeSlow_reference (l : Label B N0) (n : ℕ) (k : Frequency)
    (z : SpaceTime) (hr : 0 < z.2 0) :
    (ActualSignedStageControls.nativePoint l n k
      (ActualSignedPotentialCoherence.nativePoint n z)).1 =
      BaseContextAssembly.slowCoordinates
        (ActualSignedPotentialCoherence.nativePoint (ActualSignedPhysicalBinding.reference l) z).1
          := by
  have he := congrArg Prod.fst
    ((ActualSignedPotentialCoherence.nativePoint_absolute n z hr).trans
      (ActualSignedPotentialCoherence.nativePoint_absolute
        (ActualSignedPhysicalBinding.reference l) z hr).symm)
  change toAbsolute n (ActualSignedPotentialCoherence.nativePoint n z).1 =
    toAbsolute (ActualSignedPhysicalBinding.reference l)
      (ActualSignedPotentialCoherence.nativePoint (ActualSignedPhysicalBinding.reference l) z).1 at
        he
  change nativeSlow l.1 (toAbsolute n (ActualSignedPotentialCoherence.nativePoint n z).1) = _
  rw [he]
  exact nativeSlow_toAbsolute l.1 _

theorem nativePoint_slowCoordinates (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0) :
    BaseContextAssembly.slowCoordinates (ActualSignedPotentialCoherence.nativePoint n z).1 =
      ActualSignedPhysicalData.nativeSlow
        (PhysicalMeanJetBounds.graph h n 0 (z.1, CylindricalResidual.chart z.2)) := by
  apply Prod.ext
  · change (ActualSignedPotentialCoherence.nativePoint n z).1.1 =
      (PhysicalMeanJetBounds.graph h n 0 (z.1, CylindricalResidual.chart z.2)).1
    rw [PhysicalMeanJetBounds.graph_radius, ActualSignedPhysicalData.scaledRadial_forward,
      PolarCharts.radius_polar,
      abs_of_pos (mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hr)]
    simp only [ActualSignedPotentialCoherence.nativePoint,
      PhysicalResidualBridge.commonGraph_map (ChartScales.Q_pos n) h _ hr,
      PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply]
  · change ((ActualSignedPotentialCoherence.nativePoint n z).1.2.1.2,
      (ActualSignedPotentialCoherence.nativePoint n z).1.2.1.1) =
      ((PhysicalMeanJetBounds.graph h n 0 (z.1, CylindricalResidual.chart z.2)).2.1.2,
       (PhysicalMeanJetBounds.graph h n 0 (z.1, CylindricalResidual.chart z.2)).2.1.1)
    rw [ActualSignedPhysicalGeometry.nativePoint_slow n 0]

theorem current_nativeSlow_physicalLift (l : Label B N0) (n : ℕ) (k : Frequency)
    (z : SpaceTime) (hr : 0 < z.2 0) :
    (ActualSignedStageControls.nativePoint l n k
      (ActualSignedPotentialCoherence.nativePoint n z)).1 =
      ((ActualSignedPhysicalData.cylinderZero
          (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l)
            (z.1, CylindricalResidual.chart z.2))).1.1,
       (ActualSignedPhysicalData.cylinderZero
          (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l)
            (z.1, CylindricalResidual.chart z.2))).1.2.1) := by
  rw [current_nativeSlow_reference l n k z hr, nativePoint_slowCoordinates _ z hr]
  exact (physicalLift_slow _ _).symm

theorem current_mask_physicalLift (l : Label B N0) (n : ℕ) (k : Frequency)
    (z : SpaceTime) (hr : 0 < z.2 0) :
    ActualSignedStageControls.mask l k n (ActualSignedPotentialCoherence.nativePoint n z) =
      (ActualSignedPhysicalBinding.primary l).mask n
        (ActualSignedPhysicalData.cylinderZero
          (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l)
            (z.1, CylindricalResidual.chart z.2))) := by
  change spatialMask l.1 _ = spatialMask l.1 _
  rw [current_nativeSlow_physicalLift l n k z hr]

theorem current_target_physicalLift (l : Label B N0) (n : ℕ) (k : Frequency)
    (z : SpaceTime) (hr : 0 < z.2 0) :
    ActualSignedStageControls.target l k n (ActualSignedPotentialCoherence.nativePoint n z) =
      ActualSignedStageControls.coefficientScale l n ^ 2 •
        (ActualSignedPhysicalBinding.primary l).target n
          (ActualSignedPhysicalData.cylinderZero
            (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l)
              (z.1, CylindricalResidual.chart z.2))) := by
  unfold ActualSignedStageControls.target
  rw [current_nativeSlow_physicalLift l n k z hr]
  rfl

/-! ## Passing literal raw zeros through the current copy sum -/

theorem common_zero_of_raw (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (x : FullPoint)
    (hz : ∀ k, (ActualSignedCoherence.copies l u).amplitude n k x = 0 ∧
      (ActualSignedCoherence.copies l u).pressure n k x = 0) :
    (ActualSignedCoherence.copies l u).common.amplitude n x = 0 ∧
      (ActualSignedCoherence.copies l u).common.pressure n x = 0 := by
  constructor
  · change (∑' k, (ActualSignedCoherence.copies l u).cutoff n k x •
      (ActualSignedCoherence.copies l u).amplitude n k x) = 0
    simp only [(hz _).1, smul_zero, tsum_zero]
  · change (∑' k, ((ActualSignedCoherence.copies l u).cutoff n k x : ℂ) *
      (ActualSignedCoherence.copies l u).pressure n k x) = 0
    simp only [(hz _).2, mul_zero, tsum_zero]

theorem cylindrical_zero_of_raw (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : SpaceTime)
    (hz : ∀ k, (ActualSignedCoherence.copies l u).amplitude n k
      (ActualSignedPotentialCoherence.nativePoint n z) = 0 ∧
      (ActualSignedCoherence.copies l u).pressure n k
        (ActualSignedPotentialCoherence.nativePoint n z) = 0) :
    ActualSignedPotentialCoherence.cylindricalPotential l u n z = 0 ∧
      ActualSignedPotentialCoherence.cylindricalPressureMode l u n z = 0 := by
  have hc := common_zero_of_raw l u n _ hz
  constructor
  · have hp : ActualSignedPotentialCoherence.potentialCoefficient l u n
        (ActualSignedPotentialCoherence.nativePoint n z) = 0 := by
      simp [ActualSignedPotentialCoherence.potentialCoefficient, hc.1,
        CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross]
    have hv : ActualSignedPotentialCoherence.potential l u n
        (ActualSignedPotentialCoherence.nativePoint n z) = 0 := by
      rw [ActualSignedPotentialCoherence.potential_eq_mode]
      ext i
      simp only [HarmonicCalculus.vectorMode, HarmonicCalculus.mode, hp, Pi.zero_apply, zero_mul]
    rw [ActualSignedPotentialCoherence.cylindricalPotential,
      ActualSignedPotentialCoherence.rescaledPotential, hv, smul_zero]
  · simp [ActualSignedPotentialCoherence.cylindricalPressureMode,
      ActualSignedPotentialCoherence.rescaledPressureMode,
      ActualSignedPotentialCoherence.pressureMode, HarmonicCalculus.mode, hc.2]

theorem current_raw_zero_of_nativeQ (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (k : Frequency) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hq : physicalQ h (z.1, CylindricalResidual.chart z.2) /
      ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2) :
    (ActualSignedCoherence.copies l u).amplitude n k
      (ActualSignedPotentialCoherence.nativePoint n z) = 0 ∧
      (ActualSignedCoherence.copies l u).pressure n k
        (ActualSignedPotentialCoherence.nativePoint n z) = 0 := by
  apply (ActualSignedStageControls.parameters l).raw_zero_of_mask
  change ActualSignedStageControls.mask l k n (ActualSignedPotentialCoherence.nativePoint n z) = 0
  rw [current_mask_physicalLift l n k z hr]
  exact primary_mask_physicalLift_zero l _ _ hw hq

theorem cylindricalPotential_zero_of_nativeQ (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hq : physicalQ h (z.1, CylindricalResidual.chart z.2) /
      ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2) :
    ActualSignedPotentialCoherence.cylindricalPotential l u n z = 0 :=
  (cylindrical_zero_of_raw l u n z (fun k => current_raw_zero_of_nativeQ l u n k z hr hw hq)).1

theorem cylindricalPressureMode_zero_of_nativeQ (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hq : physicalQ h (z.1, CylindricalResidual.chart z.2) /
      ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2) :
    ActualSignedPotentialCoherence.cylindricalPressureMode l u n z = 0 :=
  (cylindrical_zero_of_raw l u n z (fun k => current_raw_zero_of_nativeQ l u n k z hr hw hq)).2

/-! ## The fixed physical exterior -/

theorem current_raw_zero_of_exterior (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (k : Frequency) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hout : (z.1, CylindricalResidual.chart z.2) ∉ active) :
    (ActualSignedCoherence.copies l u).amplitude n k
      (ActualSignedPotentialCoherence.nativePoint n z) = 0 ∧
      (ActualSignedCoherence.copies l u).pressure n k
        (ActualSignedPotentialCoherence.nativePoint n z) = 0 := by
  rcases primary_mask_or_target_zero l n (ActualSignedPhysicalBinding.reference l) hw hout with hm
    | ht
  · apply (ActualSignedStageControls.parameters l).raw_zero_of_mask
    change ActualSignedStageControls.mask l k n (ActualSignedPotentialCoherence.nativePoint n z) = 0
    rw [current_mask_physicalLift l n k z hr, hm]
  · apply ActualWaveRegularityData.raw_zero_of_target
    rw [current_target_physicalLift l n k z hr, ht, smul_zero]

theorem cylindricalPotential_zero_of_exterior (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hout : (z.1, CylindricalResidual.chart z.2) ∉ active) :
    ActualSignedPotentialCoherence.cylindricalPotential l u n z = 0 :=
  (cylindrical_zero_of_raw l u n z (fun k => current_raw_zero_of_exterior l u n k z hr hw hout)).1

theorem cylindricalPressureMode_zero_of_exterior (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hout : (z.1, CylindricalResidual.chart z.2) ∉ active) :
    ActualSignedPotentialCoherence.cylindricalPressureMode l u n z = 0 :=
  (cylindrical_zero_of_raw l u n z (fun k => current_raw_zero_of_exterior l u n k z hr hw hout)).2

end NavierStokes.ActualSignedPhysicalZeros
