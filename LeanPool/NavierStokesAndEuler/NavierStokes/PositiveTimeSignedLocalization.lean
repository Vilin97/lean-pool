/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalBinding
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData
public import LeanPool.NavierStokesAndEuler.NavierStokes.InitialPhysicalData

@[expose] public section

/-!
# Localization of the actual signed inputs at positive native time

The fixed primary's mask and target localize its native point. Positive
native time is an explicit premise; no support assertion is made for the
totalized formulas outside that domain.
-/

noncomputable section

namespace NavierStokes.PositiveTimeSignedLocalization

open Set Function
open CorrectionInitialization CorrectionInitialization.ActualPrimary

abbrev Label := ActualSignedPhysicalBinding.Label
abbrev Native := ActualSignedPhysicalData.Native

variable {B N0 : ℕ}

theorem profileRadius_eq (y : Native) :
    PrimaryTargetBounds.profileRadius h (ActualSignedPhysicalData.nativeSlow y) =
      y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) := by
  rw [PrimaryTargetBounds.profileRadius, BaseChartJets.normalizedCoordinates_eq]
  rfl

/-- The actual dyadic mask is supported strictly inside its two endpoints. -/
theorem mask_q_mem (l : Label B N0) (y : Native)
    (hm : (ActualSignedPhysicalBinding.primary l).mask
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0) :
    SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ∈ Ioo (1 / 2 : ℝ) 2 := by
  exact spatialMask_q_range l.1 (ActualSignedPhysicalData.nativeSlow y) hm

/-- Positivity comes from the same chosen prepared carrier, without an
additional nondegeneracy premise on the signed output. -/
theorem mask_radius_pos (l : Label B N0) (y : Native) (hT : 0 < y.2.1.1)
    (hm : (ActualSignedPhysicalBinding.primary l).mask
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0) :
    0 < y.1 := by
  exact (choice B N0).prepared.radius_pos l.1 (ActualSignedPhysicalData.nativeSlow y)
    (spatialMask_carrier l.1 hT hm)

/-- Nonzero actual target forces the normalized radius into the open
nominal active annulus. The endpoint zeros are used exactly. -/
theorem normalized_radius_mem (l : Label B N0) (y : Native) (hT : 0 < y.2.1.1)
    (hm : (ActualSignedPhysicalBinding.primary l).mask
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0)
    (ht : (ActualSignedPhysicalBinding.primary l).target
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0) :
    y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) := by
  by_contra ho
  have hz := ActualWaveRegularityData.target_zero_outside
    (p := ActualSignedPhysicalData.nativeSlow y) hT (mask_radius_pos l y hT hm)
    (by simpa only [profileRadius_eq] using ho)
  apply ht
  change (fun j => PrimaryTargetBounds.actualTarget modulation
    (ActualSignedPhysicalData.nativeSlow y) j) = 0
  simp only [hz, WithLp.ofLp_zero, Pi.zero_apply]
  rfl

/-- The inequalities in the positive-time localization interface. -/
theorem normalized_bounds (l : Label B N0) (y : Native) (hT : 0 < y.2.1.1)
    (hm : (ActualSignedPhysicalBinding.primary l).mask
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0)
    (ht : (ActualSignedPhysicalBinding.primary l).target
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0) :
    1 / 2 ≤ SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ∧
      SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ≤ 2 ∧
      PrimaryTargetBounds.leftRadius nominal ≤
        y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ∧
      y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ≤
        PrimaryTargetBounds.rightRadius nominal :=
  ⟨(mask_q_mem l y hm).1.le, (mask_q_mem l y hm).2.le,
    (normalized_radius_mem l y hT hm ht).1.le, (normalized_radius_mem l y hT hm ht).2.le⟩

/-- Membership is in the actual moving strip, with the same fixed primary
annulus and slow region used by the native signed estimates. -/
theorem native_mem_strip (l : Label B N0) (y : Native) (hT : 0 < y.2.1.1)
    (hm : (ActualSignedPhysicalBinding.primary l).mask
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0)
    (ht : (ActualSignedPhysicalBinding.primary l).target
      (ActualSignedPhysicalBinding.reference l) (ActualSignedPhysicalData.nativeCylinder y) ≠ 0) :
    y ∈ ActualPrimaryBounds.strip.domain := by
  apply (BaseContextAssembly.nativeStrip_mem nominal ActualPrimaryBounds.region y).mpr
  refine ⟨⟨hT, mask_q_mem l y hm⟩, ?_⟩
  change PrimaryTargetBounds.profileRadius h (ActualSignedPhysicalData.nativeSlow y) ∈ _
  rw [profileRadius_eq]
  exact normalized_radius_mem l y hT hm ht

/-- The same selected mask pulls back to the literal physical label mask
at every preterminal Cartesian point. -/
theorem mask_pullback (l : Label B N0) (w : ProblemStatement.SpaceTime)
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    (ActualSignedPhysicalBinding.primary l).mask (ActualSignedPhysicalBinding.reference l)
        (ActualSignedPhysicalData.cylinderZero
          (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l) w)) =
      PhysicalWaveSum.physicalMask (CoordinateAlgebra.D h)
        (ActualSignedPhysicalBinding.spatialLabel l) (PhysicalWaveSum.physicalParams h w) := by
  have hm := InitialPhysicalData.spatialMask_physical (l.2, l.1) 0 hw
  rw [ActualSignedPhysicalData.commonLift_zero] at hm
  exact hm

end NavierStokes.PositiveTimeSignedLocalization
