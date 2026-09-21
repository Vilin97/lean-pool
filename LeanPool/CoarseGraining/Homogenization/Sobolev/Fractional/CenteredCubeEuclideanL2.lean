/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Dilation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.UnitCubeEuclideanL2

/-!
# Euclidean `L²` fields on centered triadic cubes

This module transports the exact Euclidean `L²` carrier between the centered
triadic cube at scale `m` and the centered unit cube.  The transport uses the
literal dilation `x ↦ (3 ^ m) • x`; normalized volume is therefore preserved
exactly.

## Main definitions

- `centeredCubeDomain`: the bounded measurable realization of `originCube d m`.
- `CenteredCubeEuclideanL2Field`: Euclidean `L²` vector fields on that domain.
- `CenteredCubeEuclideanL2Field.pullbackToUnit`: pullback by the cube dilation.

## Main results

- `centeredCubeDilationMeasurePreserving`: normalized-volume preservation.
- `normalizedEuclideanLpENorm_pullbackToUnit`: exact normalized norm invariance.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-- The bounded measurable realization of the centered triadic cube at scale `m`. -/
noncomputable def centeredCubeDomain (d : ℕ) (m : ℤ) : BoundedMeasurableDomain d :=
  cubeBoundedMeasurableDomain (originCube d m)

/-- The positive dilation factor carrying the centered unit cube to scale `m`. -/
noncomputable def centeredCubeScale (m : ℤ) : ℝ :=
  (3 : ℝ) ^ m

@[simp] theorem centeredCubeScale_zero : centeredCubeScale 0 = 1 := by
  simp [centeredCubeScale]

theorem centeredCubeScale_pos (m : ℤ) : 0 < centeredCubeScale m := by
  exact zpow_pos (by norm_num) m

theorem centeredCubeScale_ne_zero (m : ℤ) : centeredCubeScale m ≠ 0 :=
  (centeredCubeScale_pos m).ne'

/-- Dilation from the centered unit cube to the centered cube at scale `m`. -/
noncomputable def centeredCubeDilation {d : ℕ} (m : ℤ) : Vec d → Vec d :=
  fun x => centeredCubeScale m • x

theorem measurable_centeredCubeDilation {d : ℕ} (m : ℤ) :
    Measurable (centeredCubeDilation (d := d) m) :=
  measurable_const_smul (centeredCubeScale m)

/-- Restricted volume gains the inverse Jacobian under centered-cube dilation. -/
theorem map_centeredCubeDilation_restrictedVolume {d : ℕ} (m : ℤ) :
    Measure.map (centeredCubeDilation (d := d) m)
        (centeredCubeDomain d 0).restrictedVolume =
      ENNReal.ofReal (((centeredCubeScale m) ^ d)⁻¹) •
        (centeredCubeDomain d m).restrictedVolume := by
  unfold centeredCubeDomain
  rw [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet,
    cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet]
  rw [show centeredCubeDilation (d := d) m =
      fun x : Vec d => centeredCubeScale m • x by rfl]
  rw [map_smul_volume_restrict (centeredCubeScale_pos m)]
  have hset :
      centeredCubeScale m • openCubeSet (originCube d 0) =
        openCubeSet (originCube d m) := by
    simpa only [centeredCubeScale, cubeScaleFactor_originCube] using
      (openCubeSet_originCube_eq_smul_originCube_zero (d := d) m).symm
  rw [hset]

/-- Normalized volume is exactly preserved by centered-cube dilation. -/
theorem map_centeredCubeDilation_normalizedVolume {d : ℕ} (m : ℤ) :
    Measure.map (centeredCubeDilation (d := d) m)
        (centeredCubeDomain d 0).normalizedVolume =
      (centeredCubeDomain d m).normalizedVolume := by
  unfold centeredCubeDomain
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  unfold normalizedCubeMeasure
  rw [Measure.map_smul]
  have hmap :
      Measure.map (centeredCubeDilation (d := d) m) (cubeMeasure (originCube d 0)) =
        ENNReal.ofReal (((centeredCubeScale m) ^ d)⁻¹) •
          cubeMeasure (originCube d m) := by
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure] using
      map_centeredCubeDilation_restrictedVolume (d := d) m
  rw [hmap]
  simp only [cubeVolume, cubeScaleFactor_originCube, centeredCubeScale,
    zpow_zero, one_pow, inv_one, ENNReal.ofReal_one, one_smul]

/-- Centered-cube dilation as a normalized-volume-preserving map. -/
theorem centeredCubeDilationMeasurePreserving {d : ℕ} (m : ℤ) :
    MeasurePreserving (centeredCubeDilation (d := d) m)
      (centeredCubeDomain d 0).normalizedVolume
      (centeredCubeDomain d m).normalizedVolume :=
  ⟨measurable_centeredCubeDilation m, map_centeredCubeDilation_normalizedVolume m⟩

/-- A Euclidean `L²` vector field on the centered cube at scale `m`. -/
structure CenteredCubeEuclideanL2Field (d : ℕ) (m : ℤ) where
  /-- The represented vector field. -/
  toField : Vec d → Vec d
  euclideanMemL2 :
    MemLp (fun x => HilbertVec.ofVec (toField x)) (2 : ℝ≥0∞)
      (centeredCubeDomain d m).normalizedVolume

namespace CenteredCubeEuclideanL2Field

instance {d : ℕ} {m : ℤ} :
    CoeFun (CenteredCubeEuclideanL2Field d m) (fun _ => Vec d → Vec d) where
  coe F := F.toField

/-- The explicit Euclidean-magnitude form of the stored `L²` fact. -/
theorem euclideanMagnitudeMemL2 {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) :
    MemLp (fun x => euclideanNorm (F x)) (2 : ℝ≥0∞)
      (centeredCubeDomain d m).normalizedVolume := by
  simpa only [euclideanNorm_eq_norm_ofVec] using F.euclideanMemL2.norm

/-- Pull a physical centered-cube field back to the centered unit cube. -/
noncomputable def pullbackToUnit {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) : UnitCubeEuclideanL2Field d where
  toField := fun x => F (centeredCubeDilation m x)
  euclideanMemL2 := by
    change MemLp
      ((fun x => HilbertVec.ofVec (F x)) ∘ centeredCubeDilation (d := d) m)
      (2 : ℝ≥0∞) (unitCenteredCubeDomain d).normalizedVolume
    rw [show unitCenteredCubeDomain d = centeredCubeDomain d 0 by rfl]
    exact F.euclideanMemL2.comp_measurePreserving
      (centeredCubeDilationMeasurePreserving m)

@[simp] theorem pullbackToUnit_apply {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) (x : Vec d) :
    F.pullbackToUnit x = F (centeredCubeScale m • x) :=
  rfl

/-- A globally measurable representative selected from the stored Euclidean
`L²` witness on the centered cube. -/
noncomputable def measurableRepresentative {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) : CenteredCubeEuclideanL2Field d m :=
  let f : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (F x)
  let hf : AEStronglyMeasurable f (centeredCubeDomain d m).normalizedVolume :=
    F.euclideanMemL2.aestronglyMeasurable
  { toField := fun x => HilbertVec.toVec (AEStronglyMeasurable.mk f hf x)
    euclideanMemL2 := by
      simpa only [HilbertVec.ofVec_toVec] using F.euclideanMemL2.ae_eq hf.ae_eq_mk }

/-- The selected centered-cube representative is globally measurable. -/
theorem measurable_measurableRepresentative {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) : Measurable F.measurableRepresentative := by
  unfold measurableRepresentative
  dsimp only
  exact (HilbertVec.continuousLinearEquivVec d).continuous.measurable.comp
    (F.euclideanMemL2.aestronglyMeasurable.measurable_mk)

/-- The selected representative agrees with the original field almost
everywhere for normalized centered-cube volume. -/
theorem ae_eq_measurableRepresentative {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) :
    F =ᵐ[(centeredCubeDomain d m).normalizedVolume] F.measurableRepresentative := by
  unfold measurableRepresentative
  dsimp only
  filter_upwards [F.euclideanMemL2.aestronglyMeasurable.ae_eq_mk] with x hx
  simpa only [HilbertVec.toVec_ofVec] using congrArg HilbertVec.toVec hx

/-- Pullback preserves the exact normalized Euclidean extended `L²` norm. -/
theorem normalizedEuclideanLpENorm_pullbackToUnit {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        F.pullbackToUnit =
      (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F := by
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
  change eLpNorm
      ((fun x => euclideanNorm (F x)) ∘ centeredCubeDilation (d := d) m)
        (2 : ℝ≥0∞) (unitCenteredCubeDomain d).normalizedVolume = _
  rw [show unitCenteredCubeDomain d = centeredCubeDomain d 0 by rfl]
  exact eLpNorm_comp_measurePreserving F.euclideanMagnitudeMemL2.aestronglyMeasurable
    (centeredCubeDilationMeasurePreserving m)

/-- Pullback preserves the proof-carrying normalized Euclidean real `L²` norm. -/
theorem normalizedEuclideanLpNorm_pullbackToUnit {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpNorm (2 : ℝ≥0∞)
        F.pullbackToUnit F.pullbackToUnit.euclideanMagnitudeMemL2 =
      (centeredCubeDomain d m).normalizedEuclideanLpNorm (2 : ℝ≥0∞)
        F F.euclideanMagnitudeMemL2 := by
  unfold BoundedMeasurableDomain.normalizedEuclideanLpNorm
  exact congrArg ENNReal.toReal (normalizedEuclideanLpENorm_pullbackToUnit F)

end CenteredCubeEuclideanL2Field

end

end Homogenization
