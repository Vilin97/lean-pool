/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousKFunctional
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanH2
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

/-!
# Measurable representatives of unit-cube Euclidean `L²` fields

The public `UnitCubeEuclideanL2Field` carrier stores an a.e. `L²` witness,
not a chosen measurable representative.  This module obtains one internally
from that witness without changing the carrier.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace UnitCubeEuclideanL2Field

/-- The globally measurable vector representative selected from the stored
Hilbert-valued Euclidean `L²` witness. -/
noncomputable def measurableRepresentative {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) : UnitCubeEuclideanL2Field d :=
  let f : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (F x)
  let hf : AEStronglyMeasurable f (unitCenteredCubeDomain d).normalizedVolume :=
    F.euclideanMemL2.aestronglyMeasurable
  { toField := fun x => HilbertVec.toVec (AEStronglyMeasurable.mk f hf x)
    euclideanMemL2 := by
      simpa only [HilbertVec.ofVec_toVec] using F.euclideanMemL2.ae_eq hf.ae_eq_mk }

/-- The selected representative is globally measurable as a `Vec d` field. -/
theorem measurable_measurableRepresentative {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) : Measurable F.measurableRepresentative := by
  unfold measurableRepresentative
  dsimp only
  exact (HilbertVec.continuousLinearEquivVec d).continuous.measurable.comp
    (F.euclideanMemL2.aestronglyMeasurable.measurable_mk)

/-- The chosen representative agrees with the original field almost
everywhere for normalized unit-cube volume. -/
theorem ae_eq_measurableRepresentative {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) :
    F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] F.measurableRepresentative := by
  unfold measurableRepresentative
  dsimp only
  filter_upwards [F.euclideanMemL2.aestronglyMeasurable.ae_eq_mk] with x hx
  simpa only [HilbertVec.toVec_ofVec] using congrArg HilbertVec.toVec hx

/-- The representative retains the stored Euclidean `L²` witness. -/
theorem measurableRepresentative_euclideanMemL2 {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) :
    MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F.measurableRepresentative x))
      (2 : ℝ≥0∞) (unitCenteredCubeDomain d).normalizedVolume :=
  F.measurableRepresentative.euclideanMemL2

/-- Every scalar coordinate of the selected representative is globally
measurable. -/
theorem measurable_measurableRepresentative_coordinate {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) (i : Fin d) :
    Measurable (fun x => F.measurableRepresentative x i) :=
  (continuous_apply i).measurable.comp F.measurable_measurableRepresentative

/-- The selected representative is an ambient-vector `L²` field for the
canonical origin-cube normalization. -/
theorem memLp_measurableRepresentative {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) :
    MemLp F.measurableRepresentative (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d 0)) := by
  rw [← unitCenteredCubeDomain_normalizedVolume_eq_normalizedCubeMeasure]
  refine F.measurableRepresentative.euclideanMemL2.mono
    F.measurable_measurableRepresentative.aestronglyMeasurable ?_
  filter_upwards with x
  exact HilbertVec.norm_le_norm_ofVec _

/-- Every scalar coordinate of the selected representative is in `L²` for
the canonical origin-cube normalization. -/
theorem memLp_measurableRepresentative_coordinate {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) (i : Fin d) :
    MemLp (fun x => F.measurableRepresentative x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d 0)) := by
  rw [← unitCenteredCubeDomain_normalizedVolume_eq_normalizedCubeMeasure]
  have hmem := F.measurableRepresentative.euclideanMemL2
  rw [memLp_piLp_iff] at hmem
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
    hmem i

/-- Replacing a field by its chosen measurable representative preserves the
continuous interpolation seminorm. -/
theorem continuousKSeminorm_eq_measurableRepresentative {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    continuousKSeminorm s F = continuousKSeminorm s F.measurableRepresentative :=
  continuousKSeminorm_congr_ae s F.ae_eq_measurableRepresentative

/-- Replacing a field by its chosen measurable representative preserves the
exact Euclidean fractional energy. -/
theorem euclideanHsEnergy_eq_measurableRepresentative {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    euclideanHsEnergy s F = euclideanHsEnergy s F.measurableRepresentative :=
  euclideanHsEnergy_congr_ae F.ae_eq_measurableRepresentative

/-- Replacing a field by its chosen measurable representative preserves the
exact Euclidean fractional seminorm. -/
theorem euclideanHsESeminorm_eq_measurableRepresentative {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    euclideanHsESeminorm s F = euclideanHsESeminorm s F.measurableRepresentative :=
  euclideanHsESeminorm_congr_ae F.ae_eq_measurableRepresentative

end UnitCubeEuclideanL2Field

end

end Homogenization
