/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.PositiveDimensionalComposition
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.MeasurableRepresentative
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.ZeroDimensionalClosure

/-!
# All-dimensional composition of sampled continuous K and Euclidean energies

This module removes the positive-dimension and measurability hypotheses from
the energy comparisons.  Dimension zero is closed exactly, while positive
dimensions use the chosen measurable representative.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A normalized-volume a.e. replacement preserves each weighted triadic
continuous `K` sample. -/
theorem triadicContinuousKSampleTerm_congr_ae {d : ℕ}
    (s : FractionalOrder) {F H : UnitCubeEuclideanL2Field d}
    (hFH : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] H) (j : ℕ) :
    triadicContinuousKSampleTerm s F j = triadicContinuousKSampleTerm s H j := by
  unfold triadicContinuousKSampleTerm
  rw [continuousKFunctional_congr_ae (triadicContinuousKScale j) hFH]

/-- A normalized-volume a.e. replacement preserves the full triadic sampled
continuous `K` energy. -/
theorem triadicContinuousKSampleEnergy_congr_ae {d : ℕ}
    (s : FractionalOrder) {F H : UnitCubeEuclideanL2Field d}
    (hFH : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] H) :
    triadicContinuousKSampleEnergy s F = triadicContinuousKSampleEnergy s H := by
  unfold triadicContinuousKSampleEnergy
  apply tsum_congr
  intro j
  exact triadicContinuousKSampleTerm_congr_ae s hFH j

/-- A normalized-volume a.e. replacement preserves the endpoint-excluded
triadic sampled continuous `K` energy. -/
theorem triadicContinuousKShiftedSampleEnergy_congr_ae {d : ℕ}
    (s : FractionalOrder) {F H : UnitCubeEuclideanL2Field d}
    (hFH : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] H) :
    triadicContinuousKShiftedSampleEnergy s F =
      triadicContinuousKShiftedSampleEnergy s H := by
  unfold triadicContinuousKShiftedSampleEnergy
  apply tsum_congr
  intro j
  exact triadicContinuousKSampleTerm_congr_ae s hFH (j + 1)

namespace UnitCubeEuclideanL2Field

/-- The selected measurable representative preserves the full triadic sampled
continuous `K` energy. -/
theorem triadicContinuousKSampleEnergy_eq_measurableRepresentative {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    triadicContinuousKSampleEnergy s F =
      triadicContinuousKSampleEnergy s F.measurableRepresentative :=
  triadicContinuousKSampleEnergy_congr_ae s F.ae_eq_measurableRepresentative

end UnitCubeEuclideanL2Field

/-- The all-dimensional finite constant for the sampled-energy to
Euclidean-energy direction. -/
noncomputable def allDimensionalSampleToHsConstant
    (s : FractionalOrder) (d : ℕ) : ℝ≥0∞ :=
  positiveDimensionalSampleToHsConstant s d

/-- The all-dimensional finite constant for the Euclidean-energy to
sampled-energy direction. -/
noncomputable def allDimensionalHsToSampleConstant (d : ℕ) : ℝ≥0∞ :=
  positiveDimensionalHsToSampleConstant d

theorem allDimensionalSampleToHsConstant_lt_top
    (s : FractionalOrder) (d : ℕ) :
    allDimensionalSampleToHsConstant s d < ∞ := by
  exact positiveDimensionalSampleToHsConstant_lt_top s d

theorem allDimensionalHsToSampleConstant_lt_top (d : ℕ) :
    allDimensionalHsToSampleConstant d < ∞ := by
  exact positiveDimensionalHsToSampleConstant_lt_top d

/-- In every dimension, the sampled continuous `K` energy controls the exact
Euclidean `H^s` energy. -/
theorem euclideanHsEnergy_le_mul_triadicContinuousKSampleEnergy_all_dim
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    euclideanHsEnergy s F ≤
      allDimensionalHsToSampleConstant d * triadicContinuousKSampleEnergy s F := by
  cases d with
  | zero =>
      rw [euclideanHsEnergy_zero_dim, triadicContinuousKSampleEnergy_zero_dim]
      simp
  | succ d =>
      let : NeZero (Nat.succ d) := ⟨Nat.succ_ne_zero d⟩
      calc
        euclideanHsEnergy s F = euclideanHsEnergy s F.measurableRepresentative :=
          F.euclideanHsEnergy_eq_measurableRepresentative s
        _ ≤ positiveDimensionalHsToSampleConstant (Nat.succ d) *
            triadicContinuousKSampleEnergy s F.measurableRepresentative :=
          euclideanHsEnergy_le_mul_triadicContinuousKSampleEnergy s
            F.measurableRepresentative F.measurable_measurableRepresentative
        _ = allDimensionalHsToSampleConstant (Nat.succ d) *
            triadicContinuousKSampleEnergy s F := by
          rw [← F.triadicContinuousKSampleEnergy_eq_measurableRepresentative s]
          rfl

/-- In every dimension, the exact Euclidean `H^s` energy controls the sampled
continuous `K` energy. -/
theorem triadicContinuousKSampleEnergy_le_mul_euclideanHsEnergy_all_dim
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    triadicContinuousKSampleEnergy s F ≤
      allDimensionalSampleToHsConstant s d * euclideanHsEnergy s F := by
  cases d with
  | zero =>
      rw [triadicContinuousKSampleEnergy_zero_dim, euclideanHsEnergy_zero_dim]
      simp
  | succ d =>
      let : NeZero (Nat.succ d) := ⟨Nat.succ_ne_zero d⟩
      calc
        triadicContinuousKSampleEnergy s F =
            triadicContinuousKSampleEnergy s F.measurableRepresentative :=
          F.triadicContinuousKSampleEnergy_eq_measurableRepresentative s
        _ ≤ positiveDimensionalSampleToHsConstant s (Nat.succ d) *
            euclideanHsEnergy s F.measurableRepresentative :=
          triadicContinuousKSampleEnergy_le_mul_euclideanHsEnergy s
            F.measurableRepresentative F.measurable_measurableRepresentative
        _ = allDimensionalSampleToHsConstant s (Nat.succ d) * euclideanHsEnergy s F := by
          rw [← F.euclideanHsEnergy_eq_measurableRepresentative s]
          rfl

/-- The exact Euclidean and sampled continuous `K` energies are finite under
the same condition in every dimension. -/
theorem euclideanHsEnergy_lt_top_iff_triadicContinuousKSampleEnergy_lt_top
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    euclideanHsEnergy s F < ∞ ↔ triadicContinuousKSampleEnergy s F < ∞ := by
  constructor
  · intro hF
    apply lt_top_iff_ne_top.mpr
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (allDimensionalSampleToHsConstant_lt_top s d).ne hF.ne)
      (triadicContinuousKSampleEnergy_le_mul_euclideanHsEnergy_all_dim s F)
  · intro hF
    apply lt_top_iff_ne_top.mpr
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (allDimensionalHsToSampleConstant_lt_top d).ne hF.ne)
      (euclideanHsEnergy_le_mul_triadicContinuousKSampleEnergy_all_dim s F)

end

end Homogenization
