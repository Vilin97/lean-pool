/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.FiveTermSplit

/-! # Cutoff Oscillation -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# CutoffOscillation

Cutoff oscillation bounds.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/--
Second manuscript term: the cutoff oscillation is bounded by its childwise
oscillation size times the parent response.
-/
theorem abs_cutoffOscillationTermOnCubeAtDepth_le_osc_mul_responseJOnCube
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (j : ℕ) (φ : Vec d → ℝ) (p q : Vec d) {osc : ℝ}
    (hOsc_int :
      ∀ R ∈ descendantsAtDepth Q j,
        IntegrableOn
          (fun x =>
            (cubeAverage R φ - φ x) * topHalfEnergyDensityOnCube Q a p q x)
          (cubeSet R) volume)
    (hOscPoint :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
          |cubeAverage R φ - φ x| ≤ osc) :
    |cutoffOscillationTermOnCubeAtDepth Q a j φ p q| ≤
      osc * Ch02.responseJ (Ch02.cubeDomain Q) a p q := by
  classical
  let S : Finset (TriadicCube d) := descendantsAtDepth Q j
  let F : Vec d → ℝ := topHalfEnergyDensityOnCube Q a p q
  have hS_nonempty : S.Nonempty := by
    simpa [S] using descendantsAtDepth_nonempty Q j
  have hcard_pos_nat : 0 < S.card := Finset.card_pos.mpr hS_nonempty
  have hcard_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hcard_pos_nat
  have hinv_nonneg : 0 ≤ ((S.card : ℝ)⁻¹) := inv_nonneg.mpr hcard_pos.le
  have hTop_int : IntegrableOn F (cubeSet Q) volume := by
    simpa [F] using topHalfEnergyDensityOnCube_integrableOn_cubeSet Q a p q
  have hTerm :
      ∀ R ∈ S,
        |cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x)| ≤
          osc * cubeAverage R F := by
    intro R hR
    have hR' : R ∈ descendantsAtDepth Q j := by simpa [S] using hR
    have hsubset : cubeSet R ⊆ cubeSet Q :=
      cubeSet_subset_of_mem_descendantsAtDepth hR'
    have hle :
        volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
      simpa [volumeMeasureOn] using
        MeasureTheory.Measure.restrict_mono_set volume hsubset
    have hF_int_R : IntegrableOn F (cubeSet R) volume :=
      hTop_int.mono_set hsubset
    have hF_nonneg_R : 0 ≤ᵐ[volumeMeasureOn (cubeSet R)] F :=
      (topHalfEnergyDensityOnCube_ae_nonneg_cubeSet Q a p q).filter_mono
        (MeasureTheory.ae_mono hle)
    have hwf_int :
        IntegrableOn (fun x => (cubeAverage R φ - φ x) * F x)
          (cubeSet R) volume := by
      simpa [F] using hOsc_int R hR'
    exact
      abs_cubeAverage_mul_nonneg_le_mul_cubeAverage_of_ae_abs_le
        R hF_int_R hwf_int hF_nonneg_R (hOscPoint R hR')
  have hAbsSum :
      |∑ R ∈ S,
          cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x)| ≤
        ∑ R ∈ S, |cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x)| :=
    Finset.abs_sum_le_sum_abs
      (s := S)
      (f := fun R =>
        cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x))
  have hSumBound :
      ∑ R ∈ S, |cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x)| ≤
        ∑ R ∈ S, osc * cubeAverage R F :=
    Finset.sum_le_sum fun R hR => hTerm R hR
  have hDesc :
      descendantsAverage Q j (fun R => cubeAverage R F) = cubeAverage Q F := by
    rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      (Q := Q) (j := j) (f := F) hTop_int]
  calc
    |cutoffOscillationTermOnCubeAtDepth Q a j φ p q|
        =
          |(S.card : ℝ)⁻¹ *
            (∑ R ∈ S,
              cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x))| := by
          simp [cutoffOscillationTermOnCubeAtDepth, descendantsAverage, S, F]
    _ =
        (S.card : ℝ)⁻¹ *
          |∑ R ∈ S,
            cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x)| := by
          rw [abs_mul, abs_of_nonneg hinv_nonneg]
    _ ≤
        (S.card : ℝ)⁻¹ *
          (∑ R ∈ S,
            |cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x)|) := by
          exact mul_le_mul_of_nonneg_left hAbsSum hinv_nonneg
    _ ≤ (S.card : ℝ)⁻¹ * (∑ R ∈ S, osc * cubeAverage R F) := by
          exact mul_le_mul_of_nonneg_left hSumBound hinv_nonneg
    _ = osc * descendantsAverage Q j (fun R => cubeAverage R F) := by
          simp only [descendantsAverage, S]
          rw [← Finset.mul_sum]
          ring
    _ = osc * cubeAverage Q F := by rw [hDesc]
    _ = osc * Ch02.responseJ (Ch02.cubeDomain Q) a p q := by
          rw [← responseJOnCube_eq_cubeAverage_topHalfEnergy Q a p q]

/-- Cutoff-oscillation bound with the product integrability discharged from a
bounded cutoff. -/
theorem abs_cutoffOscillationTermOnCubeAtDepth_le_scale_mul_responseJOnCube_of_ae_bounded_cutoff
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (j : ℕ) {φ : Vec d → ℝ} {B C scaleSep : ℝ} (p q : Vec d)
    (hφ_meas : AEStronglyMeasurable φ (volumeMeasureOn (cubeSet Q)))
    (hφ_bound : ∀ᵐ x ∂ volumeMeasureOn (cubeSet Q), ‖φ x‖ ≤ B)
    (hOscPoint :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
          |cubeAverage R φ - φ x| ≤ C * scaleSep) :
    |cutoffOscillationTermOnCubeAtDepth Q a j φ p q| ≤
      C * scaleSep * Ch02.responseJ (Ch02.cubeDomain Q) a p q := by
  have hbase :=
    abs_cutoffOscillationTermOnCubeAtDepth_le_osc_mul_responseJOnCube
      (Q := Q) (a := a) (j := j) (φ := φ) (p := p) (q := q)
      (osc := C * scaleSep)
      (cutoffOscillationTermOnCubeAtDepth_integrableOn_descendants_of_ae_bounded
        Q a j p q hφ_meas hφ_bound)
      hOscPoint
  simpa [mul_assoc] using hbase

/-- Law-facing form of the cutoff-oscillation bound for the Ch4 dependent
triadic coefficient family. -/
theorem abs_cutoffOscillationTermOnDependentFamilyAtDepth_le_scale_mul_restrictionResponseJObservableCubeSet_of_ae_bounded_cutoff
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) {φ : Vec d → ℝ} {B C scaleSep : ℝ}
    (p q : Vec d)
    (hφ_meas : AEStronglyMeasurable φ (volumeMeasureOn (cubeSet Q)))
    (hφ_bound : ∀ᵐ x ∂ volumeMeasureOn (cubeSet Q), ‖φ x‖ ≤ B)
    (hOscPoint :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
          |cubeAverage R φ - φ x| ≤ C * scaleSep) :
    |cutoffOscillationTermOnCubeAtDepth Q
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
        j φ p q| ≤
      C * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a := by
  have hraw :=
    abs_cutoffOscillationTermOnCubeAtDepth_le_scale_mul_responseJOnCube_of_ae_bounded_cutoff
      (Q := Q)
      (a := (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
      (j := j) (φ := φ) (B := B) (C := C) (scaleSep := scaleSep)
      p q hφ_meas hφ_bound hOscPoint
  simpa [responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet a ha Q p q]
    using hraw

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
