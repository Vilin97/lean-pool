/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.BesovLeGagliardo
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.GagliardoLeBesov
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.EuclideanGagliardoCoordinateBridge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.OverlapCoordinateBridge

/-!
# Extended overlap-Besov and coordinate Gagliardo energies

This module compares the corrected vector overlap-Besov truncations on the centered unit cube
with the finite family of scalar coordinate Gagliardo energies. The overlap energy is defined in
`ℝ≥0∞` as the supremum of the finite squared truncations; in particular, it never passes through
the legacy real-valued `sSup` seminorm.

The positive-dimensional comparison lemmas below are proof-internal producers. Their explicit
measurability, `MemLp`, and `[NeZero d]` hypotheses are intended to be discharged later by the
measurable-representative and zero-dimensional wrappers, rather than exposed in the final
source-facing theorem.
-/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

/-- The extended corrected-vector overlap-Besov energy on the centered unit cube. -/
noncomputable def extendedVectorOverlapBesovEnergy {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  ⨆ N : ℕ, ENNReal.ofReal
    ((cubeBesovOverlappingPositiveVectorPartialSeminormTwo
      (originCube d 0) s.1 N F) ^ 2)

/-- The explicit dimension factor in the overlap-to-Gagliardo estimate is finite. -/
theorem overlapBesovEnergy_gagliardoConstant_lt_top (d : ℕ) :
    ((d : ℝ≥0∞) * (2 * 3 ^ d)) < ∞ := by
  exact lt_top_iff_ne_top.2 (by finiteness)

/-- The explicit dimension factor in the Gagliardo-to-overlap estimate is finite. -/
theorem coordinateGagliardoEnergy_overlapBesovConstant_lt_top (d : ℕ) :
    ((d : ℝ≥0∞) *
      (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ)) < ∞ := by
  exact lt_top_iff_ne_top.2 (by
    apply ENNReal.mul_ne_top
    · finiteness
    · apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      rw [Gagliardo.gagliardoBesovLowerConstant]
      exact ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (by norm_num)) (ENNReal.pow_ne_top (by norm_num)))

/-- The root-scale correction is exactly one on the centered unit cube. -/
@[simp] theorem cubeBesovScaleWeight_originCube_zero {d : ℕ} (s : ℝ) :
    cubeBesovScaleWeight s (originCube d 0) = 1 := by
  simp [cubeBesovScaleWeight]

/-- Every squared finite truncation is bounded by the extended overlap-Besov energy. -/
theorem ofReal_sq_vectorPartialSeminorm_le_extendedVectorOverlapBesovEnergy {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (N : ℕ) :
    ENNReal.ofReal
        ((cubeBesovOverlappingPositiveVectorPartialSeminormTwo
          (originCube d 0) s.1 N F) ^ 2) ≤
      extendedVectorOverlapBesovEnergy s F := by
  exact le_iSup (fun M : ℕ => ENNReal.ofReal
    ((cubeBesovOverlappingPositiveVectorPartialSeminormTwo
      (originCube d 0) s.1 M F) ^ 2)) N

/-- The extended corrected-vector overlap energy vanishes in dimension zero. -/
theorem extendedVectorOverlapBesovEnergy_zero_dim
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field 0) :
    extendedVectorOverlapBesovEnergy s F = 0 := by
  have hFzero : (F : Vec 0 → Vec 0) = 0 := by
    funext x
    exact Subsingleton.elim (F x) 0
  apply le_antisymm
  · refine iSup_le fun N => ?_
    rw [hFzero]
    simp [cubeBesovOverlappingPositiveVectorPartialSeminormTwo,
      cubeBesovOverlappingPositiveVectorDepthSeminorm,
      cubeBesovOverlappingPositiveVectorDepthAverage, overlapCentersAverage,
      overlapCubeLpNorm]
  · exact bot_le

private theorem iSup_scalarPartialSeminorm_le_extendedVectorOverlapBesovEnergy {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (i : Fin d)
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0))) :
    (⨆ N : ℕ, ENNReal.ofReal
        ((cubeBesovOverlapPartialSeminorm (originCube d 0) s.1
          (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => F x i)) ^ 2)) ≤
      extendedVectorOverlapBesovEnergy s F := by
  refine iSup_le fun N => ?_
  have hpartial :
      cubeBesovOverlapPartialSeminorm (originCube d 0) s.1
          (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => F x i) ≤
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo
          (originCube d 0) s.1 N F := by
    simpa only [cubeBesovScaleWeight_originCube_zero, one_mul] using
      cubeBesovOverlapPartialSeminorm_two_coordinate_le_vector
        (originCube d 0) s.1 F i N hF
  have hsquare :
      (cubeBesovOverlapPartialSeminorm (originCube d 0) s.1
          (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => F x i)) ^ 2 ≤
        (cubeBesovOverlappingPositiveVectorPartialSeminormTwo
          (originCube d 0) s.1 N F) ^ 2 :=
    (sq_le_sq₀
      (cubeBesovOverlapPartialSeminorm_nonneg (originCube d 0) s.1
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => F x i))
      (cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg
        (originCube d 0) s.1 N F)).2 hpartial
  exact (ENNReal.ofReal_le_ofReal hsquare).trans
    (ofReal_sq_vectorPartialSeminorm_le_extendedVectorOverlapBesovEnergy s F N)

/-- Proof-internal positive-dimensional producer: the coordinate Gagliardo energy is bounded
by the extended corrected-vector overlap energy. -/
theorem coordinateGagliardoEnergy_le_mul_extendedVectorOverlapBesovEnergy {d : ℕ}
    [NeZero d] (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (hFmeas : Measurable F)
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0))) :
    coordinateGagliardoEnergy s F ≤
      ((d : ℝ≥0∞) * (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ)) *
        extendedVectorOverlapBesovEnergy s F := by
  rw [coordinateGagliardoEnergy]
  calc
    (∑ i : Fin d,
        (Gagliardo.cubeGagliardoESeminorm (originCube d 0) s.1
          (2 : ℝ≥0∞) (fun x => F x i)) ^ (2 : ℝ)) ≤
      ∑ _i : Fin d,
        (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
          extendedVectorOverlapBesovEnergy s F := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hscalar :
          (Gagliardo.cubeGagliardoESeminorm (originCube d 0) s.1
            (2 : ℝ≥0∞) (fun x => F x i)) ^ (2 : ℝ) ≤
            (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
              ⨆ N : ℕ, ENNReal.ofReal
                ((cubeBesovOverlapPartialSeminorm (originCube d 0) s.1
                  (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => F x i)) ^ 2) := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using!
          Gagliardo.gagliardo_rpow_le_iSup_partialSeminorm
            (originCube d 0) s.2.1.le s.2.2.le (p := (2 : ℝ≥0∞))
            (by norm_num) (by norm_num)
            ((measurable_pi_apply i).comp hFmeas) (hF.eval i)
      exact hscalar.trans (mul_le_mul_right
        (iSup_scalarPartialSeminorm_le_extendedVectorOverlapBesovEnergy s F i hF)
        ((Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ)))
    _ = ((d : ℝ≥0∞) * (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ)) *
          extendedVectorOverlapBesovEnergy s F := by
      simp [mul_assoc]

private theorem ofReal_sq_vectorPartialSeminorm_le_mul_coordinateGagliardoEnergy {d : ℕ}
    [NeZero d] (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (N : ℕ)
    (hFmeas : Measurable F)
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0))) :
    ENNReal.ofReal
        ((cubeBesovOverlappingPositiveVectorPartialSeminormTwo
          (originCube d 0) s.1 N F) ^ 2) ≤
      ((d : ℝ≥0∞) * (2 * 3 ^ d)) * coordinateGagliardoEnergy s F := by
  let P : Fin d → ℝ := fun i =>
    cubeBesovOverlapPartialSeminorm (originCube d 0) s.1
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => F x i)
  have hP_nonneg : ∀ i : Fin d, 0 ≤ P i := fun i =>
    cubeBesovOverlapPartialSeminorm_nonneg (originCube d 0) s.1
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => F x i)
  have hvector_le :
      cubeBesovOverlappingPositiveVectorPartialSeminormTwo
          (originCube d 0) s.1 N F ≤
        ∑ i : Fin d, P i := by
    simpa only [cubeBesovScaleWeight_originCube_zero, one_mul] using
      scaleWeight_mul_vectorPartialSeminorm_le_sum_coordinates
        (originCube d 0) s.1 F N hF
  have hsquare_le :
      (cubeBesovOverlappingPositiveVectorPartialSeminormTwo
          (originCube d 0) s.1 N F) ^ 2 ≤
        (d : ℝ) * ∑ i : Fin d, (P i) ^ 2 := by
    calc
      (cubeBesovOverlappingPositiveVectorPartialSeminormTwo
          (originCube d 0) s.1 N F) ^ 2 ≤
          (∑ i : Fin d, P i) ^ 2 :=
        (sq_le_sq₀
          (cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg
            (originCube d 0) s.1 N F)
          (Finset.sum_nonneg fun i _hi => hP_nonneg i)).2 hvector_le
      _ ≤ (d : ℝ) * ∑ i : Fin d, (P i) ^ 2 := by
        simpa using
          (sq_sum_le_card_mul_sum_sq
            (s := (Finset.univ : Finset (Fin d))) (f := P))
  have hscalar : ∀ i : Fin d,
      ENNReal.ofReal ((P i) ^ 2) ≤
        2 * 3 ^ d *
          (Gagliardo.cubeGagliardoESeminorm (originCube d 0) s.1
            (2 : ℝ≥0∞) (fun x => F x i)) ^ (2 : ℝ) := by
    intro i
    simpa only [P, ENNReal.toReal_ofNat, Real.rpow_two] using!
      Gagliardo.ofReal_partialSeminorm_rpow_le_gagliardo
        (originCube d 0) s.2.1.le (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num)
        ((measurable_pi_apply i).comp hFmeas) (hF.eval i) N
  calc
    ENNReal.ofReal
        ((cubeBesovOverlappingPositiveVectorPartialSeminormTwo
          (originCube d 0) s.1 N F) ^ 2) ≤
      ENNReal.ofReal ((d : ℝ) * ∑ i : Fin d, (P i) ^ 2) :=
        ENNReal.ofReal_le_ofReal hsquare_le
    _ = (d : ℝ≥0∞) * ∑ i : Fin d, ENNReal.ofReal ((P i) ^ 2) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg d),
        ENNReal.ofReal_sum_of_nonneg (fun i _hi => sq_nonneg (P i))]
      simp
    _ ≤ (d : ℝ≥0∞) * ∑ i : Fin d,
        2 * 3 ^ d *
          (Gagliardo.cubeGagliardoESeminorm (originCube d 0) s.1
            (2 : ℝ≥0∞) (fun x => F x i)) ^ (2 : ℝ) := by
      exact mul_le_mul_right (Finset.sum_le_sum fun i _hi => hscalar i) _
    _ = ((d : ℝ≥0∞) * (2 * 3 ^ d)) * coordinateGagliardoEnergy s F := by
      rw [coordinateGagliardoEnergy, ← Finset.mul_sum]
      ac_rfl

/-- Proof-internal positive-dimensional producer: the extended corrected-vector overlap energy
is bounded by the coordinate Gagliardo energy. -/
theorem extendedVectorOverlapBesovEnergy_le_mul_coordinateGagliardoEnergy {d : ℕ}
    [NeZero d] (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (hFmeas : Measurable F)
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0))) :
    extendedVectorOverlapBesovEnergy s F ≤
      ((d : ℝ≥0∞) * (2 * 3 ^ d)) * coordinateGagliardoEnergy s F := by
  refine iSup_le fun N => ?_
  exact ofReal_sq_vectorPartialSeminorm_le_mul_coordinateGagliardoEnergy
    s F N hFmeas hF

end

end Homogenization
