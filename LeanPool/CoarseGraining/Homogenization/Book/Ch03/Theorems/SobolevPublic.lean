/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.FractionalSobolevVsBesov
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.EndPoints
import LeanPool.CoarseGraining.Homogenization.Besov.PositiveOverlapBridge
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.PositiveSeminorms.Definitions
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge.CoordinateStandard

/-!
# Legacy Sobolev/dual-Besov compatibility wrappers for the Chapter 3 comparison

This file supplies the compatibility layer used by `Book.MainResults`: positive
data use the componentwise legacy fractional-Sobolev form from `Ch01.Legacy`,
while the negative left-hand side is a legacy dual-Besov wrapper. The bridge
lemmas convert these compatibility quantities to the Besov quantities consumed
by the already-proved deterministic comparison theorem. The positive lane is
the legacy ambient-sup-distance, finite-truncation / real-`sSup` overlap
presentation, not the exact Euclidean / `ENNReal` manuscript API.
-/

namespace Homogenization
namespace Book
namespace Ch03

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Legacy

/-- Legacy componentwise fractional-Sobolev regularity for a vector force. -/
def ForceSobolevRegularity {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (g : Vec d → Vec d) : Prop :=
  ∀ i : Fin d,
    Ch01.Legacy.MemFractionalSobolev Q s (2 : ℝ≥0∞) (fun x => g x i)

/-- Legacy scale-normalized componentwise fractional-Sobolev seminorm. -/
noncomputable def scaleNormalizedPositiveSobolevVectorSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  cubeBesovScaleWeight (-s) Q *
    ∑ i : Fin d,
      Ch01.Legacy.fractionalSobolevSeminorm Q s (2 : ℝ≥0∞) (fun x => g x i)

/-- Legacy dual-Besov wrapper used by the Chapter 3 compatibility lane.

Its body is `scaleNormalizedDualNegativeBesovVectorNormTwo`; it is not an
identification with either Chapter 1 negative-Sobolev primitive. -/
noncomputable abbrev scaleNormalizedNegativeSobolevVectorNormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  scaleNormalizedDualNegativeBesovVectorNormTwo Q s F

/-- Legacy dual-Besov compatibility left-hand side of the homogenization
comparison. -/
noncomputable def homogenizationComparisonNegativeSobolevLHS {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d)
    (s : ℝ) (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : ℝ :=
  scaleNormalizedNegativeSobolevVectorNormTwo Q s
      (homogenizationComparisonConstantGradientField a0 u v) +
    scaleNormalizedNegativeSobolevVectorNormTwo Q s
      (homogenizationComparisonFluxField Q a a0 u v)

theorem scaleNormalizedPositiveSobolevVectorSeminormTwo_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (g : Vec d → Vec d) :
    0 ≤ scaleNormalizedPositiveSobolevVectorSeminormTwo Q s g := by
  unfold scaleNormalizedPositiveSobolevVectorSeminormTwo
  exact mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q)
    (Finset.sum_nonneg fun i _ =>
      Gagliardo.cubeGagliardoSeminorm_nonneg Q s (2 : ℝ≥0∞) (fun x => g x i))

theorem forceSobolevRegularity_memLp {d : ℕ} {Q : TriadicCube d}
    {s : ℝ} {g : Vec d → Vec d}
    (hg : ForceSobolevRegularity Q s g) :
    MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  exact MeasureTheory.MemLp.of_eval fun i => (hg i).memLp

end Legacy

theorem cubeLpNorm_two_vec_le_sum_components {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) u ≤
      ∑ i : Fin d, cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x i) := by
  let μ : MeasureTheory.Measure (Vec d) := normalizedCubeMeasure Q
  let D : Vec d → ℝ := fun x => ∑ i : Fin d, ‖u x i‖
  have hcoord_mem :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) μ := by
    intro i
    simpa [μ] using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hcoord_norm_mem :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ := by
    intro i
    simpa using (hcoord_mem i).norm
  have hD_mem : MeasureTheory.MemLp D (2 : ℝ≥0∞) μ := by
    have hsum :=
      MeasureTheory.memLp_finsetSum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := Finset.univ)
        (f := fun i : Fin d => fun x : Vec d => ‖u x i‖)
        (fun i _hi => hcoord_norm_mem i)
    simpa [D] using hsum
  have hvec_le :
      MeasureTheory.eLpNorm u (2 : ℝ≥0∞) μ ≤
        MeasureTheory.eLpNorm D (2 : ℝ≥0∞) μ := by
    have hpoint :
        ∀ᵐ x ∂μ, ‖u x‖ ≤ (1 : ℝ) * ‖D x‖ := by
      exact Filter.Eventually.of_forall fun x => by
        have hD_nonneg : 0 ≤ D x :=
          Finset.sum_nonneg fun i _hi => norm_nonneg _
        have hu_le_D : ‖u x‖ ≤ D x := by
          refine (pi_norm_le_iff_of_nonneg hD_nonneg).2 ?_
          intro i
          exact Finset.single_le_sum
            (fun j _hj => norm_nonneg (u x j)) (Finset.mem_univ i)
        simpa [Real.norm_eq_abs, abs_of_nonneg hD_nonneg] using hu_le_D
    simpa using
      (MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint
        (2 : ℝ≥0∞))
  have hsum_eLp :
      MeasureTheory.eLpNorm D (2 : ℝ≥0∞) μ ≤
        ∑ i : Fin d,
          MeasureTheory.eLpNorm (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ := by
    have hD :
        D = ∑ i : Fin d, (fun x : Vec d => ‖u x i‖) := by
      funext x
      simp [D]
    rw [hD]
    exact
      MeasureTheory.eLpNorm_sum_le
        (μ := μ) (p := (2 : ℝ≥0∞)) (s := Finset.univ)
        (f := fun i : Fin d => fun x : Vec d => ‖u x i‖)
        (fun i _hi => (hcoord_norm_mem i).1)
        (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
  have hmain :
      MeasureTheory.eLpNorm u (2 : ℝ≥0∞) μ ≤
        ∑ i : Fin d,
          MeasureTheory.eLpNorm (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ :=
    hvec_le.trans hsum_eLp
  have hsum_ne_top :
      (∑ i : Fin d,
          MeasureTheory.eLpNorm (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun i _hi => (hcoord_norm_mem i).2.ne
  have htoReal :
      (MeasureTheory.eLpNorm u (2 : ℝ≥0∞) μ).toReal ≤
        (∑ i : Fin d,
          MeasureTheory.eLpNorm (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ).toReal :=
    ENNReal.toReal_mono hsum_ne_top hmain
  rw [ENNReal.toReal_sum (fun i _hi => (hcoord_norm_mem i).2.ne)] at htoReal
  have hsum_toReal_norm :
      (∑ i : Fin d,
          (MeasureTheory.eLpNorm (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ).toReal) =
        ∑ i : Fin d,
          (MeasureTheory.eLpNorm (fun x => u x i) (2 : ℝ≥0∞) μ).toReal := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [MeasureTheory.eLpNorm_norm]
  rw [hsum_toReal_norm] at htoReal
  simpa [cubeLpNorm, μ] using htoReal

theorem sqrt_cubeBesovPositiveVectorDepthAverage_le_sum_components
    {d : ℕ} (Q : TriadicCube d) (g : Vec d → Vec d) (j : ℕ)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    Real.sqrt (cubeBesovPositiveVectorDepthAverage Q g j) ≤
      ∑ i : Fin d,
        Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x => g x i) j) := by
  classical
  let A : TriadicCube d → Fin d → ℝ :=
    fun R i => cubeLpNorm R (2 : ℝ≥0∞) (fun x => cubeFluctuationVec R g x i)
  have hA_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, ∀ i ∈ Finset.univ, 0 ≤ A R i := by
    intro R _hR i _hi
    exact cubeLpNorm_nonneg R (2 : ℝ≥0∞) _
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R g)) ^ 2 ≤
          (∑ i : Fin d, A R i) ^ 2 := by
    intro R hR
    have hgR : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic (E := Vec d) hR hg
    have hfluct :
        MeasureTheory.MemLp (cubeFluctuationVec R g) (2 : ℝ≥0∞)
          (normalizedCubeMeasure R) :=
      memLp_cubeFluctuationVec R g hgR
    have hnorm :=
      cubeLpNorm_two_vec_le_sum_components R (cubeFluctuationVec R g) hfluct
    exact (sq_le_sq₀
      (cubeLpNorm_nonneg R (2 : ℝ≥0∞) (cubeFluctuationVec R g))
      (Finset.sum_nonneg fun i _hi => hA_nonneg R hR i (Finset.mem_univ i))).mpr hnorm
  have havg_le :
      cubeBesovPositiveVectorDepthAverage Q g j ≤
        descendantsAverage Q j fun R => (∑ i : Fin d, A R i) ^ 2 := by
    unfold cubeBesovPositiveVectorDepthAverage
    exact descendantsAverage_le_descendantsAverage Q j hpoint
  calc
    Real.sqrt (cubeBesovPositiveVectorDepthAverage Q g j)
        ≤
          Real.sqrt (descendantsAverage Q j fun R => (∑ i : Fin d, A R i) ^ 2) :=
            Real.sqrt_le_sqrt havg_le
    _ =
          (descendantsAverage Q j fun R => (∑ i : Fin d, A R i) ^ 2) ^
            (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    _ ≤
          ∑ i : Fin d,
            (descendantsAverage Q j fun R => (A R i) ^ 2) ^ (1 / 2 : ℝ) := by
            simpa using
              descendantsAverage_L2_sum_le_sum_descendantsAverage_L2
                Q j Finset.univ A hA_nonneg
    _ =
          ∑ i : Fin d,
            Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞)
              (fun x => g x i) j) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          have hbase :
              descendantsAverage Q j (fun R => (A R i) ^ 2) =
                cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x => g x i) j := by
            unfold cubeBesovDepthAverage descendantsAverage A cubeBesovOscillation
            apply congrArg (fun z : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * z)
            refine Finset.sum_congr rfl ?_
            intro R _hR
            rw [cubeFluctuation_component_eq_cubeFluctuationVec_component R g i]
            norm_num
          rw [hbase, Real.sqrt_eq_rpow]

theorem cubeBesovPositiveVectorPartialSeminormTwo_le_scaleWeight_mul_sum_components
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤
      cubeBesovScaleWeight (-s) Q *
        ∑ i : Fin d,
          cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => g x i) := by
  classical
  let W : ℝ := cubeBesovScaleWeight (-s) Q
  let A : ℕ → Fin d → ℝ :=
    fun j i =>
      W * cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => g x i) j
  have hW_nonneg : 0 ≤ W := cubeBesovScaleWeight_nonneg (-s) Q
  have hA_nonneg :
      ∀ j ∈ Finset.range (N + 1), ∀ i ∈ Finset.univ, 0 ≤ A j i := by
    intro j _hj i _hi
    exact mul_nonneg hW_nonneg
      (cubeBesovDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) (fun x => g x i) j)
  have hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeBesovPositiveVectorDepthSeminorm Q s g j ≤
          ∑ i : Fin d, A j i := by
    intro j _hj
    have hroot :=
      sqrt_cubeBesovPositiveVectorDepthAverage_le_sum_components Q g j hg
    have hscale :
        cubeBesovPositiveVectorDepthSeminorm Q s g j =
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (cubeBesovPositiveVectorDepthAverage Q g j) := rfl
    rw [hscale]
    calc
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (cubeBesovPositiveVectorDepthAverage Q g j)
          ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          ∑ i : Fin d,
            Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞)
              (fun x => g x i) j) := by
            exact mul_le_mul_of_nonneg_left hroot
              (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      _ =
        ∑ i : Fin d, A j i := by
          unfold A W
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          have hcoord :=
            cubeBesovPositiveVectorDepthSeminorm_coordinateVectorField
              Q s i (fun x => g x i) j
          unfold cubeBesovPositiveVectorDepthSeminorm at hcoord
          rw [cubeBesovPositiveVectorDepthAverage_coordinateVectorField] at hcoord
          simpa [Real.sqrt_eq_rpow] using hcoord
  have hsq :
      (cubeBesovPositiveVectorPartialSeminormTwo Q s N g) ^ 2 ≤
        ∑ j ∈ Finset.range (N + 1), (∑ i : Fin d, A j i) ^ 2 := by
    rw [sq_cubeBesovPositiveVectorPartialSeminormTwo]
    refine Finset.sum_le_sum ?_
    intro j hj
    have hleft_nonneg :
        0 ≤ cubeBesovPositiveVectorDepthSeminorm Q s g j :=
      cubeBesovPositiveVectorDepthSeminorm_nonneg Q s g j
    have hright_nonneg : 0 ≤ ∑ i : Fin d, A j i :=
      Finset.sum_nonneg fun i hi => hA_nonneg j hj i hi
    nlinarith [hdepth j hj]
  have hpartial_nonneg :
      0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s N g :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s N g
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N g
        =
          Real.sqrt ((cubeBesovPositiveVectorPartialSeminormTwo Q s N g) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hpartial_nonneg]
    _ ≤
          Real.sqrt (∑ j ∈ Finset.range (N + 1), (∑ i : Fin d, A j i) ^ 2) :=
            Real.sqrt_le_sqrt hsq
    _ ≤
          ∑ i : Fin d,
            Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j i) ^ 2) := by
            exact sqrt_sum_sq_sum_le_sum_sqrt_sum_sq
              (Finset.range (N + 1)) Finset.univ A hA_nonneg
    _ =
          W *
            ∑ i : Fin d,
              cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
                (fun x => g x i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          unfold A cubeBesovPartialSeminorm
          have hsqrt :=
            sqrt_sum_sq_const_mul_eq_componentwise
              (Finset.range (N + 1)) W
              (fun j => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞)
                (fun x => g x i) j) hW_nonneg
          simpa [Real.sqrt_eq_rpow] using hsqrt

namespace Legacy

theorem cubeBesovPositiveVectorPartialSeminormTwo_le_const_mul_sobolev
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {s : ℝ} (N : ℕ)
    (g : Vec d → Vec d) (hs : 0 < s) (_hs1 : s ≤ 1)
    (hg : ForceSobolevRegularity Q s g) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤
      ((3 : ℝ) ^ ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d) *
        scaleNormalizedPositiveSobolevVectorSeminormTwo Q s g := by
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d
  have hmem : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    forceSobolevRegularity_memLp hg
  have hbase :=
    cubeBesovPositiveVectorPartialSeminormTwo_le_scaleWeight_mul_sum_components
      Q s N g hmem
  have hcomponent :
      ∀ i : Fin d,
        cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => g x i) ≤
          (3 : ℝ) ^ ((d : ℝ) / 2) *
            (Ch01.Legacy.wspVsBsppConstant d *
              Ch01.Legacy.fractionalSobolevSeminorm Q s (2 : ℝ≥0∞)
                (fun x => g x i)) := by
    intro i
    obtain ⟨gi, hgi_meas, hgi_ae_norm⟩ :=
      (hg i).memLp.aestronglyMeasurable.aemeasurable
    have hgi_ae : (fun x => g x i) =ᵐ[Homogenization.cubeMeasure Q] gi :=
      Gagliardo.ae_normalizedCubeMeasure_iff.1 hgi_ae_norm
    have hgiLp : MeasureTheory.MemLp gi (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
      (hg i).memLp.ae_eq hgi_ae_norm
    have hgiW : Gagliardo.MemWsp Q s (2 : ℝ≥0∞) gi :=
      (Gagliardo.memWsp_congr_ae hgi_ae).1 (hg i).memWsp
    have hpartial_eq :
        cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => g x i) =
          cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N gi :=
      Gagliardo.overlap_partialSeminorm_congr_ae hgi_ae
    have hfrac_eq :
        Ch01.Legacy.fractionalSobolevSeminorm Q s (2 : ℝ≥0∞) (fun x => g x i) =
          Ch01.Legacy.fractionalSobolevSeminorm Q s (2 : ℝ≥0∞) gi :=
      congrArg ENNReal.toReal (Gagliardo.cubeGagliardoESeminorm_congr_ae hgi_ae)
    have hdisjoint_overlap :=
      cubeBesovPartialSeminorm_le_three_rpow_mul_overlapPartialSeminorm
        Q s (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (by norm_num : 0 < ENNReal.toReal (2 : ℝ≥0∞))
        (by norm_num : 1 ≤ ENNReal.toReal (2 : ℝ≥0∞))
        N (fun x => g x i)
    have hSob :=
      Ch01.Legacy.besovOverlapPartial_le_const_mul_gagliardo
        (Q := Q) (s := s) (p := (2 : ℝ≥0∞))
        (u := gi) hs (by norm_num) (by norm_num)
        hgi_meas hgiLp hgiW N
    calc
      cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x => g x i)
          ≤
            (3 : ℝ) ^ ((d : ℝ) / ENNReal.toReal (2 : ℝ≥0∞)) *
              cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
                (fun x => g x i) := hdisjoint_overlap
      _ =
            (3 : ℝ) ^ ((d : ℝ) / 2) *
              cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
                (fun x => g x i) := by norm_num
      _ ≤
            (3 : ℝ) ^ ((d : ℝ) / 2) *
              (Ch01.Legacy.wspVsBsppConstant d *
                Ch01.Legacy.fractionalSobolevSeminorm Q s (2 : ℝ≥0∞)
                  (fun x => g x i)) := by
            have hSob' :
                cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
                    (fun x => g x i) ≤
                  Ch01.Legacy.wspVsBsppConstant d *
                    Ch01.Legacy.fractionalSobolevSeminorm Q s (2 : ℝ≥0∞)
                      (fun x => g x i) := by
              simpa [hpartial_eq, hfrac_eq] using hSob
            exact mul_le_mul_of_nonneg_left hSob'
              (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hsum :
      ∑ i : Fin d,
          cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => g x i) ≤
        (3 : ℝ) ^ ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d *
          ∑ i : Fin d,
            Ch01.Legacy.fractionalSobolevSeminorm Q s (2 : ℝ≥0∞)
              (fun x => g x i) := by
    calc
      ∑ i : Fin d,
          cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => g x i)
          ≤
        ∑ i : Fin d,
          (3 : ℝ) ^ ((d : ℝ) / 2) *
            (Ch01.Legacy.wspVsBsppConstant d *
              Ch01.Legacy.fractionalSobolevSeminorm Q s (2 : ℝ≥0∞)
                (fun x => g x i)) := by
          exact Finset.sum_le_sum fun i _ => hcomponent i
      _ =
        (3 : ℝ) ^ ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d *
          ∑ i : Fin d,
              Ch01.Legacy.fractionalSobolevSeminorm Q s (2 : ℝ≥0∞)
                (fun x => g x i) := by
          rw [Finset.mul_sum]
          ring_nf
  have hW_nonneg : 0 ≤ cubeBesovScaleWeight (-s) Q :=
    cubeBesovScaleWeight_nonneg (-s) Q
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N g
        ≤ cubeBesovScaleWeight (-s) Q *
          ∑ i : Fin d,
            cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
              (fun x => g x i) := hbase
    _ ≤ cubeBesovScaleWeight (-s) Q *
          ((3 : ℝ) ^ ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d *
            ∑ i : Fin d,
              Ch01.Legacy.fractionalSobolevSeminorm Q s (2 : ℝ≥0∞)
                (fun x => g x i)) := by
          exact mul_le_mul_of_nonneg_left hsum hW_nonneg
    _ =
      ((3 : ℝ) ^ ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d) *
        scaleNormalizedPositiveSobolevVectorSeminormTwo Q s g := by
          unfold scaleNormalizedPositiveSobolevVectorSeminormTwo
          ring

theorem ForceSobolevRegularity.toForceBesovRegularity
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : ForceSobolevRegularity Q s g) (hs : 0 < s) (hs1 : s ≤ 1) :
    ForceBesovRegularity Q s g := by
  refine ⟨forceSobolevRegularity_memLp hg, ?_⟩
  refine ⟨((3 : ℝ) ^ ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d) *
      scaleNormalizedPositiveSobolevVectorSeminormTwo Q s g, ?_⟩
  rintro x ⟨N, rfl⟩
  exact cubeBesovPositiveVectorPartialSeminormTwo_le_const_mul_sobolev
    Q N g hs hs1 hg

theorem scaleNormalizedPositiveBesovVectorSeminormTwo_le_const_mul_sobolev
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {s : ℝ} (g : Vec d → Vec d)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hg : ForceSobolevRegularity Q s g) :
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s g ≤
      ((3 : ℝ) ^ ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d) *
        scaleNormalizedPositiveSobolevVectorSeminormTwo Q s g := by
  simpa [scaleNormalizedPositiveBesovVectorSeminormTwo] using
    cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q s g
      (fun N =>
        cubeBesovPositiveVectorPartialSeminormTwo_le_const_mul_sobolev
          Q N g hs hs1 hg)

theorem homogenizationComparisonNegativeSobolevLHS_le_const_mul_negativeBesovLHS
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (a0 : ConstantCoeffMatrix d) (s : ℝ)
    (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (hs : 0 < s) :
    homogenizationComparisonNegativeSobolevLHS Q a a0 s u v ≤
      ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s)) *
        homogenizationComparisonNegativeBesovLHS Q a a0 s u v := by
  let K : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s)
  let Gc : Vec d → Vec d :=
    homogenizationComparisonConstantGradientField a0 u v
  let Gf : Vec d → Vec d :=
    homogenizationComparisonFluxField Q a a0 u v
  have huGrad : MemVectorL2 (cubeSet Q) u.grad := by
    simpa using (publicH1ToCubeSet u).grad_memVectorL2
  have hvGrad : MemVectorL2 (cubeSet Q) v.grad := by
    simpa using (publicH1ToCubeSet v).grad_memVectorL2
  have hgradDiff : MemVectorL2 (cubeSet Q) (fun x => u.grad x - v.grad x) :=
    huGrad.sub hvGrad
  have hEll0 :
      IsEllipticFieldOn a0.lam a0.Lam (cubeSet Q)
        (constantCoeffField a0.matrix) :=
    constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0
      (measurableSet_cubeSet Q)
  have hGc_mem : MemVectorL2 (cubeSet Q) Gc := by
    simpa [Gc, homogenizationComparisonConstantGradientField, constantCoeffField] using!
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hgradDiff
  let GfInternal : Vec d → Vec d :=
    fluxComparison (publicCoeffField Q a) a0.matrix u.grad v.grad
  have hfluxA : MemVectorL2 (cubeSet Q)
      (fun x => matVecMul (publicCoeffField Q a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) huGrad
  have hflux0 : MemVectorL2 (cubeSet Q)
      (fun x => matVecMul a0.matrix (v.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hvGrad
  have hGfInternal_mem : MemVectorL2 (cubeSet Q) GfInternal := by
    dsimp [GfInternal, fluxComparison]
    exact hfluxA.sub hflux0
  have hGf_ae : Gf =ᵐ[volumeMeasureOn (cubeSet Q)] GfInternal := by
    dsimp [Gf, GfInternal]
    exact
      homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
        (Q := Q) (a := a) (a0 := a0) u v
  have hGf_mem : MemVectorL2 (cubeSet Q) Gf :=
    MeasureTheory.MemLp.ae_eq hGf_ae.symm hGfInternal_mem
  have hGc_bound :
      scaleNormalizedNegativeSobolevVectorNormTwo Q s Gc ≤
        K * cubeBesovNegativeVectorSeminormTwo Q s Gc := by
    simpa [scaleNormalizedNegativeSobolevVectorNormTwo, K] using
      scaleNormalizedDualNegativeBesovVectorNormTwo_le_note_constant_mul_cubeBesovNegativeVectorSeminormTwo
        Q s Gc hs hGc_mem
  have hGf_bound :
      scaleNormalizedNegativeSobolevVectorNormTwo Q s Gf ≤
        K * cubeBesovNegativeVectorSeminormTwo Q s Gf := by
    simpa [scaleNormalizedNegativeSobolevVectorNormTwo, K] using
      scaleNormalizedDualNegativeBesovVectorNormTwo_le_note_constant_mul_cubeBesovNegativeVectorSeminormTwo
        Q s Gf hs hGf_mem
  calc
    homogenizationComparisonNegativeSobolevLHS Q a a0 s u v
        = scaleNormalizedNegativeSobolevVectorNormTwo Q s Gc +
            scaleNormalizedNegativeSobolevVectorNormTwo Q s Gf := by
          rfl
    _ ≤ K * cubeBesovNegativeVectorSeminormTwo Q s Gc +
        K * cubeBesovNegativeVectorSeminormTwo Q s Gf :=
          add_le_add hGc_bound hGf_bound
    _ =
        K * homogenizationComparisonNegativeBesovLHS Q a a0 s u v := by
          unfold homogenizationComparisonNegativeBesovLHS
          dsimp [Gc, Gf, K]
          ring

end Legacy

end

end Ch03
end Book
end Homogenization
