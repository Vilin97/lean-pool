/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePAveraging
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarDivergenceGradientW1p
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpSolutionStability
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge

/-!
# Exact-overlap finite-`p` PDE splitting

The smooth overlap average gives a paired `H¹`/`W¹ᵖ` divergence datum.  This
file combines that datum with the constant-coefficient cube estimates: the
original zero-trace solution is compared to the solution driven by the smooth
average, and the latter gradient receives a finite-`W¹ᵖ` representative.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem cubeDirichletDivergenceProblem_to_centered_normalized
    {d : ℕ} [NeZero d] (m : ℤ) {u : H10Function (openCubeSet (originCube d m))}
    {h : Vec d → Vec d}
    (hh : MemLp (fun x => HilbertVec.ofVec (h x)) 2
      (normalizedCubeMeasure (originCube d m)))
    (hu : CubeDirichletDivergenceProblem (originCube d m) u h) :
    IsCenteredCubeH10ScalarDivergenceSolution m 1 u
      ⟨h, hh⟩ := by
  intro phi
  have hmeasure : (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
    simp only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [hmeasure, MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_smul_measure, smul_eq_mul, smul_eq_mul, one_mul,
    hu phi]
  ring

/-- On every origin cube, a zero-trace solution splits off the smooth overlap
average.  The constants depend only on the fixed dimension and finite
exponent, and are chosen before the cube, averaging depth, partition, datum,
and supplied solution. -/
theorem exists_exactOverlapFiniteP_pdeSplitting
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (j : ℕ)
      (P : SmoothOverlapPartition (originCube d m) j) (h : Vec d → Vec d),
      MemLp (fun x => HilbertVec.ofVec (h x)) 2
        (normalizedCubeMeasure (originCube d m)) →
      MemLp (fun x => HilbertVec.ofVec (h x)) q.exponent
        (normalizedCubeMeasure (originCube d m)) →
      ∀ w : H10Function (openCubeSet (originCube d m)),
      CubeDirichletDivergenceProblem (originCube d m) w h →
        ∃ v : H10Function (openCubeSet (originCube d m)),
          ∃ V : CubeVectorW1pFunction (originCube d m) q,
            CubeDirichletDivergenceProblem (originCube d m) v (P.averagingField h) ∧
              V.toField = v.toH1Function.grad ∧
                eLpNorm (fun x => HilbertVec.ofVec
                  (w.toH1Function.grad x - v.toH1Function.grad x)) q.exponent
                    (normalizedCubeMeasure (originCube d m)) ≤
                  C * eLpNorm (fun x => HilbertVec.ofVec
                    (h x - P.averagingField h x)) q.exponent
                      (normalizedCubeMeasure (originCube d m)) ∧
                eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
                    (normalizedCubeMeasure (originCube d m)) ≤
                  C * eLpNorm (fun x => HilbertMat.ofMat
                    ((P.averagingCompetitorW1p h q).jacobian x)) q.exponent
                      (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨Cstab, hCstab_top, hstab⟩ :=
    CubeCalderonZygmund.INTERNAL.centeredCubeH10ScalarDivergence_solution_stability d q
  obtain ⟨Cgrad, hCgrad_top, hgrad⟩ :=
    CubeCalderonZygmund.exists_cubeVectorW1p_scalarDivergence_cz_of_paired d q
  refine ⟨Cstab + Cgrad, ENNReal.add_lt_top.mpr ⟨hCstab_top, hCgrad_top⟩, ?_⟩
  intro m j P h hh2 hhq w hw
  obtain ⟨_, _, _, _, _⟩ := P.exists_synchronized_averagingCompetitors h q hh2 hhq
  let G2 : CubeVectorH1Function (originCube d m) := P.averagingCompetitor h
  let Gq : CubeVectorW1pFunction (originCube d m) q := P.averagingCompetitorW1p h q
  have hG2 : G2.toField = P.averagingField h := by
    rfl
  have hGq : Gq.toField = P.averagingField h := by
    rfl
  have hGgrad : ∀ x i k, (G2.coord i).grad x k = Gq.jacobian x i k := by
    intro x i k
    rfl
  have hG2_l2 : MemLp (fun x => HilbertVec.ofVec (G2.toField x)) 2
      (normalizedCubeMeasure (originCube d m)) := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using!
      H1Function.memL2_normalizedCubeMeasure (G2.coord i)
  have hGq_q : MemLp (fun x => HilbertVec.ofVec (Gq.toField x)) q.exponent
      (normalizedCubeMeasure (originCube d m)) :=
    Gq.euclideanMemLp
  let hField : CubeEuclideanL2LpField (originCube d m) q :=
    { toField := h
      euclideanMemLp := hhq
      euclideanMemL2 := hh2 }
  let gField : CubeEuclideanL2LpField (originCube d m) q :=
    { toField := Gq.toField
      euclideanMemLp := hGq_q
      euclideanMemL2 := hG2_l2 }
  obtain ⟨v, hv⟩ :=
    exists_cubeDirichletDivergenceProblem_of_memLp_normalizedCubeMeasure
      (Q := originCube d m) (h := G2.toField)
      G2.memLp_toField_normalizedCubeMeasure
  obtain ⟨V, hVfield, hVbound⟩ := hgrad m G2 Gq (by rw [hG2, hGq]) hGgrad v (by
    simpa only [hG2] using hv)
  have hw_normalized := cubeDirichletDivergenceProblem_to_centered_normalized m hh2 hw
  have hv_normalized :=
    cubeDirichletDivergenceProblem_to_centered_normalized m hG2_l2 hv
  have hstab_bound := hstab m 1 hField gField w v (by norm_num) hw_normalized hv_normalized
  refine ⟨v, V, hv, hVfield, ?_, ?_⟩
  · calc
      eLpNorm (fun x => HilbertVec.ofVec
          (w.toH1Function.grad x - v.toH1Function.grad x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) =
        (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
          (fun x => w.toH1Function.grad x - v.toH1Function.grad x) := by
            simp only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
              BoundedMeasurableDomain.normalizedLpENorm, centeredCubeDomain,
              cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
              euclideanNorm_eq_norm_ofVec, MeasureTheory.eLpNorm_norm]
      _ ≤ Cstab * (ENNReal.ofReal (1 : ℝ))⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            (fun x => hField.toField x - gField.toField x) := hstab_bound
      _ = Cstab * eLpNorm (fun x => HilbertVec.ofVec
          (h x - P.averagingField h x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) := by
            simp only [ENNReal.ofReal_one, inv_one, mul_one,
              BoundedMeasurableDomain.normalizedEuclideanLpENorm,
              BoundedMeasurableDomain.normalizedLpENorm, centeredCubeDomain,
              cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
              euclideanNorm_eq_norm_ofVec, MeasureTheory.eLpNorm_norm,
              hField, gField, hGq]
      _ ≤ (Cstab + Cgrad) * eLpNorm (fun x => HilbertVec.ofVec
          (h x - P.averagingField h x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) := by
            gcongr
            exact le_add_right le_rfl
  · calc
      eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) ≤
        Cgrad * eLpNorm (fun x => HilbertMat.ofMat (Gq.jacobian x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) := hVbound
      _ = Cgrad * eLpNorm (fun x => HilbertMat.ofMat
          ((P.averagingCompetitorW1p h q).jacobian x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) := by rfl
      _ ≤ (Cstab + Cgrad) * eLpNorm (fun x => HilbertMat.ofMat
          ((P.averagingCompetitorW1p h q).jacobian x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) := by
            gcongr
            exact le_add_left le_rfl

end

end Homogenization
