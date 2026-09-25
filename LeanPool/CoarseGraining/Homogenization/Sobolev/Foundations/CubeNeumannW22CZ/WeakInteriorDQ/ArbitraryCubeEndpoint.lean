/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.OriginCubeEndpoint
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.PoissonTranslation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianTranslation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentExactEnergy

/-! # Arbitrary Cube Endpoint -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

noncomputable def originCubeWeakInteriorDepthConstantExact (d : ℕ) (m : ℤ) : ℝ :=
  let Q : TriadicCube d := originCube d m
  (((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ)) *
      (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) *
    (((d : ℝ) * (d : ℝ)) *
      MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m)

theorem originCubeWeakInteriorDepthConstantExact_nonneg (d : ℕ) (m : ℤ) :
    0 ≤ originCubeWeakInteriorDepthConstantExact d m := by
  let Q : TriadicCube d := originCube d m
  have hparent :
      0 ≤ ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ)) *
        (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue := by
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hcount :
      0 ≤ ((d : ℝ) * (d : ℝ)) *
        MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d))
      (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact_nonneg d m)
  dsimp [originCubeWeakInteriorDepthConstantExact, Q]
  exact mul_nonneg hparent hcount

/-- The C.2 depth constant for an arbitrary cube, transported from the
scale-sharp centered-cube estimate at the same scale. -/
noncomputable def cubeWeakInteriorDepthConstant {d : ℕ} (Q : TriadicCube d) : ℝ :=
  originCubeWeakInteriorDepthConstantExact d Q.scale

theorem cubeWeakInteriorDepthConstant_nonneg {d : ℕ} (Q : TriadicCube d) :
    0 ≤ cubeWeakInteriorDepthConstant Q := by
  exact originCubeWeakInteriorDepthConstantExact_nonneg d Q.scale

theorem originCubeWeakInteriorDepthConstantExact_eq_unit (d : ℕ) (m : ℤ) :
    originCubeWeakInteriorDepthConstantExact d m =
      originCubeWeakInteriorDepthConstantExact d 0 := by
  let V : ℝ := cubeVolume (originCube d m)
  let A : ℝ := (V⁻¹) ^ (1 / 2 : ℝ)
  let C₀ : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue
  let D₂ : ℝ := (d : ℝ) * (d : ℝ)
  let K : ℝ :=
    MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d m
  let K₀ : ℝ :=
    MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact d 0
  have hcancel : A * K = K₀ := by
    simpa [A, K, K₀, V] using
      MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstantExact_volume_cancel d m
  have h0vol : cubeVolume (originCube d 0) = 1 := by
    simp [cubeVolume_eq_scaleFactor_pow]
  have h0 :
      originCubeWeakInteriorDepthConstantExact d 0 = C₀ * (D₂ * K₀) := by
    dsimp [originCubeWeakInteriorDepthConstantExact, C₀, D₂, K₀]
    rw [h0vol]
    norm_num
  calc
    originCubeWeakInteriorDepthConstantExact d m
        = C₀ * (D₂ * (A * K)) := by
          dsimp [originCubeWeakInteriorDepthConstantExact, A, C₀, D₂, K, V]
          ring
    _ = C₀ * (D₂ * K₀) := by
          rw [hcancel]
    _ = originCubeWeakInteriorDepthConstantExact d 0 := h0.symm

theorem cubeWeakInteriorDepthConstant_eq_dimensionConstant {d : ℕ}
    (Q : TriadicCube d) :
    cubeWeakInteriorDepthConstant Q =
      originCubeWeakInteriorDepthConstantExact d 0 := by
  exact originCubeWeakInteriorDepthConstantExact_eq_unit d Q.scale

namespace MeanZeroNeumannPoissonSolution

theorem originCube_sum_reducedSolverEnergyBoundExact_le_depthConstant_mul_cubeLpNorm
    {d : ℕ} {m : ℤ} {F : Vec d → ℝ} :
    (((cubeVolume (originCube d m))⁻¹) ^ (1 / (2 : ℝ)) *
          (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) *
        (∑ k : Fin d, ∑ _l : Fin d,
          originCubeParentReducedSolverEnergyBoundExact d m F k) ≤
      originCubeWeakInteriorDepthConstantExact d m *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
  let Q : TriadicCube d := originCube d m
  let P : ℝ :=
    ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ)) *
      (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue
  let K : ℝ := originCubeParentReducedSolverEnergyConstantExact d m
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  have hsum_eq :
      (∑ k : Fin d, ∑ _l : Fin d,
        originCubeParentReducedSolverEnergyBoundExact d m F k) =
        ((d : ℝ) * (d : ℝ)) * (K * L) := by
    calc
      (∑ k : Fin d, ∑ _l : Fin d,
        originCubeParentReducedSolverEnergyBoundExact d m F k)
          = ∑ k : Fin d, ∑ _l : Fin d, K * L := by
              refine Finset.sum_congr rfl ?_
              intro k _hk
              refine Finset.sum_congr rfl ?_
              intro _l _hl
              simpa [K, L, Q] using
                originCubeParentReducedSolverEnergyBoundExact_eq_constant_mul_cubeLpNorm
                  d m F k
      _ = ((d : ℝ) * (d : ℝ)) * (K * L) := by
            simp
            ring
  calc
    P * (∑ k : Fin d, ∑ _l : Fin d,
          originCubeParentReducedSolverEnergyBoundExact d m F k)
        = P * (((d : ℝ) * (d : ℝ)) * (K * L)) := by
          rw [hsum_eq]
    _ = originCubeWeakInteriorDepthConstantExact d m * L := by
          dsimp [originCubeWeakInteriorDepthConstantExact, P, K, L, Q]
          ring
    _ ≤ originCubeWeakInteriorDepthConstantExact d m *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
          exact le_rfl

theorem exists_hasWeakHessianOn_cube_hessianCoordL2NormSum_le_solverEnergyBound
    {d : ℕ} {Q : TriadicCube d} {F : Vec d → ℝ}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hmean : cubeAverage Q F = 0)
    (W : MeanZeroNeumannPoissonSolution Q F) :
    ∃ H : HasWeakHessianOn (openCubeSet Q) W.w.toH1Function,
      H.hessianCoordL2NormSum ≤
        ∑ i : Fin d, ∑ _j : Fin d,
          originCubeParentReducedSolverEnergyBoundExact d Q.scale
            (fun x => F (x + triadicCubeShift Q)) i := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let z : Vec d := triadicCubeShift Q
  let F₀ : Vec d → ℝ := fun x => F (x + z)
  let W₀ : MeanZeroNeumannPoissonSolution Q₀ F₀ := W.untranslateToOrigin Q
  have hF₀ : MeasureTheory.MemLp F₀ (2 : ℝ≥0∞) (normalizedCubeMeasure Q₀) := by
    simpa [Q₀, F₀, z] using memLp_originCube_comp_addRight_of_memLp Q hF
  have hmean₀ : cubeAverage Q₀ F₀ = 0 := by
    dsimp [Q₀, F₀, z]
    rw [cubeAverage_originCube_comp_addRight_eq Q F, hmean]
  rcases
    W₀.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_solverEnergyBoundExact
      hmean₀ hF₀ with
    ⟨_uP, _huP_toFun, _huP_grad, H₀, hH₀⟩
  have hU : openCubeSet Q = translateSet z (openCubeSet Q₀) := by
    simpa [Q₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let HT : HasWeakHessianOn (translateSet z (openCubeSet Q₀))
      (W₀.w.toH1Function.translate z) := H₀.translate z
  let H : HasWeakHessianOn (openCubeSet Q) W.w.toH1Function :=
    { hess := HT.hess
      hess_memL2 := by
        intro i j
        simpa [hU] using HT.hess_memL2 i j
      weak_second := by
        intro i j
        have hweak :
            HasWeakPartialDerivOn (openCubeSet Q) j
              (fun x => (W₀.w.toH1Function.translate z).grad x i)
              (HT.hess i j) := by
          simpa [hU] using HT.weak_second i j
        refine
          HasWeakPartialDerivOn.congr_of_eqOn
            (measurableSet_openCubeSet Q) ?_ ?_ hweak
        · intro x _hx
          exact congrArg (fun v : Vec d => v i)
            (W.untranslateToOrigin_translate_grad Q x)
        · intro x _hx
          rfl }
  refine ⟨H, ?_⟩
  have hH_HT : H.hessianCoordL2NormSum = HT.hessianCoordL2NormSum := by
    simp [H, hU, HasWeakHessianOn.hessianCoordL2NormSum,
      HasWeakHessianOn.hessCoordToScalarL2, Homogenization.toScalarL2]
  have hHT_H₀ : HT.hessianCoordL2NormSum = H₀.hessianCoordL2NormSum := by
    simpa [HT] using H₀.hessianCoordL2NormSum_translate_eq z
  calc
    H.hessianCoordL2NormSum = HT.hessianCoordL2NormSum := hH_HT
    _ = H₀.hessianCoordL2NormSum := hHT_H₀
    _ ≤ ∑ i : Fin d, ∑ _j : Fin d,
          originCubeParentReducedSolverEnergyBoundExact d Q.scale
            (fun x => F (x + triadicCubeShift Q)) i := by
          simpa [Q₀, F₀, z] using hH₀

theorem cubeBesovDepthSeminorm_grad_cube_le_weakInteriorDepthConstant
    {d : ℕ} {Q : TriadicCube d} {F : Vec d → ℝ}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hmean : cubeAverage Q F = 0)
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) (_N j : ℕ) (_hj : j ∈ Finset.range (_N + 1)) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i) j ≤
      cubeWeakInteriorDepthConstant Q *
        cubeLpNorm Q (2 : ℝ≥0∞) F := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let z : Vec d := triadicCubeShift Q
  let F₀ : Vec d → ℝ := fun x => F (x + z)
  rcases W.exists_hasWeakHessianOn_cube_hessianCoordL2NormSum_le_solverEnergyBound
      hF hmean with
    ⟨H, hH⟩
  let P : ℝ :=
    ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ)) *
      (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hdepth :
      cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
          (fun x => W.w.toH1Function.grad x i) j ≤
        P * H.hessianCoordL2NormSum := by
    simpa [P] using H.cubeBesovDepthSeminorm_gradCoord_le_parentVolume_scaledCoercive i j
  have hsum :
      P *
          (∑ k : Fin d, ∑ _l : Fin d,
            originCubeParentReducedSolverEnergyBoundExact d Q.scale F₀ k) ≤
        cubeWeakInteriorDepthConstant Q * cubeLpNorm Q (2 : ℝ≥0∞) F := by
    have horigin :=
      originCube_sum_reducedSolverEnergyBoundExact_le_depthConstant_mul_cubeLpNorm
        (d := d) (m := Q.scale) (F := F₀)
    have hnorm := cubeLpNorm_originCube_comp_addRight_eq_of_memLp Q hF
    calc
      P *
          (∑ k : Fin d, ∑ _l : Fin d,
            originCubeParentReducedSolverEnergyBoundExact d Q.scale F₀ k)
          ≤ originCubeWeakInteriorDepthConstantExact d Q.scale *
              cubeLpNorm Q₀ (2 : ℝ≥0∞) F₀ := by
              simpa [P, Q₀, cubeVolume_originCube_same_scale Q] using horigin
      _ = cubeWeakInteriorDepthConstant Q * cubeLpNorm Q (2 : ℝ≥0∞) F := by
            simp [cubeWeakInteriorDepthConstant, Q₀, F₀, z, hnorm]
  calc
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i) j
        ≤ P * H.hessianCoordL2NormSum := hdepth
    _ ≤ P *
          (∑ k : Fin d, ∑ _l : Fin d,
            originCubeParentReducedSolverEnergyBoundExact d Q.scale F₀ k) := by
          exact mul_le_mul_of_nonneg_left hH hP_nonneg
    _ ≤ cubeWeakInteriorDepthConstant Q * cubeLpNorm Q (2 : ℝ≥0∞) F := hsum

theorem cubePoissonGradientDualTestNormL2CoreEstimate_cube
    {d : ℕ} (Q : TriadicCube d) :
    CubePoissonGradientDualTestNormL2CoreEstimate Q
      (cubeWeakInteriorDepthConstant Q + cubePoissonGradientAverageConstant Q) := by
  refine
    cubePoissonGradientDualTestNormL2CoreEstimate_of_depthSeminorm
      (cubeWeakInteriorDepthConstant_nonneg Q) ?_
  intro F hF hmean W i N j hj
  exact
    cubeBesovDepthSeminorm_grad_cube_le_weakInteriorDepthConstant
      hF hmean W i N j hj

end MeanZeroNeumannPoissonSolution

end

end Homogenization
