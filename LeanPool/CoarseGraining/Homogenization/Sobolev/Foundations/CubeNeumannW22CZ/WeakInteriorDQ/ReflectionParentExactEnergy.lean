/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentSmoothBound

/-! # Reflection Parent Exact Energy -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {m : ℤ} {F : Vec d → ℝ}

theorem norm_gradToHilbertVectorL2_le_solverCubeLpNorm_exact
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ‖W.w.toH1Function.gradToHilbertVectorL2‖ ≤
      cubeMeanZeroH1CoerciveConstant (originCube d m) *
        ((cubeVolume (originCube d m)) ^ (1 / 2 : ℝ) *
          cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F) := by
  let Q : TriadicCube d := originCube d m
  calc
    ‖W.w.toH1Function.gradToHilbertVectorL2‖ =
        ‖W.w.gradToHilbertVectorL2‖ := rfl
    _ ≤ cubeMeanZeroH1CoerciveConstant Q *
          ‖Homogenization.toScalarL2
            (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF)‖ := by
          simpa [Q] using
            meanZeroNeumannPoissonSolution_norm_gradToHilbertVectorL2_le Q hF W
    _ = cubeMeanZeroH1CoerciveConstant Q *
          ((cubeVolume Q) ^ (1 / 2 : ℝ) *
            cubeLpNorm Q (2 : ℝ≥0∞) F) := by
          rw [norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two Q hF]

theorem norm_toScalarL2_le_solverCubeLpNorm_exact
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ‖W.w.toH1Function.toScalarL2‖ ≤
      cubeMeanZeroH1CoerciveConstant (originCube d m) *
        (cubeMeanZeroH1CoerciveConstant (originCube d m) *
          ((cubeVolume (originCube d m)) ^ (1 / 2 : ℝ) *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F)) := by
  let Q : TriadicCube d := originCube d m
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let hC : H1CoerciveEstimate (openCubeSet Q) :=
    scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q
  have hvalue :
      ‖W.w.toH1Function.toScalarL2‖ ≤
        cubeMeanZeroH1CoerciveConstant Q * W.w.gradientL2Norm := by
    change W.w.valueL2Norm ≤ cubeMeanZeroH1CoerciveConstant Q * W.w.gradientL2Norm
    simpa [cubeMeanZeroH1CoerciveConstant, hC] using hC.bound W.w
  calc
    ‖W.w.toH1Function.toScalarL2‖
        ≤ cubeMeanZeroH1CoerciveConstant Q * W.w.gradientL2Norm := hvalue
    _ ≤ cubeMeanZeroH1CoerciveConstant Q * ‖W.w.gradToHilbertVectorL2‖ := by
          exact mul_le_mul_of_nonneg_left
            (H1MeanZeroFunction.gradientL2Norm_le_norm_gradToHilbertVectorL2 W.w)
            (cubeMeanZeroH1CoerciveConstant_nonneg Q)
    _ ≤ cubeMeanZeroH1CoerciveConstant Q *
          (cubeMeanZeroH1CoerciveConstant Q *
            ((cubeVolume Q) ^ (1 / 2 : ℝ) *
              cubeLpNorm Q (2 : ℝ≥0∞) F)) := by
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [Q] using!
                norm_gradToHilbertVectorL2_le_solverCubeLpNorm_exact W hF)
            (cubeMeanZeroH1CoerciveConstant_nonneg Q)

/-- Scale-sharp forcing-facing reflected-parent reduced energy expression. -/
noncomputable def originCubeParentReducedSolverEnergyBoundExact
    (d : ℕ) (m : ℤ) (F : Vec d → ℝ) (_i : Fin d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let B : ℝ := (cubeVolume Q) ^ (1 / 2 : ℝ) * L
  ((4 : ℝ) *
    ((2 : ℝ) * ((3 : ℝ) ^ d * (cubeVolume Q * L ^ (2 : ℝ))) +
      ((3 : ℝ) *
        ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)) *
        ((2 : ℝ) * ((3 : ℝ) ^ d * (C * B) ^ 2) +
          (2 : ℝ) *
            (((d : ℝ) *
              (quantitativeCubeCutoffGradientConst d /
                (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2) *
              ((3 : ℝ) ^ d * (C * (C * B)) ^ 2))))) ^
    (1 / (2 : ℝ))

theorem originCubeParentReducedNormEnergyBound_le_solverEnergyBoundExact
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    (i : Fin d) :
    originCubeParentReducedNormEnergyBound W i ≤
      originCubeParentReducedSolverEnergyBoundExact d m F i := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let B : ℝ := (cubeVolume Q) ^ (1 / 2 : ℝ) * L
  let Kinner : ℝ :=
    (3 : ℝ) *
      ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)
  let Kouter : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2
  let A : ℝ :=
    (2 : ℝ) * ((3 : ℝ) ^ d * (cubeVolume Q * L ^ (2 : ℝ))) +
      Kinner *
        ((2 : ℝ) *
            ((3 : ℝ) ^ d * ‖W.w.toH1Function.gradToHilbertVectorL2‖ ^ 2) +
          (2 : ℝ) *
            (Kouter *
              ((3 : ℝ) ^ d * ‖W.w.toH1Function.toScalarL2‖ ^ 2)))
  let Benergy : ℝ :=
    (2 : ℝ) * ((3 : ℝ) ^ d * (cubeVolume Q * L ^ (2 : ℝ))) +
      Kinner *
        ((2 : ℝ) * ((3 : ℝ) ^ d * (C * B) ^ 2) +
          (2 : ℝ) *
            (Kouter * ((3 : ℝ) ^ d * (C * (C * B)) ^ 2)))
  have hgrad_sq :
      ‖W.w.toH1Function.gradToHilbertVectorL2‖ ^ 2 ≤ (C * B) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _)
      (by
        simpa [Q, C, L, B] using
          norm_gradToHilbertVectorL2_le_solverCubeLpNorm_exact W hF)
      2
  have hvalue_sq :
      ‖W.w.toH1Function.toScalarL2‖ ^ 2 ≤ (C * (C * B)) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _)
      (by
        simpa [Q, C, L, B] using
          norm_toScalarL2_le_solverCubeLpNorm_exact W hF)
      2
  have hthree_nonneg : 0 ≤ (3 : ℝ) ^ d := by positivity
  have hKinner_nonneg : 0 ≤ Kinner := by
    dsimp [Kinner]
    positivity
  have hKouter_nonneg : 0 ≤ Kouter := by
    dsimp [Kouter]
    positivity
  have hinner :
      (2 : ℝ) *
          ((3 : ℝ) ^ d * ‖W.w.toH1Function.gradToHilbertVectorL2‖ ^ 2) +
        (2 : ℝ) *
          (Kouter *
            ((3 : ℝ) ^ d * ‖W.w.toH1Function.toScalarL2‖ ^ 2)) ≤
      (2 : ℝ) * ((3 : ℝ) ^ d * (C * B) ^ 2) +
        (2 : ℝ) *
          (Kouter * ((3 : ℝ) ^ d * (C * (C * B)) ^ 2)) := by
    refine add_le_add ?_ ?_
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hgrad_sq hthree_nonneg)
        (by norm_num)
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hvalue_sq hthree_nonneg)
          hKouter_nonneg)
        (by norm_num)
  have hAB : A ≤ Benergy := by
    dsimp [A, Benergy]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hinner hKinner_nonneg) _
  have h4AB : (4 : ℝ) * A ≤ (4 : ℝ) * Benergy :=
    mul_le_mul_of_nonneg_left hAB (by norm_num)
  have h4A_nonneg : 0 ≤ (4 : ℝ) * A := by
    have hL_nonneg : 0 ≤ L := by
      dsimp [L]
      exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F
    have hL_sq_nonneg : 0 ≤ L ^ (2 : ℝ) :=
      Real.rpow_nonneg hL_nonneg _
    have hforce_nonneg :
        0 ≤ (2 : ℝ) * ((3 : ℝ) ^ d * (cubeVolume Q * L ^ (2 : ℝ))) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg hthree_nonneg
          (mul_nonneg (cubeVolume_nonneg Q) hL_sq_nonneg))
    have hgrad_term_nonneg :
        0 ≤ (2 : ℝ) *
          ((3 : ℝ) ^ d * ‖W.w.toH1Function.gradToHilbertVectorL2‖ ^ 2) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg hthree_nonneg (sq_nonneg _))
    have hvalue_term_nonneg :
        0 ≤ (2 : ℝ) *
          (Kouter * ((3 : ℝ) ^ d * ‖W.w.toH1Function.toScalarL2‖ ^ 2)) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg hKouter_nonneg
          (mul_nonneg hthree_nonneg (sq_nonneg _)))
    have hinner_orig_nonneg :
        0 ≤
          (2 : ℝ) *
              ((3 : ℝ) ^ d *
                ‖W.w.toH1Function.gradToHilbertVectorL2‖ ^ 2) +
            (2 : ℝ) *
              (Kouter *
                ((3 : ℝ) ^ d * ‖W.w.toH1Function.toScalarL2‖ ^ 2)) :=
      add_nonneg hgrad_term_nonneg hvalue_term_nonneg
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      exact add_nonneg hforce_nonneg
        (mul_nonneg hKinner_nonneg hinner_orig_nonneg)
    exact mul_nonneg (by norm_num) hA_nonneg
  simpa [originCubeParentReducedNormEnergyBound,
    originCubeParentReducedSolverEnergyBoundExact, Q, Qp, C, L, B, Kinner,
    Kouter, A, Benergy] using
    Real.rpow_le_rpow h4A_nonneg h4AB
      (by norm_num : 0 ≤ (1 / (2 : ℝ)))

theorem exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_solverEnergyBoundExact
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hmean : cubeAverage (originCube d m) F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
          cubeCoordinateFoldReflectedScalar (originCube d m)
            W.w.toH1Function.toFun ∧
        uP.grad =
          cubeCoordinateFoldReflectedVectorField (originCube d m)
            (fun y => W.w.toH1Function.grad y) ∧
          ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) W.w.toH1Function,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                originCubeParentReducedSolverEnergyBoundExact d m F i := by
  rcases
    W.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_normEnergyBound
      hmean hF with
    ⟨uP, huP_toFun, huP_grad, H, hH⟩
  refine ⟨uP, huP_toFun, huP_grad, H, hH.trans ?_⟩
  exact Finset.sum_le_sum fun i _hi =>
    Finset.sum_le_sum fun _j _hj =>
      originCubeParentReducedNormEnergyBound_le_solverEnergyBoundExact W hF i

private noncomputable def originCubeParentReducedSolverEnergyInsideExact
    (d : ℕ) (m : ℤ) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let V : ℝ := cubeVolume Q
  let B : ℝ := V ^ (1 / 2 : ℝ)
  let Kinner : ℝ :=
    (3 : ℝ) *
      ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)
  let Kouter : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2
  (4 : ℝ) *
    ((2 : ℝ) * ((3 : ℝ) ^ d * V) +
      Kinner *
        ((2 : ℝ) * ((3 : ℝ) ^ d * (C * B) ^ 2) +
          (2 : ℝ) * (Kouter * ((3 : ℝ) ^ d * (C * (C * B)) ^ 2))))

private theorem originCubeParentReducedSolverEnergyInsideExact_nonneg
    (d : ℕ) (m : ℤ) :
    0 ≤ originCubeParentReducedSolverEnergyInsideExact d m := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let V : ℝ := cubeVolume Q
  let B : ℝ := V ^ (1 / 2 : ℝ)
  let Kinner : ℝ :=
    (3 : ℝ) *
      ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)
  let Kouter : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    exact cubeVolume_nonneg Q
  have hKinner_nonneg : 0 ≤ Kinner := by
    dsimp [Kinner]
    positivity
  have hKouter_nonneg : 0 ≤ Kouter := by
    dsimp [Kouter]
    positivity
  have hmain_nonneg :
      0 ≤ (2 : ℝ) * ((3 : ℝ) ^ d * V) +
        Kinner *
          ((2 : ℝ) * ((3 : ℝ) ^ d * (C * B) ^ 2) +
            (2 : ℝ) * (Kouter * ((3 : ℝ) ^ d * (C * (C * B)) ^ 2))) := by
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (by norm_num)
        (mul_nonneg (by positivity) hV_nonneg)
    · refine mul_nonneg hKinner_nonneg ?_
      refine add_nonneg ?_ ?_
      · exact mul_nonneg (by norm_num)
          (mul_nonneg (by positivity) (sq_nonneg _))
      · exact mul_nonneg (by norm_num)
          (mul_nonneg hKouter_nonneg
            (mul_nonneg (by positivity) (sq_nonneg _)))
  dsimp [originCubeParentReducedSolverEnergyInsideExact, Q, Qp, C, V, B, Kinner, Kouter]
  exact mul_nonneg (by norm_num) hmain_nonneg

noncomputable def originCubeParentReducedSolverEnergyConstantExact
    (d : ℕ) (m : ℤ) : ℝ :=
  (originCubeParentReducedSolverEnergyInsideExact d m) ^ (1 / (2 : ℝ))

theorem originCubeParentReducedSolverEnergyConstantExact_nonneg
    (d : ℕ) (m : ℤ) :
    0 ≤ originCubeParentReducedSolverEnergyConstantExact d m := by
  unfold originCubeParentReducedSolverEnergyConstantExact
  exact Real.rpow_nonneg
    (originCubeParentReducedSolverEnergyInsideExact_nonneg d m) _

private theorem originCubeParentReducedSolverEnergyInsideExact_eq_volume_mul_unit
    (d : ℕ) (m : ℤ) :
    originCubeParentReducedSolverEnergyInsideExact d m =
      cubeVolume (originCube d m) *
        originCubeParentReducedSolverEnergyInsideExact d 0 := by
  let s : ℝ := (3 : ℝ) ^ m
  let C₀ : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).constant
  let κ : ℝ := quantitativeCubeCutoffGradientConst d
  have hs_pos : 0 < s := by
    dsimp [s]
    exact zpow_pos (by norm_num : (0 : ℝ) < 3) m
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hV_m : cubeVolume (originCube d m) = s ^ d := by
    simp [cubeVolume_eq_scaleFactor_pow, s]
  have hV_0 : cubeVolume (originCube d 0) = 1 := by
    simp [cubeVolume_eq_scaleFactor_pow]
  have hC_m :
      cubeMeanZeroH1CoerciveConstant (originCube d m) = s * C₀ := by
    simp [cubeMeanZeroH1CoerciveConstant_eq_scale_mul_unit, C₀, s]
  have hC_0 :
      cubeMeanZeroH1CoerciveConstant (originCube d 0) = C₀ := by
    simp [cubeMeanZeroH1CoerciveConstant_eq_scale_mul_unit, C₀]
  have hR_m : cubeRadius (originCube d (m + 1)) = (3 / 2 : ℝ) * s := by
    dsimp [cubeRadius, cubeScaleFactor, originCube, s]
    rw [zpow_add₀]
    · norm_num
      ring
    · norm_num
  have hR_0 : cubeRadius (originCube d (1 : ℤ)) = (3 / 2 : ℝ) := by
    norm_num [cubeRadius, cubeScaleFactor, originCube]
  have hBsq : ((s ^ d) ^ (1 / 2 : ℝ)) ^ 2 = s ^ d := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (by positivity)
  dsimp [originCubeParentReducedSolverEnergyInsideExact]
  rw [hV_m, hV_0, hC_m, hC_0, hR_m, hR_0]
  norm_num
  ring_nf
  rw [hBsq]
  field_simp [hs_ne]

theorem originCubeParentReducedSolverEnergyConstantExact_volume_cancel
    (d : ℕ) (m : ℤ) :
    ((cubeVolume (originCube d m))⁻¹) ^ (1 / 2 : ℝ) *
        originCubeParentReducedSolverEnergyConstantExact d m =
      originCubeParentReducedSolverEnergyConstantExact d 0 := by
  let V : ℝ := cubeVolume (originCube d m)
  let A : ℝ := originCubeParentReducedSolverEnergyInsideExact d 0
  have hV_pos : 0 < V := by
    dsimp [V]
    exact cubeVolume_pos (originCube d m)
  have hV_nonneg : 0 ≤ V := le_of_lt hV_pos
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact originCubeParentReducedSolverEnergyInsideExact_nonneg d 0
  have hinside :
      originCubeParentReducedSolverEnergyInsideExact d m = V * A := by
    dsimp [V, A]
    exact originCubeParentReducedSolverEnergyInsideExact_eq_volume_mul_unit d m
  have hV_cancel :
      (V⁻¹) ^ (1 / 2 : ℝ) * (V ^ (1 / 2 : ℝ)) = 1 := by
    rw [Real.inv_rpow hV_nonneg (1 / 2 : ℝ)]
    exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hV_pos _).ne'
  calc
    ((cubeVolume (originCube d m))⁻¹) ^ (1 / 2 : ℝ) *
        originCubeParentReducedSolverEnergyConstantExact d m
        = (V⁻¹) ^ (1 / 2 : ℝ) *
            ((V * A) ^ (1 / 2 : ℝ)) := by
          simp [originCubeParentReducedSolverEnergyConstantExact, V, A, hinside]
    _ = (V⁻¹) ^ (1 / 2 : ℝ) *
          (V ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)) := by
          rw [Real.mul_rpow hV_nonneg hA_nonneg]
    _ = A ^ (1 / 2 : ℝ) := by
          rw [← mul_assoc, hV_cancel, one_mul]
    _ = originCubeParentReducedSolverEnergyConstantExact d 0 := by
          simp [originCubeParentReducedSolverEnergyConstantExact, A]

theorem originCubeParentReducedSolverEnergyBoundExact_eq_constant_mul_cubeLpNorm
    (d : ℕ) (m : ℤ) (F : Vec d → ℝ) (i : Fin d) :
    originCubeParentReducedSolverEnergyBoundExact d m F i =
      originCubeParentReducedSolverEnergyConstantExact d m *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let V : ℝ := cubeVolume Q
  let B : ℝ := V ^ (1 / 2 : ℝ)
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let Kinner : ℝ :=
    (3 : ℝ) *
      ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)
  let Kouter : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F
  have hfactor :
      (4 : ℝ) *
        ((2 : ℝ) * ((3 : ℝ) ^ d * (V * L ^ (2 : ℝ))) +
          Kinner *
            ((2 : ℝ) * ((3 : ℝ) ^ d * (C * (B * L)) ^ 2) +
              (2 : ℝ) *
                (Kouter * ((3 : ℝ) ^ d * (C * (C * (B * L))) ^ 2)))) =
        originCubeParentReducedSolverEnergyInsideExact d m * L ^ 2 := by
    dsimp [originCubeParentReducedSolverEnergyInsideExact, Q, Qp, C, V, B, L, Kinner, Kouter]
    rw [Real.rpow_two]
    ring
  calc
    originCubeParentReducedSolverEnergyBoundExact d m F i
        = ((originCubeParentReducedSolverEnergyInsideExact d m) * L ^ 2) ^
            (1 / (2 : ℝ)) := by
          dsimp [originCubeParentReducedSolverEnergyBoundExact, Q, Qp, C, V, L, B,
            Kinner, Kouter]
          rw [hfactor]
    _ = (originCubeParentReducedSolverEnergyInsideExact d m) ^ (1 / (2 : ℝ)) *
          (L ^ 2) ^ (1 / (2 : ℝ)) := by
          rw [Real.mul_rpow
            (originCubeParentReducedSolverEnergyInsideExact_nonneg d m) (sq_nonneg L)]
    _ = originCubeParentReducedSolverEnergyConstantExact d m * L := by
          unfold originCubeParentReducedSolverEnergyConstantExact
          rw [show (L ^ 2) ^ (1 / (2 : ℝ)) = L by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hL_nonneg]]

end MeanZeroNeumannPoissonSolution

end

end Homogenization
