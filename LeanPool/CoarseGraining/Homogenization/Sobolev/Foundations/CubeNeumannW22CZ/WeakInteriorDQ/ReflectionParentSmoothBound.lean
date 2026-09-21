/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentInterior
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothTestBoundEstimate

/-! # Reflection Parent Smooth Bound -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {m : ℤ} {F : Vec d → ℝ}

/-- Original-cube energy bound obtained after reading the fixed-radii
reflected-parent reduced smooth-test constant through the all-face reflection
identities. -/
noncomputable def originCubeParentReducedOriginalEnergyBound
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F) (_i : Fin d) : ℝ :=
  ((4 : ℝ) *
    ((2 : ℝ) *
        ((3 : ℝ) ^ d *
          ∫ y in openCubeSet (originCube d m), F y ^ 2 ∂MeasureTheory.volume) +
      ((3 : ℝ) *
        ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            (((1 / 2 : ℝ) - (1 / 3 : ℝ)) *
              cubeRadius (originCube d (m + 1)))) ^ 2)) *
        ((2 : ℝ) *
            ((3 : ℝ) ^ d *
              ∫ y in openCubeSet (originCube d m),
                vecDot (W.w.toH1Function.grad y) (W.w.toH1Function.grad y)
                ∂MeasureTheory.volume) +
          (2 : ℝ) *
            (((d : ℝ) *
              (quantitativeCubeCutoffGradientConst d /
                (((7 / 8 : ℝ) - (3 / 4 : ℝ)) *
                  cubeRadius (originCube d (m + 1)))) ^ 2) *
              ((3 : ℝ) ^ d *
                ∫ y in openCubeSet (originCube d m),
                W.w.toH1Function.toFun y ^ 2 ∂MeasureTheory.volume))))) ^
    (1 / (2 : ℝ))

/-- The same reflected-parent reduced energy bound, but with the original-cube
forcing, gradient, and value integrals rewritten as the normalized forcing
`L²` norm and the solver's `L²` realizations. -/
noncomputable def originCubeParentReducedNormEnergyBound
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F) (_i : Fin d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  ((4 : ℝ) *
    ((2 : ℝ) *
        ((3 : ℝ) ^ d *
          (cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ (2 : ℝ))) +
      ((3 : ℝ) *
        ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)) *
        ((2 : ℝ) *
            ((3 : ℝ) ^ d * ‖W.w.toH1Function.gradToHilbertVectorL2‖ ^ 2) +
          (2 : ℝ) *
            (((d : ℝ) *
              (quantitativeCubeCutoffGradientConst d /
                (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2) *
              ((3 : ℝ) ^ d * ‖W.w.toH1Function.toScalarL2‖ ^ 2))))) ^
    (1 / (2 : ℝ))

/-- The solver gradient `L²` realization on the original cube is controlled by
the normalized forcing `L²` norm. -/
theorem norm_gradToHilbertVectorL2_le_solverCubeLpNorm
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ‖W.w.toH1Function.gradToHilbertVectorL2‖ ≤
      cubeMeanZeroH1CoerciveConstant (originCube d m) *
        ((cubeVolume (originCube d m) + 1) *
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
    _ ≤ cubeMeanZeroH1CoerciveConstant Q *
          ((cubeVolume Q + 1) * cubeLpNorm Q (2 : ℝ≥0∞) F) := by
          exact mul_le_mul_of_nonneg_left
            (norm_toScalarL2_openCubeSet_le_volume_add_one_mul_cubeLpNorm_two Q hF)
            (cubeMeanZeroH1CoerciveConstant_nonneg Q)

/-- The solver value `L²` realization on the original cube is controlled by
the normalized forcing `L²` norm, using the cube coercive estimate once more
after the gradient estimate. -/
theorem norm_toScalarL2_le_solverCubeLpNorm
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ‖W.w.toH1Function.toScalarL2‖ ≤
      cubeMeanZeroH1CoerciveConstant (originCube d m) *
        (cubeMeanZeroH1CoerciveConstant (originCube d m) *
          ((cubeVolume (originCube d m) + 1) *
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
            ((cubeVolume Q + 1) * cubeLpNorm Q (2 : ℝ≥0∞) F)) := by
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [Q] using!
                norm_gradToHilbertVectorL2_le_solverCubeLpNorm W hF)
            (cubeMeanZeroH1CoerciveConstant_nonneg Q)

/-- A fully forcing-facing version of the reflected-parent reduced energy
bound. The remaining constants are explicit cube geometry and the coercive
constant already used by the Neumann solver. -/
noncomputable def originCubeParentReducedSolverEnergyBound
    (d : ℕ) (m : ℤ) (F : Vec d → ℝ) (_i : Fin d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let B : ℝ := (cubeVolume Q + 1) * L
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

/-- The reflected-parent reduced norm energy is bounded by the explicit
forcing-facing solver energy expression. -/
theorem originCubeParentReducedNormEnergyBound_le_solverEnergyBound
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    (i : Fin d) :
    originCubeParentReducedNormEnergyBound W i ≤
      originCubeParentReducedSolverEnergyBound d m F i := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let B : ℝ := (cubeVolume Q + 1) * L
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
          norm_gradToHilbertVectorL2_le_solverCubeLpNorm W hF)
      2
  have hvalue_sq :
      ‖W.w.toH1Function.toScalarL2‖ ^ 2 ≤ (C * (C * B)) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _)
      (by
        simpa [Q, C, L, B] using
          norm_toScalarL2_le_solverCubeLpNorm W hF)
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
    originCubeParentReducedSolverEnergyBound, Q, Qp, C, L, B, Kinner,
    Kouter, A, Benergy] using
    Real.rpow_le_rpow h4A_nonneg h4AB
      (by norm_num : 0 ≤ (1 / (2 : ℝ)))

/-- The raw original-cube reflected-parent energy expression is exactly the
same as its norm-realized form. -/
theorem originCubeParentReducedOriginalEnergyBound_eq_normEnergyBound
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    (i : Fin d) :
    originCubeParentReducedOriginalEnergyBound W i =
      originCubeParentReducedNormEnergyBound W i := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  have hforce :
      ∫ y in openCubeSet Q, F y ^ 2 ∂MeasureTheory.volume =
        cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ (2 : ℝ) := by
    simpa [Q, pow_two] using
      setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow Q F hF
  have hgrad :
      ∫ y in openCubeSet Q,
          vecDot (W.w.toH1Function.grad y) (W.w.toH1Function.grad y)
          ∂MeasureTheory.volume =
        ‖W.w.toH1Function.gradToHilbertVectorL2‖ ^ 2 := by
    have hinner :
        ∫ y in openCubeSet Q,
            vecDot (W.w.toH1Function.grad y) (W.w.toH1Function.grad y)
            ∂MeasureTheory.volume =
          inner ℝ W.w.toH1Function.gradToHilbertVectorL2
            W.w.toH1Function.gradToHilbertVectorL2 := by
      simpa [H1Function.gradToHilbertVectorL2] using
        (inner_toHilbertVectorL2OfVecField_eq_integral
          (U := openCubeSet Q)
          W.w.toH1Function.grad_memVectorL2
          W.w.toH1Function.grad_memVectorL2).symm
    rw [hinner]
    exact real_inner_self_eq_norm_sq W.w.toH1Function.gradToHilbertVectorL2
  have hvalue :
      ∫ y in openCubeSet Q, W.w.toH1Function.toFun y ^ 2
          ∂MeasureTheory.volume =
        ‖W.w.toH1Function.toScalarL2‖ ^ 2 := by
    simpa [H1Function.toScalarL2, Homogenization.toScalarL2] using
      (toReal_eLpNorm_two_sq_eq_integral_sq W.w.toH1Function.memL2).symm
  simp [originCubeParentReducedOriginalEnergyBound,
    originCubeParentReducedNormEnergyBound, Q, hforce, hgrad, hvalue]

/-- A fixed-radii reduced smooth-test constant on the reflected parent is
bounded by the corresponding original-cube energy expression. -/
theorem openCubeInnerQuotientHessianSmoothTestReducedBound_le_originCubeParentReducedOriginalEnergyBound
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    {uP : H1Function (openCubeSet (originCube d (m + 1)))}
    (huP_toFun :
      uP.toFun =
        cubeCoordinateFoldReflectedScalar (originCube d m)
          W.w.toH1Function.toFun)
    (huP_grad :
      uP.grad =
        cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => W.w.toH1Function.grad y))
    (i : Fin d) :
    @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
        d (originCube d (m + 1)) uP
        (cubeCoordinateFoldReflectedScalar (originCube d m) F)
        i (1 / 3 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
        (originCubeParentThreeQuarterSevenEighthCutoff d m) ≤
      originCubeParentReducedOriginalEnergyBound W i := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let fP : Vec d → ℝ := cubeCoordinateFoldReflectedScalar Q F
  let G : Vec d → Vec d := fun y => W.w.toH1Function.grad y
  let GP : Vec d → Vec d := cubeCoordinateFoldReflectedVectorField Q G
  let uPfun : Vec d → ℝ :=
    cubeCoordinateFoldReflectedScalar Q W.w.toH1Function.toFun
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
    (2 : ℝ) * ∫ x in openCubeSet Qp, fP x ^ 2 ∂MeasureTheory.volume +
      Kinner *
        ((2 : ℝ) * ∫ x in openCubeSet Qp, (uP.grad x i) ^ 2
            ∂MeasureTheory.volume +
          (2 : ℝ) *
            (Kouter *
              ∫ x in openCubeSet Qp, uP.toFun x ^ 2 ∂MeasureTheory.volume))
  let B : ℝ :=
    (2 : ℝ) *
        ((3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, F y ^ 2 ∂MeasureTheory.volume) +
      Kinner *
        ((2 : ℝ) *
            ((3 : ℝ) ^ d *
              ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂MeasureTheory.volume) +
          (2 : ℝ) *
            (Kouter *
              ((3 : ℝ) ^ d *
                ∫ y in openCubeSet Q, W.w.toH1Function.toFun y ^ 2
                  ∂MeasureTheory.volume)))
  have hFopen : MemScalarL2 (openCubeSet Q) F := by
    simpa [Q, MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure (originCube d m) hF
  have hforce_eq :
      ∫ x in openCubeSet Qp, fP x ^ 2 ∂MeasureTheory.volume =
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, F y ^ 2 ∂MeasureTheory.volume := by
    simpa [Q, Qp, fP, pow_two] using
      setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sq_of_memScalarL2_three_pow
        (m := m) hFopen
  have hvalue_eq :
      ∫ x in openCubeSet Qp, uP.toFun x ^ 2 ∂MeasureTheory.volume =
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, W.w.toH1Function.toFun y ^ 2
            ∂MeasureTheory.volume := by
    have hW : MemScalarL2 (openCubeSet Q) W.w.toH1Function.toFun := by
      simpa [Q, MemScalarL2, volumeMeasureOn] using W.w.toH1Function.memL2
    calc
      ∫ x in openCubeSet Qp, uP.toFun x ^ 2 ∂MeasureTheory.volume =
          ∫ x in openCubeSet Qp, uPfun x ^ 2 ∂MeasureTheory.volume := by
            rw [huP_toFun]
      _ =
          (3 : ℝ) ^ d *
            ∫ y in openCubeSet Q, W.w.toH1Function.toFun y ^ 2
              ∂MeasureTheory.volume := by
            simpa [Q, Qp, uPfun, pow_two] using
              setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sq_of_memScalarL2_three_pow
                (m := m) hW
  have hgrad_coord_le :
      ∫ x in openCubeSet Qp, (uP.grad x i) ^ 2 ∂MeasureTheory.volume ≤
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂MeasureTheory.volume := by
    have hcoord :
        ∫ x in openCubeSet Qp, (uP.grad x i) ^ 2 ∂MeasureTheory.volume ≤
          ∫ x in openCubeSet Qp, vecNormSq (uP.grad x) ∂MeasureTheory.volume := by
      simpa [Real.rpow_two, Real.norm_eq_abs, sq_abs] using
        WeakPoissonEquationOn.integral_coord_norm_rpow_two_le_integral_vecNormSq_of_memVectorL2
          (U := openCubeSet Qp) uP.grad_memVectorL2 i
    have hG : MemVectorL2 (openCubeSet Q) G := by
      simpa [Q, G, MemVectorL2, volumeMeasureOn] using
        W.w.toH1Function.grad_memVectorL2
    have hvec_eq :
        ∫ x in openCubeSet Qp, vecNormSq (uP.grad x) ∂MeasureTheory.volume =
          (3 : ℝ) ^ d *
            ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂MeasureTheory.volume := by
      calc
        ∫ x in openCubeSet Qp, vecNormSq (uP.grad x) ∂MeasureTheory.volume =
            ∫ x in openCubeSet Qp, vecDot (GP x) (GP x)
              ∂MeasureTheory.volume := by
              rw [huP_grad]
              rfl
        _ =
            (3 : ℝ) ^ d *
              ∫ y in openCubeSet Q, vecDot (G y) (G y)
                ∂MeasureTheory.volume := by
              simpa [Q, Qp, G, GP] using
                setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2_three_pow
                  (m := m) hG
    exact hcoord.trans_eq hvec_eq
  have hlower :
      (2 : ℝ) * ∫ x in openCubeSet Qp, (uP.grad x i) ^ 2
          ∂MeasureTheory.volume +
        (2 : ℝ) *
          (Kouter *
            ∫ x in openCubeSet Qp, uP.toFun x ^ 2 ∂MeasureTheory.volume) ≤
      (2 : ℝ) *
          ((3 : ℝ) ^ d *
            ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂MeasureTheory.volume) +
        (2 : ℝ) *
          (Kouter *
            ((3 : ℝ) ^ d *
              ∫ y in openCubeSet Q, W.w.toH1Function.toFun y ^ 2
                ∂MeasureTheory.volume)) := by
    rw [hvalue_eq]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hgrad_coord_le (by norm_num))
      (le_refl _)
  have hKinner_nonneg : 0 ≤ Kinner := by
    dsimp [Kinner]
    positivity
  have hAB : A ≤ B := by
    dsimp [A, B]
    rw [hforce_eq]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hlower hKinner_nonneg) _
  have h4AB : (4 : ℝ) * A ≤ (4 : ℝ) * B :=
    mul_le_mul_of_nonneg_left hAB (by norm_num)
  have h4A_nonneg : 0 ≤ (4 : ℝ) * A := by
    dsimp [A, Kinner, Kouter]
    positivity
  simpa [WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound,
    originCubeParentReducedOriginalEnergyBound, Q, Qp, fP, G, GP, uPfun,
    Kinner, Kouter, A, B] using
    Real.rpow_le_rpow h4A_nonneg h4AB (by norm_num : 0 ≤ (1 / (2 : ℝ)))

/-- The fixed-radii reflected-parent Hessian estimate with the raw smooth-test
constant replaced by the reduced unweighted `H¹` bound. -/
theorem exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_reducedBound
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
                @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
                  d (originCube d (m + 1)) uP
                  (cubeCoordinateFoldReflectedScalar (originCube d m) F)
                  i (1 / 3 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
                  (originCubeParentThreeQuarterSevenEighthCutoff d m) := by
  rcases
    W.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le
      hmean hF with
    ⟨uP, huP_toFun, huP_grad, H, hH⟩
  refine ⟨uP, huP_toFun, huP_grad, H, hH.trans ?_⟩
  exact Finset.sum_le_sum fun i _hi =>
    Finset.sum_le_sum fun _j _hj =>
      WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound_le_reducedBound
        (Q := originCube d (m + 1)) uP
        (cubeCoordinateFoldReflectedScalar (originCube d m) F) i
        (ρ₁ := (1 / 3 : ℝ)) (ρ₂ := (1 / 2 : ℝ))
        (σ₁ := (3 / 4 : ℝ)) (σ₂ := (7 / 8 : ℝ))
        (originCubeParentThreeQuarterSevenEighthCutoff d m)

/-- The fixed-radii reflected-parent Hessian estimate, with the right-hand
side expressed entirely in original-cube energy terms. -/
theorem exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_originalEnergyBound
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
                originCubeParentReducedOriginalEnergyBound W i := by
  rcases
    W.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_reducedBound
      hmean hF with
    ⟨uP, huP_toFun, huP_grad, H, hH⟩
  refine ⟨uP, huP_toFun, huP_grad, H, hH.trans ?_⟩
  exact Finset.sum_le_sum fun i _hi =>
    Finset.sum_le_sum fun _j _hj =>
      openCubeInnerQuotientHessianSmoothTestReducedBound_le_originCubeParentReducedOriginalEnergyBound
        W hF huP_toFun huP_grad i

/-- The fixed-radii reflected-parent Hessian estimate with the right-hand side
expressed through solver `L²` norms. -/
theorem exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_normEnergyBound
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
                originCubeParentReducedNormEnergyBound W i := by
  rcases
    W.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_originalEnergyBound
      hmean hF with
    ⟨uP, huP_toFun, huP_grad, H, hH⟩
  refine ⟨uP, huP_toFun, huP_grad, H, hH.trans ?_⟩
  exact Finset.sum_le_sum fun i _hi =>
    Finset.sum_le_sum fun _j _hj =>
      le_of_eq (originCubeParentReducedOriginalEnergyBound_eq_normEnergyBound W hF i)

/-- The fixed-radii reflected-parent Hessian estimate with the right-hand side
controlled by the explicit forcing-facing solver energy expression. -/
theorem exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_solverEnergyBound
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
                originCubeParentReducedSolverEnergyBound d m F i := by
  rcases
    W.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_normEnergyBound
      hmean hF with
    ⟨uP, huP_toFun, huP_grad, H, hH⟩
  refine ⟨uP, huP_toFun, huP_grad, H, hH.trans ?_⟩
  exact Finset.sum_le_sum fun i _hi =>
    Finset.sum_le_sum fun _j _hj =>
      originCubeParentReducedNormEnergyBound_le_solverEnergyBound W hF i

end MeanZeroNeumannPoissonSolution

end

end Homogenization
