/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.EnergyBound
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCoerciveH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareZeroTrace

/-! # Solver Energy -/

namespace Homogenization

open scoped ENNReal Pointwise

noncomputable section

namespace CubeDirichletWeakPoissonProblem

variable {d : ℕ} {m : ℤ} {u : H10Function (openCubeSet (originCube d m))}
  {F : Vec d → ℝ}

private theorem le_of_sq_le_mul_self_right {G A : ℝ}
    (hG : 0 ≤ G) (hA : 0 ≤ A) (h : G ^ 2 ≤ A * G) :
    G ≤ A := by
  by_cases hzero : G = 0
  · rw [hzero]
    exact hA
  · have hGpos : 0 < G := lt_of_le_of_ne hG (Ne.symm hzero)
    have hmul : G * G ≤ A * G := by
      simpa [pow_two] using h
    rw [mul_comm A G] at hmul
    exact (mul_le_mul_iff_right₀ hGpos).mp hmul

/-- A chosen zero-trace Poincare constant on the unit centered origin cube. -/
noncomputable def originCubeUnitZeroTraceH1CoerciveConstant
    (d : ℕ) [NeZero d] : ℝ :=
  Classical.choose
    (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d 0))
      (isOpenBoundedConvexDomain_openCubeSet (originCube d 0)))

theorem originCubeUnitZeroTraceH1CoerciveConstant_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤ originCubeUnitZeroTraceH1CoerciveConstant d := by
  exact
    (Classical.choose_spec
      (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
        (U := openCubeSet (originCube d 0))
        (isOpenBoundedConvexDomain_openCubeSet (originCube d 0)))).1

theorem originCubeUnitZeroTraceH1CoerciveConstant_bound
    [NeZero d] (u : H10Function (openCubeSet (originCube d 0))) :
    ‖u.toH1Function.toScalarL2‖ ≤
      originCubeUnitZeroTraceH1CoerciveConstant d *
        u.toH1Function.gradientCoordL2NormSum := by
  exact
    (Classical.choose_spec
      (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
        (U := openCubeSet (originCube d 0))
        (isOpenBoundedConvexDomain_openCubeSet (originCube d 0)))).2 u

/-- The scale-sharp zero-trace Poincare constant on centered origin cubes,
obtained by dilating the unit centered cube estimate. -/
noncomputable def originCubeZeroTraceH1CoerciveConstant
    (d : ℕ) [NeZero d] (m : ℤ) : ℝ :=
  cubeScaleFactor (originCube d m) *
    originCubeUnitZeroTraceH1CoerciveConstant d

theorem originCubeZeroTraceH1CoerciveConstant_nonneg
    (d : ℕ) [NeZero d] (m : ℤ) :
    0 ≤ originCubeZeroTraceH1CoerciveConstant d m := by
  exact mul_nonneg
    (le_of_lt (by
      dsimp [cubeScaleFactor, originCube]
      positivity))
    (originCubeUnitZeroTraceH1CoerciveConstant_nonneg d)

private theorem originCubeZeroTraceH1CoerciveConstant_bound_smul_unit
    [NeZero d] (m : ℤ) :
    ∀ u : H10Function
        (cubeScaleFactor (originCube d m) • openCubeSet (originCube d 0)),
      ‖u.toH1Function.toScalarL2‖ ≤
        originCubeZeroTraceH1CoerciveConstant d m *
          u.toH1Function.gradientCoordL2NormSum := by
  let s : ℝ := cubeScaleFactor (originCube d m)
  let U0 : Set (Vec d) := openCubeSet (originCube d 0)
  have hs : 0 < s := by
    dsimp [s, cubeScaleFactor, originCube]
    positivity
  intro u
  let v : H10Function U0 := u.unscale hs
  have hunit :
      ‖v.toH1Function.toScalarL2‖ ≤
        originCubeUnitZeroTraceH1CoerciveConstant d *
          v.toH1Function.gradientCoordL2NormSum :=
    originCubeUnitZeroTraceH1CoerciveConstant_bound v
  have hvalue :
      ‖v.toH1Function.toScalarL2‖ =
        dilationL2Factor d s * ‖u.toH1Function.toScalarL2‖ := by
    simpa [v, U0] using!
      H1Function.norm_toScalarL2_unscale_eq
        (d := d) (U := U0) hs u.toH1Function
  have hgrad :
      v.toH1Function.gradientCoordL2NormSum =
        s * dilationL2Factor d s *
          u.toH1Function.gradientCoordL2NormSum := by
    simpa [v, U0] using!
      H1Function.gradientCoordL2NormSum_unscale_eq
        (d := d) (U := U0) hs u.toH1Function
  have hscaled :
      dilationL2Factor d s * ‖u.toH1Function.toScalarL2‖ ≤
        originCubeUnitZeroTraceH1CoerciveConstant d *
          (s * dilationL2Factor d s *
            u.toH1Function.gradientCoordL2NormSum) := by
    simpa [hvalue, hgrad] using hunit
  have hf_pos : 0 < dilationL2Factor d s :=
    dilationL2Factor_pos (d := d) hs
  have hscaled' :
      dilationL2Factor d s * ‖u.toH1Function.toScalarL2‖ ≤
        dilationL2Factor d s *
          ((s * originCubeUnitZeroTraceH1CoerciveConstant d) *
            u.toH1Function.gradientCoordL2NormSum) := by
    calc
      dilationL2Factor d s * ‖u.toH1Function.toScalarL2‖
          ≤ originCubeUnitZeroTraceH1CoerciveConstant d *
              (s * dilationL2Factor d s *
                u.toH1Function.gradientCoordL2NormSum) := hscaled
      _ =
          dilationL2Factor d s *
            ((s * originCubeUnitZeroTraceH1CoerciveConstant d) *
              u.toH1Function.gradientCoordL2NormSum) := by
            ring
  have hscaled'' :
      dilationL2Factor d s * ‖u.toH1Function.toScalarL2‖ ≤
        dilationL2Factor d s *
          (originCubeZeroTraceH1CoerciveConstant d m *
            u.toH1Function.gradientCoordL2NormSum) := by
    simpa [originCubeZeroTraceH1CoerciveConstant, s, mul_assoc] using hscaled'
  exact (mul_le_mul_iff_right₀ hf_pos).mp hscaled''

theorem originCubeZeroTraceH1CoerciveConstant_bound
    [NeZero d] :
    ∀ u : H10Function (openCubeSet (originCube d m)),
      ‖u.toH1Function.toScalarL2‖ ≤
        originCubeZeroTraceH1CoerciveConstant d m *
          u.toH1Function.gradientCoordL2NormSum := by
  let s : ℝ := cubeScaleFactor (originCube d m)
  let U0 : Set (Vec d) := openCubeSet (originCube d 0)
  have hU : openCubeSet (originCube d m) = s • U0 := by
    simpa [s, U0] using openCubeSet_originCube_eq_smul_unit d m
  rw [hU]
  exact originCubeZeroTraceH1CoerciveConstant_bound_smul_unit (d := d) m

/-- The zero-trace Poincare constant converted to the Hilbert-vector gradient
norm used by the interior estimate. -/
noncomputable def originCubeZeroTraceH1HilbertCoerciveConstant
    (d : ℕ) [NeZero d] (m : ℤ) : ℝ :=
  originCubeZeroTraceH1CoerciveConstant d m * d

theorem originCubeZeroTraceH1HilbertCoerciveConstant_nonneg
    (d : ℕ) [NeZero d] (m : ℤ) :
    0 ≤ originCubeZeroTraceH1HilbertCoerciveConstant d m := by
  exact mul_nonneg
    (originCubeZeroTraceH1CoerciveConstant_nonneg d m)
    (Nat.cast_nonneg d)

theorem originCubeZeroTraceH1HilbertCoerciveConstant_bound
    [NeZero d] (u : H10Function (openCubeSet (originCube d m))) :
    ‖u.toH1Function.toScalarL2‖ ≤
      originCubeZeroTraceH1HilbertCoerciveConstant d m *
        ‖u.toH1Function.gradToHilbertVectorL2‖ := by
  let C₀ : ℝ := originCubeZeroTraceH1CoerciveConstant d m
  have hC₀_nonneg : 0 ≤ C₀ := by
    dsimp [C₀]
    exact originCubeZeroTraceH1CoerciveConstant_nonneg d m
  have hvec :
      u.toH1Function.gradientCoordL2NormSum ≤
        d * ‖u.toH1Function.gradToHilbertVectorL2‖ := by
    calc
      u.toH1Function.gradientCoordL2NormSum
          ≤ d * ‖u.toH1Function.gradToVectorL2‖ :=
            u.toH1Function.gradientCoordL2NormSum_le
      _ ≤ d * ‖u.toH1Function.gradToHilbertVectorL2‖ := by
            exact mul_le_mul_of_nonneg_left
              u.toH1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2
              (Nat.cast_nonneg d)
  calc
    ‖u.toH1Function.toScalarL2‖
        ≤ C₀ * u.toH1Function.gradientCoordL2NormSum := by
          simpa [C₀] using originCubeZeroTraceH1CoerciveConstant_bound u
    _ ≤ C₀ * (d * ‖u.toH1Function.gradToHilbertVectorL2‖) := by
          exact mul_le_mul_of_nonneg_left hvec hC₀_nonneg
    _ =
        originCubeZeroTraceH1HilbertCoerciveConstant d m *
          ‖u.toH1Function.gradToHilbertVectorL2‖ := by
          simp [originCubeZeroTraceH1HilbertCoerciveConstant, C₀]
          ring

/-- Testing the Dirichlet weak equation with the solution and using zero-trace
Poincare controls the gradient by the normalized forcing norm. -/
theorem norm_gradToHilbertVectorL2_le_solverCubeLpNorm_exact
    [NeZero d]
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ‖u.toH1Function.gradToHilbertVectorL2‖ ≤
      originCubeZeroTraceH1HilbertCoerciveConstant d m *
        ((cubeVolume (originCube d m)) ^ (1 / 2 : ℝ) *
          cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F) := by
  let Q : TriadicCube d := originCube d m
  let Gnorm : ℝ := ‖u.toH1Function.gradToHilbertVectorL2‖
  let C : ℝ := originCubeZeroTraceH1HilbertCoerciveConstant d m
  have hFopen : MemScalarL2 (openCubeSet Q) F := by
    simpa [Q, MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure (originCube d m) hF
  have hgrad_integral :
      ∫ y in openCubeSet Q,
          vecDot (u.toH1Function.grad y) (u.toH1Function.grad y)
          ∂MeasureTheory.volume =
        Gnorm ^ 2 := by
    have hinner :
        ∫ y in openCubeSet Q,
            vecDot (u.toH1Function.grad y) (u.toH1Function.grad y)
            ∂MeasureTheory.volume =
          inner ℝ u.toH1Function.gradToHilbertVectorL2
            u.toH1Function.gradToHilbertVectorL2 := by
      simpa [H1Function.gradToHilbertVectorL2, Gnorm] using
        (inner_toHilbertVectorL2OfVecField_eq_integral
          (U := openCubeSet Q)
          u.toH1Function.grad_memVectorL2
          u.toH1Function.grad_memVectorL2).symm
    rw [hinner]
    exact real_inner_self_eq_norm_sq u.toH1Function.gradToHilbertVectorL2
  have hweak_u :
      ∫ y in openCubeSet Q,
          vecDot (u.toH1Function.grad y) (u.toH1Function.grad y)
          ∂MeasureTheory.volume =
        ∫ y in openCubeSet Q, F y * u.toH1Function y
          ∂MeasureTheory.volume := by
    simpa [Q] using hweak u
  have hGsq_rhs :
      Gnorm ^ 2 =
        ∫ y in openCubeSet Q, F y * u.toH1Function y
          ∂MeasureTheory.volume := by
    rw [← hgrad_integral]
    exact hweak_u
  have hpair_abs :
      |∫ y in openCubeSet Q, F y * u.toH1Function y
          ∂MeasureTheory.volume| ≤
        ‖toScalarL2 hFopen‖ * ‖u.toH1Function.toScalarL2‖ := by
    have hinner := inner_toScalarL2_eq_integral_mul
      (U := openCubeSet Q) hFopen u.toH1Function.memL2
    rw [← hinner]
    simpa [H1Function.toScalarL2] using
      abs_real_inner_le_norm (toScalarL2 hFopen) u.toH1Function.toScalarL2
  have hvalue :
      ‖u.toH1Function.toScalarL2‖ ≤ C * Gnorm := by
    simpa [C, Gnorm] using
      originCubeZeroTraceH1HilbertCoerciveConstant_bound u
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact originCubeZeroTraceH1HilbertCoerciveConstant_nonneg d m
  have hsq :
      Gnorm ^ 2 ≤ (‖toScalarL2 hFopen‖ * C) * Gnorm := by
    calc
      Gnorm ^ 2
          ≤ |∫ y in openCubeSet Q, F y * u.toH1Function y
              ∂MeasureTheory.volume| := by
            rw [hGsq_rhs]
            exact le_abs_self _
      _ ≤ ‖toScalarL2 hFopen‖ * ‖u.toH1Function.toScalarL2‖ := hpair_abs
      _ ≤ ‖toScalarL2 hFopen‖ * (C * Gnorm) := by
            exact mul_le_mul_of_nonneg_left hvalue (norm_nonneg _)
      _ = (‖toScalarL2 hFopen‖ * C) * Gnorm := by ring
  have hG_le :
      Gnorm ≤ ‖toScalarL2 hFopen‖ * C := by
    exact le_of_sq_le_mul_self_right
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) hC_nonneg) hsq
  have hFnorm :
      ‖toScalarL2 hFopen‖ =
        (cubeVolume Q) ^ (1 / 2 : ℝ) *
          cubeLpNorm Q (2 : ℝ≥0∞) F := by
    simpa [Q] using
      norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two Q hF
  calc
    ‖u.toH1Function.gradToHilbertVectorL2‖ = Gnorm := rfl
    _ ≤ ‖toScalarL2 hFopen‖ * C := hG_le
    _ =
        C * ((cubeVolume Q) ^ (1 / 2 : ℝ) *
          cubeLpNorm Q (2 : ℝ≥0∞) F) := by
          rw [hFnorm]
          ring
    _ =
        originCubeZeroTraceH1HilbertCoerciveConstant d m *
          ((cubeVolume (originCube d m)) ^ (1 / 2 : ℝ) *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F) := by
          simp [Q, C]

/-- The solution value is controlled by the forcing norm after one additional
zero-trace Poincare step. -/
theorem norm_toScalarL2_le_solverCubeLpNorm_exact
    [NeZero d]
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ‖u.toH1Function.toScalarL2‖ ≤
      originCubeZeroTraceH1HilbertCoerciveConstant d m *
        (originCubeZeroTraceH1HilbertCoerciveConstant d m *
          ((cubeVolume (originCube d m)) ^ (1 / 2 : ℝ) *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F)) := by
  let C : ℝ := originCubeZeroTraceH1HilbertCoerciveConstant d m
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact originCubeZeroTraceH1HilbertCoerciveConstant_nonneg d m
  calc
    ‖u.toH1Function.toScalarL2‖
        ≤ C * ‖u.toH1Function.gradToHilbertVectorL2‖ := by
          simpa [C] using
            originCubeZeroTraceH1HilbertCoerciveConstant_bound u
    _ ≤ C *
          (C *
            ((cubeVolume (originCube d m)) ^ (1 / 2 : ℝ) *
              cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F)) := by
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [C] using
                norm_gradToHilbertVectorL2_le_solverCubeLpNorm_exact hweak hF)
            hC_nonneg

/-- Scale-sharp forcing-facing odd-reflected parent reduced energy expression
for Dirichlet solutions, using the chosen zero-trace Poincare constant. -/
noncomputable def originCubeParentReducedSolverEnergyBoundExact
    (d : ℕ) [NeZero d] (m : ℤ) (F : Vec d → ℝ) (_i : Fin d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := originCubeZeroTraceH1HilbertCoerciveConstant d m
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

private noncomputable def originCubeParentReducedSolverEnergyInsideExact
    (d : ℕ) [NeZero d] (m : ℤ) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := originCubeZeroTraceH1HilbertCoerciveConstant d m
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
    (d : ℕ) [NeZero d] (m : ℤ) :
    0 ≤ originCubeParentReducedSolverEnergyInsideExact d m := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := originCubeZeroTraceH1HilbertCoerciveConstant d m
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

/-- The coefficient obtained by factoring the normalized forcing norm out of
the exact Dirichlet solver-energy bound. -/
noncomputable def originCubeParentReducedSolverEnergyConstantExact
    (d : ℕ) [NeZero d] (m : ℤ) : ℝ :=
  (originCubeParentReducedSolverEnergyInsideExact d m) ^ (1 / (2 : ℝ))

theorem originCubeParentReducedSolverEnergyConstantExact_nonneg
    (d : ℕ) [NeZero d] (m : ℤ) :
    0 ≤ originCubeParentReducedSolverEnergyConstantExact d m := by
  unfold originCubeParentReducedSolverEnergyConstantExact
  exact Real.rpow_nonneg
    (originCubeParentReducedSolverEnergyInsideExact_nonneg d m) _

private theorem originCubeParentReducedSolverEnergyInsideExact_eq_volume_mul_unit
    (d : ℕ) [NeZero d] (m : ℤ) :
    originCubeParentReducedSolverEnergyInsideExact d m =
      cubeVolume (originCube d m) *
        originCubeParentReducedSolverEnergyInsideExact d 0 := by
  let s : ℝ := (3 : ℝ) ^ m
  let C₀ : ℝ := originCubeZeroTraceH1HilbertCoerciveConstant d 0
  have hs_pos : 0 < s := by
    dsimp [s]
    exact zpow_pos (by norm_num : (0 : ℝ) < 3) m
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hV_m : cubeVolume (originCube d m) = s ^ d := by
    simp [cubeVolume_eq_scaleFactor_pow, s]
  have hV_0 : cubeVolume (originCube d 0) = 1 := by
    simp [cubeVolume_eq_scaleFactor_pow]
  have hC_m :
      originCubeZeroTraceH1HilbertCoerciveConstant d m = s * C₀ := by
    dsimp [originCubeZeroTraceH1HilbertCoerciveConstant,
      originCubeZeroTraceH1CoerciveConstant, C₀, s, cubeScaleFactor, originCube]
    ring
  have hC_0 :
      originCubeZeroTraceH1HilbertCoerciveConstant d 0 = C₀ := rfl
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
    (d : ℕ) [NeZero d] (m : ℤ) :
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
    (d : ℕ) [NeZero d] (m : ℤ) (F : Vec d → ℝ) (i : Fin d) :
    originCubeParentReducedSolverEnergyBoundExact d m F i =
      originCubeParentReducedSolverEnergyConstantExact d m *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := originCubeZeroTraceH1HilbertCoerciveConstant d m
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

/-- The norm-energy bound is controlled by the explicit forcing-facing
Dirichlet solver energy expression. -/
theorem originCubeParentReducedNormEnergyBound_le_solverEnergyBoundExact
    [NeZero d]
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    (i : Fin d) :
    originCubeParentReducedNormEnergyBound u F i ≤
      originCubeParentReducedSolverEnergyBoundExact d m F i := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := originCubeZeroTraceH1HilbertCoerciveConstant d m
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
            ((3 : ℝ) ^ d * ‖u.toH1Function.gradToHilbertVectorL2‖ ^ 2) +
          (2 : ℝ) *
            (Kouter *
              ((3 : ℝ) ^ d * ‖u.toH1Function.toScalarL2‖ ^ 2)))
  let Benergy : ℝ :=
    (2 : ℝ) * ((3 : ℝ) ^ d * (cubeVolume Q * L ^ (2 : ℝ))) +
      Kinner *
        ((2 : ℝ) * ((3 : ℝ) ^ d * (C * B) ^ 2) +
          (2 : ℝ) *
            (Kouter * ((3 : ℝ) ^ d * (C * (C * B)) ^ 2)))
  have hgrad_sq :
      ‖u.toH1Function.gradToHilbertVectorL2‖ ^ 2 ≤ (C * B) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _)
      (by
        simpa [Q, C, L, B] using
          norm_gradToHilbertVectorL2_le_solverCubeLpNorm_exact hweak hF)
      2
  have hvalue_sq :
      ‖u.toH1Function.toScalarL2‖ ^ 2 ≤ (C * (C * B)) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _)
      (by
        simpa [Q, C, L, B] using
          norm_toScalarL2_le_solverCubeLpNorm_exact hweak hF)
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
          ((3 : ℝ) ^ d * ‖u.toH1Function.gradToHilbertVectorL2‖ ^ 2) +
        (2 : ℝ) *
          (Kouter *
            ((3 : ℝ) ^ d * ‖u.toH1Function.toScalarL2‖ ^ 2)) ≤
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
          ((3 : ℝ) ^ d * ‖u.toH1Function.gradToHilbertVectorL2‖ ^ 2) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg hthree_nonneg (sq_nonneg _))
    have hvalue_term_nonneg :
        0 ≤ (2 : ℝ) *
          (Kouter * ((3 : ℝ) ^ d * ‖u.toH1Function.toScalarL2‖ ^ 2)) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg hKouter_nonneg
          (mul_nonneg hthree_nonneg (sq_nonneg _)))
    have hinner_orig_nonneg :
        0 ≤
          (2 : ℝ) *
              ((3 : ℝ) ^ d *
                ‖u.toH1Function.gradToHilbertVectorL2‖ ^ 2) +
            (2 : ℝ) *
              (Kouter *
                ((3 : ℝ) ^ d * ‖u.toH1Function.toScalarL2‖ ^ 2)) :=
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

/-- The fixed-radii reflected-parent Hessian estimate controlled by the
forcing-facing Dirichlet solver energy expression. -/
theorem exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_solverEnergyBoundExact
    [NeZero d]
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d m)
            u.toH1Function.toFun ∧
        uP.grad =
          cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) ∧
          ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                originCubeParentReducedSolverEnergyBoundExact d m F i := by
  rcases
    hweak.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_normEnergyBound
      hF with
    ⟨uP, huP_toFun, huP_grad, H, hH⟩
  refine ⟨uP, huP_toFun, huP_grad, H, hH.trans ?_⟩
  exact Finset.sum_le_sum fun i _hi =>
    Finset.sum_le_sum fun _j _hj =>
      originCubeParentReducedNormEnergyBound_le_solverEnergyBoundExact hweak hF i

end CubeDirichletWeakPoissonProblem

end

end Homogenization
