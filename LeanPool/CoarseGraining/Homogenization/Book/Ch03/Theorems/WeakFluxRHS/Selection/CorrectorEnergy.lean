/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.WeakFluxRHS.Selection.Budgets

/-! # Corrector Energy -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Weak flux RHS selection: corrected local energy bridge
-/

noncomputable section

private theorem sqrt_2500_mul_fourth_mul_mul_mul_sq_mul_sq
    {x y z u w : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hu : 0 ≤ u) (hw : 0 ≤ w) :
    Real.sqrt (2500 * x ^ 4 * y * z * u ^ 2 * w ^ 2) =
      50 * x ^ 2 * Real.sqrt y * Real.sqrt z * u * w := by
  have hx_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  calc
    Real.sqrt (2500 * x ^ 4 * y * z * u ^ 2 * w ^ 2)
        =
      Real.sqrt (2500 * (x ^ 4 * (y * (z * (u ^ 2 * w ^ 2))))) := by
        ring_nf
    _ =
      Real.sqrt 2500 * Real.sqrt (x ^ 4 * (y * (z * (u ^ 2 * w ^ 2)))) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2500)]
    _ =
      Real.sqrt 2500 * (Real.sqrt (x ^ 4) * Real.sqrt (y * (z * (u ^ 2 * w ^ 2)))) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ x ^ 4)]
    _ =
      Real.sqrt 2500 * (x ^ 2 * (Real.sqrt y * Real.sqrt (z * (u ^ 2 * w ^ 2)))) := by
        rw [show x ^ 4 = (x ^ 2) ^ 2 by ring]
        rw [Real.sqrt_sq hx_sq_nonneg]
        rw [Real.sqrt_mul hy]
    _ =
      Real.sqrt 2500 * (x ^ 2 * (Real.sqrt y * (Real.sqrt z * Real.sqrt (u ^ 2 * w ^ 2)))) := by
        rw [Real.sqrt_mul hz]
    _ =
      Real.sqrt 2500 * (x ^ 2 * (Real.sqrt y * (Real.sqrt z * (u * w)))) := by
        rw [show u ^ 2 * w ^ 2 = (u * w) ^ 2 by ring]
        rw [Real.sqrt_sq (mul_nonneg hu hw)]
    _ = 50 * x ^ 2 * Real.sqrt y * Real.sqrt z * u * w := by
      rw [show Real.sqrt (2500 : ℝ) = 50 by
        calc
          Real.sqrt (2500 : ℝ) = Real.sqrt ((50 : ℝ) ^ 2) := by norm_num
          _ = 50 := Real.sqrt_sq (by norm_num : 0 ≤ (50 : ℝ))]
      ring

/-- Corrected weak-flux public bridge with the local Neumann-corrector selector
already supplied.  The coefficient-energy component is closed by public
multiscale ellipticity, while the corrector-energy component is closed by the
public averaged Neumann-corrector energy estimate. -/
theorem localizedForcedSolutionPublicFlux_le_weakFluxCorrectorEnergyExpandedRHS_of_correctorEnergySelector
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (z : TriadicCube d → Vec d → Vec d) (m : ℕ)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (publicCoeffField Q a x)
            (forcedSolutionGradientField u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (publicCoeffField Q a x)
                    (forcedSolutionGradientField u x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R (publicCoeffField Q a)
            (forcedSolutionGradientField u) (z R) s)
    (hz :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        ∃ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
          z R = (fun x => ω.toH1MeanZero.toH1Function.grad x)) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (publicCoeffField Q a x)
          (forcedSolutionGradientField u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
              (publicCoeffField Q a) *
              cubeAverage Q
                (coefficientEnergyDensity (publicCoeffField Q a)
                  (forcedSolutionGradientField u)) +
            2500 * (s⁻¹) ^ 4 *
              LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
              (lambdaSq Q (s / 2) (.finite 2)
                (publicCoeffField Q a))⁻¹ *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)) := by
  have hs_le : s ≤ 1 := hs_lt.le
  have hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q (publicCoeffField Q a) s
          (forcedSolutionGradientField u) n) :=
    weakFluxRHSScaledAveragedSeminormSq_bddAbove_publicCoeffField_forcedSolution
      u hs
  have hsum_half :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ))
              (publicCoeffField Q a)) 1) :=
    publicCoeffField_summable_qtwo_maxDescendantBBlockNormAtScale_rpow_one
      (Q := Q) (a := a) (s := s / 2) (by nlinarith)
  have havg_parent_nonneg :
      0 ≤ cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (forcedSolutionGradientField u)) :=
    cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (forcedSolutionGradientField u))
  have havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R
          (coefficientEnergyDensity (publicCoeffField Q a)
            (forcedSolutionGradientField u)) := by
    intro n R hR
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_descendant_cubeSet Q a hR)
        (forcedSolutionGradientField u))
  have hint :
      MeasureTheory.IntegrableOn
        (coefficientEnergyDensity (publicCoeffField Q a)
          (forcedSolutionGradientField u))
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
      (forcedSolutionGradientField_memVectorL2_cubeSet u)
  let Bcoeff : ℝ :=
    weakFluxRHSWeightedCoefficientEnergyBase Q (publicCoeffField Q a)
      (forcedSolutionGradientField u) s
  let Bcorr : ℝ := forcedSolutionWeakFluxCorrectorEnergyForceScale Q a s g
  have hBcoeff_nonneg : 0 ≤ Bcoeff := by
    dsimp [Bcoeff]
    exact
      weakFluxRHSWeightedCoefficientEnergyBase_nonneg Q (publicCoeffField Q a)
        (forcedSolutionGradientField u) hs havg_parent_nonneg
  have hBcorr_nonneg : 0 ≤ Bcorr := by
    dsimp [Bcorr]
    exact forcedSolutionWeakFluxCorrectorEnergyForceScale_nonneg hs
  have hcoeff :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalCoefficientEnergyErrorAverage Q (publicCoeffField Q a)
            (forcedSolutionGradientField u) s (m + k) ≤ Bcoeff := by
    intro k
    dsimp [Bcoeff]
    exact
      weakFluxRHSDepthWeight_mul_coefficientEnergyErrorAverage_le_weightedCoefficientEnergyBase
        Q (publicCoeffField Q a) (forcedSolutionGradientField u) (m + k)
        hs (publicCoeffField_isEllipticFieldOn_openCubeSet Q a)
        (publicCoeffField_openCubeDescendantDeterministicCoarseData Q a)
        hsum_half (havg_nonneg (m + k)) hint
  have hcorr :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalCorrectorEnergyErrorAverage Q (publicCoeffField Q a)
            z s (m + k) ≤ Bcorr := by
    intro k
    dsimp [Bcorr]
    exact
      weakFluxRHSDepthWeight_mul_publicCorrectorEnergyErrorAverage_le_forceScale
        (Q := Q) (a := a) (s := s) (g := g) (n := m + k)
        hs hs_lt hg z (hz (m + k))
  have hmain :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (publicCoeffField Q a x)
            (forcedSolutionGradientField u x)) m ≤
        Real.sqrt
          ((coarsePoincareRHSDepthWeight s m)⁻¹ *
            ((Bcoeff + Bcorr) * (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) :=
    _root_.Homogenization.localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_correctorEnergyComponents_bddAbove
      Q (publicCoeffField Q a) s (forcedSolutionGradientField u) z hs
      hlocal m hBdd hBcoeff_nonneg hBcorr_nonneg hcoeff hcorr
  have hscalar :
      (Bcoeff + Bcorr) * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
        50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
            (publicCoeffField Q a) *
            cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                (forcedSolutionGradientField u)) +
          2500 * (s⁻¹) ^ 4 *
            LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
            (lambdaSq Q (s / 2) (.finite 2)
              (publicCoeffField Q a))⁻¹ *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
    dsimp [Bcoeff, Bcorr]
    exact
      weakFluxRHSWeightedCoefficientEnergyBase_add_publicCorrectorEnergyForceScale_mul_inv_one_sub_le_noteEnergyForce
        Q a (forcedSolutionGradientField u) g hs hs_le havg_parent_nonneg
  have hweight_nonneg : 0 ≤ (coarsePoincareRHSDepthWeight s m)⁻¹ :=
    inv_nonneg.mpr
      (by
        unfold coarsePoincareRHSDepthWeight
        exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  exact hmain.trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hscalar hweight_nonneg))

/-- Depth-zero corrected weak-flux bridge with the left-hand side expressed as
the public finite-`2` negative Besov norm of the forced flux. -/
theorem scaleNormalizedForcedFlux_le_weakFluxCorrectorEnergyExpandedRHS_of_correctorEnergySelector
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (z : TriadicCube d → Vec d → Vec d)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (publicCoeffField Q a x)
            (forcedSolutionGradientField u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (publicCoeffField Q a x)
                    (forcedSolutionGradientField u x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R (publicCoeffField Q a)
            (forcedSolutionGradientField u) (z R) s)
    (hz :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        ∃ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
          z R = (fun x => ω.toH1MeanZero.toH1Function.grad x)) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2)
        (forcedSolutionFluxField Q a u) ≤
      Real.sqrt
        (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
            (publicCoeffField Q a) *
            cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                (forcedSolutionGradientField u)) +
          2500 * (s⁻¹) ^ 4 *
            LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
            (lambdaSq Q (s / 2) (.finite 2)
              (publicCoeffField Q a))⁻¹ *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  let F : Vec d → Vec d :=
    fun x => matVecMul (publicCoeffField Q a x) (forcedSolutionGradientField u x)
  have hloc :
      localizedFluxDefectNegativeBesovAverageTwo Q s F 0 ≤
        Real.sqrt
          (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
              (publicCoeffField Q a) *
              cubeAverage Q
                (coefficientEnergyDensity (publicCoeffField Q a)
                  (forcedSolutionGradientField u)) +
            2500 * (s⁻¹) ^ 4 *
              LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
              (lambdaSq Q (s / 2) (.finite 2)
                (publicCoeffField Q a))⁻¹ *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
    simpa [F, coarsePoincareRHSDepthWeight] using
      localizedForcedSolutionPublicFlux_le_weakFluxCorrectorEnergyExpandedRHS_of_correctorEnergySelector
        (Q := Q) (a := a) (s := s) (g := g) u z 0 hs hs_lt hg
        hlocal hz
  have hF_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N F) := by
    simpa [F] using
      forcedSolutionPublicFlux_negativeBesovPartialSeminormTwo_bddAbove_descendant
        (Q := Q) (R := Q) (a := a) (g := g) (j := 0) u
        (by simp [descendantsAtDepth_zero]) hs
  have hF_nonneg : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q s F :=
    cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove Q s F hF_bdd
  have hdepth :
      localizedFluxDefectNegativeBesovAverageTwo Q s F 0 =
        cubeBesovNegativeVectorSeminormTwo Q s F :=
    localizedFluxDefectNegativeBesovAverageTwo_depth_zero_of_nonneg
      Q s F hF_nonneg
  calc
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2)
        (forcedSolutionFluxField Q a u)
        =
      cubeBesovNegativeVectorSeminormTwo Q s F := by
        simpa [F] using
          scaleNormalizedNegativeBesovVectorNorm_forcedSolutionFluxField_finite_two_eq_cubeBesovNegativeVectorSeminormTwo_publicCoeffField
            Q a s u
    _ =
      localizedFluxDefectNegativeBesovAverageTwo Q s F 0 := hdepth.symm
    _ ≤
      Real.sqrt
        (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
            (publicCoeffField Q a) *
            cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                (forcedSolutionGradientField u)) +
          2500 * (s⁻¹) ^ 4 *
            LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
            (lambdaSq Q (s / 2) (.finite 2)
              (publicCoeffField Q a))⁻¹ *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := hloc

/-- The corrected weak-flux square-root envelope is absorbed by the public
weak-flux RHS once the theorem constant dominates the two displayed
dimension-only scalars. -/
theorem weakFluxCorrectorEnergyExpandedRHS_le_weakFluxWithRHSRHS_of_constant
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_energy : Real.sqrt 50 ≤ C)
    (hC_force :
      50 * ((d : ℝ) *
          (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d}
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    Real.sqrt
        (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
            (publicCoeffField Q a) *
            cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                (forcedSolutionGradientField u)) +
          2500 * (s⁻¹) ^ 4 *
            LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
            (lambdaSq Q (s / 2) (.finite 2)
              (publicCoeffField Q a))⁻¹ *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
      weakFluxWithRHSRHS (((d : ℝ) ^ 2) * C) Q a s g u := by
  let L : ℝ := LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a)
  let l : ℝ := lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a)
  let E : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (forcedSolutionGradientField u))
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let D : ℝ :=
    (d : ℝ) * (Real.rpow (3 : ℝ) ((d : ℝ) + s) * Real.sqrt 2)
  have hs_le : s ≤ 1 := hs_lt.le
  have hC_nonneg : 0 ≤ C :=
    (Real.sqrt_nonneg 50).trans hC_energy
  have hL_nonneg : 0 ≤ L := by
    simpa [L] using
      multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2
        (publicCoeffField Q a) (by norm_num)
        (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hl_nonneg : 0 ≤ l := by
    simpa [l] using
      multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2
        (publicCoeffField Q a) (by norm_num)
        (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hl_inv_nonneg : 0 ≤ l⁻¹ := inv_nonneg.mpr hl_nonneg
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (forcedSolutionGradientField u))
  have hB_nonneg : 0 ≤ B := by
    simpa [B, scaleNormalizedPositiveBesovVectorSeminormTwo] using
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (Q := Q) (s := s) (g := g) hg
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hD_le :
      D ≤
        (d : ℝ) *
          (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2) := by
    dsimp [D]
    have hpow :
        Real.rpow (3 : ℝ) ((d : ℝ) + s) ≤
          Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith)
    have hinner :
        Real.rpow (3 : ℝ) ((d : ℝ) + s) * Real.sqrt 2 ≤
          Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg 2)
    exact mul_le_mul_of_nonneg_left hinner (by exact_mod_cast Nat.zero_le d)
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hs_inv_sq_nonneg : 0 ≤ (s⁻¹) ^ 2 := sq_nonneg s⁻¹
  have hs_inv_sq_le :
      (s⁻¹) ^ 2 ≤ Real.rpow s (-(5 / 2 : ℝ)) := by
    calc
      (s⁻¹) ^ 2 = Real.rpow s (-2 : ℝ) := by
        rw [show (s⁻¹) ^ 2 = (s ^ (2 : ℕ))⁻¹ by field_simp [hs.ne']]
        rw [show s ^ (2 : ℕ) = Real.rpow s (2 : ℝ) by
          simp]
        rw [show (Real.rpow s (2 : ℝ))⁻¹ = Real.rpow s (-(2 : ℝ)) by
          simp]
      _ ≤ Real.rpow s (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hs hs_le (by norm_num)
  have hA_nonneg : 0 ≤ 50 * (s⁻¹) ^ 2 * L * E := by
    positivity
  have hF_nonneg : 0 ≤ 2500 * (s⁻¹) ^ 4 * L * l⁻¹ * D ^ 2 * B ^ 2 := by
    positivity
  have hsqrtA :
      Real.sqrt (50 * (s⁻¹) ^ 2 * L * E) =
        Real.sqrt 50 * s⁻¹ * Real.sqrt L * Real.sqrt E := by
    calc
      Real.sqrt (50 * (s⁻¹) ^ 2 * L * E)
          = Real.sqrt (50 * ((s⁻¹) ^ 2 * (L * E))) := by ring_nf
      _ =
          Real.sqrt 50 * Real.sqrt ((s⁻¹) ^ 2 * (L * E)) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 50)]
      _ =
          Real.sqrt 50 *
            (Real.sqrt ((s⁻¹) ^ 2) * Real.sqrt (L * E)) := by
            rw [Real.sqrt_mul (sq_nonneg s⁻¹)]
      _ =
          Real.sqrt 50 * (s⁻¹ * (Real.sqrt L * Real.sqrt E)) := by
            rw [Real.sqrt_sq hs_inv_nonneg, Real.sqrt_mul hL_nonneg]
      _ = Real.sqrt 50 * s⁻¹ * Real.sqrt L * Real.sqrt E := by ring
  have hsqrtF :
      Real.sqrt (2500 * (s⁻¹) ^ 4 * L * l⁻¹ * D ^ 2 * B ^ 2) =
        50 * (s⁻¹) ^ 2 * Real.sqrt L * Real.sqrt l⁻¹ * D * B := by
    exact sqrt_2500_mul_fourth_mul_mul_mul_sq_mul_sq
      hL_nonneg hl_inv_nonneg hD_nonneg hB_nonneg
  have henergy :
      Real.sqrt (50 * (s⁻¹) ^ 2 * L * E) ≤
        C * s⁻¹ * Real.sqrt L * Real.sqrt E := by
    have hcoeff :
        Real.sqrt 50 * s⁻¹ ≤ C * s⁻¹ :=
      mul_le_mul_of_nonneg_right hC_energy hs_inv_nonneg
    have htail : 0 ≤ Real.sqrt L * Real.sqrt E :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc
      Real.sqrt (50 * (s⁻¹) ^ 2 * L * E)
          = (Real.sqrt 50 * s⁻¹) * (Real.sqrt L * Real.sqrt E) := by
            rw [hsqrtA]
            ring
      _ ≤ (C * s⁻¹) * (Real.sqrt L * Real.sqrt E) :=
            mul_le_mul_of_nonneg_right hcoeff htail
      _ = C * s⁻¹ * Real.sqrt L * Real.sqrt E := by ring
  have hforce :
      Real.sqrt (2500 * (s⁻¹) ^ 4 * L * l⁻¹ * D ^ 2 * B ^ 2) ≤
        C * Real.rpow s (-(5 / 2 : ℝ)) *
          Real.sqrt L * Real.sqrt l⁻¹ * B := by
    have hconstD : 50 * D ≤ C := by
      calc
        50 * D ≤
            50 * ((d : ℝ) *
              (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) :=
            mul_le_mul_of_nonneg_left hD_le (by norm_num : 0 ≤ (50 : ℝ))
        _ ≤ C := hC_force
    have hcoeff :
        (50 * D) * (s⁻¹) ^ 2 ≤
          C * Real.rpow s (-(5 / 2 : ℝ)) :=
      mul_le_mul hconstD hs_inv_sq_le hs_inv_sq_nonneg hC_nonneg
    have htail : 0 ≤ Real.sqrt L * Real.sqrt l⁻¹ * B :=
      mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        hB_nonneg
    calc
      Real.sqrt (2500 * (s⁻¹) ^ 4 * L * l⁻¹ * D ^ 2 * B ^ 2)
          =
        ((50 * D) * (s⁻¹) ^ 2) *
          (Real.sqrt L * Real.sqrt l⁻¹ * B) := by
            rw [hsqrtF]
            ring
      _ ≤
        (C * Real.rpow s (-(5 / 2 : ℝ))) *
          (Real.sqrt L * Real.sqrt l⁻¹ * B) :=
            mul_le_mul_of_nonneg_right hcoeff htail
      _ =
        C * Real.rpow s (-(5 / 2 : ℝ)) *
          Real.sqrt L * Real.sqrt l⁻¹ * B := by ring
  calc
    Real.sqrt
        (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
            (publicCoeffField Q a) *
            cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                (forcedSolutionGradientField u)) +
          2500 * (s⁻¹) ^ 4 *
            LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
            (lambdaSq Q (s / 2) (.finite 2)
              (publicCoeffField Q a))⁻¹ *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)
        =
      Real.sqrt
        (50 * (s⁻¹) ^ 2 * L * E +
          2500 * (s⁻¹) ^ 4 * L * l⁻¹ * D ^ 2 * B ^ 2) := by
        simp [L, l, E, B, D]
    _ ≤
      Real.sqrt (50 * (s⁻¹) ^ 2 * L * E) +
        Real.sqrt (2500 * (s⁻¹) ^ 4 * L * l⁻¹ * D ^ 2 * B ^ 2) :=
        sqrt_add_le_add_sqrt_of_nonneg hA_nonneg hF_nonneg
    _ ≤
      C * s⁻¹ * Real.sqrt L * Real.sqrt E +
        C * Real.rpow s (-(5 / 2 : ℝ)) *
          Real.sqrt L * Real.sqrt l⁻¹ * B :=
        add_le_add henergy hforce
    _ =
      C *
        (s⁻¹ * Real.sqrt L * Real.sqrt E +
          Real.rpow s (-(5 / 2 : ℝ)) *
            Real.sqrt L * Real.sqrt l⁻¹ * B) := by ring
    _ ≤ weakFluxWithRHSRHS (((d : ℝ) ^ 2) * C) Q a s g u := by
      simpa [L, l, E, B] using
        weakFluxRHSBound_publicCoeffField_le_dim_sq_mul_public
          (d := d) C Q a u hC_nonneg hs hB_nonneg

/-- Public weak-flux estimate from a supplied corrected local selector, after
absorbing the corrected square-root envelope into `weakFluxWithRHSRHS`. -/
theorem scaleNormalizedForcedFlux_le_weakFluxWithRHSRHS_of_correctorEnergySelector
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_energy : Real.sqrt 50 ≤ C)
    (hC_force :
      50 * ((d : ℝ) *
          (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) ≤ C)
    (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (z : TriadicCube d → Vec d → Vec d)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (publicCoeffField Q a x)
            (forcedSolutionGradientField u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (publicCoeffField Q a x)
                    (forcedSolutionGradientField u x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R (publicCoeffField Q a)
            (forcedSolutionGradientField u) (z R) s)
    (hz :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        ∃ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
          z R = (fun x => ω.toH1MeanZero.toH1Function.grad x)) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2)
        (forcedSolutionFluxField Q a u) ≤
      weakFluxWithRHSRHS (((d : ℝ) ^ 2) * C) Q a s g u := by
  exact
    (scaleNormalizedForcedFlux_le_weakFluxCorrectorEnergyExpandedRHS_of_correctorEnergySelector
      (Q := Q) (a := a) (s := s) (g := g) u z hs hs_lt hg hlocal hz).trans
      (weakFluxCorrectorEnergyExpandedRHS_le_weakFluxWithRHSRHS_of_constant
        (d := d) (C := C) hC_energy hC_force
        (Q := Q) (a := a) (s := s) (g := g) u hs hs_lt hg)

end

end Ch03
end Book
end Homogenization
