/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedNoteApex
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergyAveraged

/-! # Budgets -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Weak flux RHS selection: scalar budgets
-/

noncomputable section

/-- The public scalar budget supplied by the RHS Poincare tail estimate for
the gradient of a forced solution. -/
def forcedSolutionWeakFluxPoincareTailBudget
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g) : ℝ :=
  250 * (s⁻¹) ^ 2 *
      (lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a))⁻¹ *
      cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (forcedSolutionGradientField u)) +
    15000 * (s⁻¹) ^ 4 *
      ((lambdaSq Q (s / 2) (.finite 2)
        (publicCoeffField Q a))⁻¹) ^ 2 *
      ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
      (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2

theorem forcedSolutionWeakFluxPoincareTailBudget_nonneg
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (hs : 0 < s) :
    0 ≤ forcedSolutionWeakFluxPoincareTailBudget Q a s u := by
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2
      (publicCoeffField Q a) (by norm_num)
      (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hlambda_inv_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2)
        (publicCoeffField Q a))⁻¹ :=
    inv_nonneg.mpr hlambda_nonneg
  have havg_nonneg :
      0 ≤ cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (forcedSolutionGradientField u)) :=
    cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (forcedSolutionGradientField u))
  unfold forcedSolutionWeakFluxPoincareTailBudget
  positivity

/-- The public force-scale budget for the selected Neumann-corrector energy
component in the corrected weak-flux route. -/
noncomputable def forcedSolutionWeakFluxCorrectorEnergyForceScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  1000 * (geometricDiscount s 2)⁻¹ * (s⁻¹) ^ 2 *
    LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
    (lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a))⁻¹ *
    ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
    (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2

theorem forcedSolutionWeakFluxCorrectorEnergyForceScale_nonneg
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {s : ℝ} {g : Vec d → Vec d} (hs : 0 < s) :
    0 ≤ forcedSolutionWeakFluxCorrectorEnergyForceScale Q a s g := by
  have hdiscount_nonneg : 0 ≤ (geometricDiscount s 2)⁻¹ :=
    inv_nonneg.mpr
      (le_of_lt (geometricDiscount_pos (by nlinarith : 0 < s * (2 : ℝ))))
  have hLambda_nonneg :
      0 ≤ LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) :=
    multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2
      (publicCoeffField Q a) (by norm_num)
      (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hlambda_inv_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2)
        (publicCoeffField Q a))⁻¹ :=
    inv_nonneg.mpr
      (multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2
        (publicCoeffField Q a) (by norm_num)
        (by nlinarith : 0 ≤ s / 2 * (2 : ℝ)))
  unfold forcedSolutionWeakFluxCorrectorEnergyForceScale
  positivity

/-- Public wrapper for the deterministic averaged corrector-energy estimate:
after choosing Neumann correctors on every descendant at depth `n`, their
localized weak-flux corrector-energy component is bounded by the public
force-scale budget. -/
theorem weakFluxRHSDepthWeight_mul_publicCorrectorEnergyErrorAverage_le_forceScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (n : ℕ)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (z : TriadicCube d → Vec d → Vec d)
    (hz :
      ∀ R ∈ descendantsAtDepth Q n,
        ∃ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
          z R = (fun x => ω.toH1MeanZero.toH1Function.grad x)) :
    coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalCorrectorEnergyErrorAverage Q (publicCoeffField Q a) z s n ≤
      forcedSolutionWeakFluxCorrectorEnergyForceScale Q a s g := by
  simpa [forcedSolutionWeakFluxCorrectorEnergyForceScale] using
    _root_.Homogenization.weakFluxRHSDepthWeight_mul_correctorEnergyErrorAverage_le_forceScale
      (Q := Q) (a := publicCoeffField Q a) (g := g)
      (s := s) (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      n hs hs_lt.le (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
      hg.memLp hg.partialSeminorms_bddAbove z hz

theorem forcedSolutionWeakFluxCorrectorEnergyForceScale_mul_inv_one_sub_le_noteForceScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (g : Vec d → Vec d) {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    forcedSolutionWeakFluxCorrectorEnergyForceScale Q a s g *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      2500 * (s⁻¹) ^ 4 *
        LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
        (lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a))⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  simpa [forcedSolutionWeakFluxCorrectorEnergyForceScale] using
    _root_.Homogenization.weakFluxRHSCorrectorEnergyForceScale_mul_inv_one_sub_step_le_noteForceScale
      Q (publicCoeffField Q a) g hs hs_le

/-- Scalar expansion for the corrected weak-flux route after combining the
coefficient-energy component with the selected Neumann-corrector energy force
scale. -/
theorem weakFluxRHSWeightedCoefficientEnergyBase_add_publicCorrectorEnergyForceScale_mul_inv_one_sub_le_noteEnergyForce
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (u g : Vec d → Vec d) {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (havg_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q a) u)) :
    (weakFluxRHSWeightedCoefficientEnergyBase Q (publicCoeffField Q a) u s +
        forcedSolutionWeakFluxCorrectorEnergyForceScale Q a s g) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
          (publicCoeffField Q a) *
          cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a) u) +
        2500 * (s⁻¹) ^ 4 *
          LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
          (lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a))⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have hcoeff :
      weakFluxRHSWeightedCoefficientEnergyBase Q (publicCoeffField Q a) u s *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
        50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
            (publicCoeffField Q a) *
          cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a) u) :=
    weakFluxRHSWeightedCoefficientEnergyBase_mul_inv_one_sub_step_le_noteEnergySquare
      Q (publicCoeffField Q a) u hs hs_le havg_nonneg
  have hcorr :
      forcedSolutionWeakFluxCorrectorEnergyForceScale Q a s g *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
        2500 * (s⁻¹) ^ 4 *
          LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
          (lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a))⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 :=
    forcedSolutionWeakFluxCorrectorEnergyForceScale_mul_inv_one_sub_le_noteForceScale
      Q a g hs hs_le
  calc
    (weakFluxRHSWeightedCoefficientEnergyBase Q (publicCoeffField Q a) u s +
        forcedSolutionWeakFluxCorrectorEnergyForceScale Q a s g) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ =
      weakFluxRHSWeightedCoefficientEnergyBase Q (publicCoeffField Q a) u s *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹ +
        forcedSolutionWeakFluxCorrectorEnergyForceScale Q a s g *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
        ring
    _ ≤
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
          (publicCoeffField Q a) *
          cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a) u) +
        2500 * (s⁻¹) ^ 4 *
          LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a) *
          (lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a))⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 :=
        add_le_add hcoeff hcorr

end

end Ch03
end Book
end Homogenization
