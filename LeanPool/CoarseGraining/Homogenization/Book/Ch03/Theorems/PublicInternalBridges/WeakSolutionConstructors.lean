/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutions

/-! # Weak Solution Constructors -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public weak-solution constructor bridges

This file contains terminal constructor bridges built from the public
weak-solution conversion lemmas.

## Audit tag

Claim: construct the public-coefficient corrector data and homogenization
comparison-pair witnesses used by the Chapter 3 endpoint theorem packages.

Downstream target: Ch3 public aggregate imports.  This file is constructor
plumbing only and introduces no public `*Theory` package.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open ZeroTraceDirichletCorrectorData

noncomputable def neumannForcedSolutionMeanZeroCorrectorData_publicCoeffField
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (w : NeumannForcedCubeSolution Q a g) :
    MeanZeroNeumannCorrectorData Q (publicCoeffField Q a)
      (fun x => g x - cubeAverageVec Q g) where
  toH1MeanZero := publicH1MeanZeroToCubeSet w.toH1MeanZero
  weakSolution :=
    isMeanZeroNeumannRhsWeakSolution_publicCoeffField_cubeSet_of_neumannForcedCubeSolution
      w

@[simp] theorem neumannForcedSolutionMeanZeroCorrectorData_publicCoeffField_grad
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (w : NeumannForcedCubeSolution Q a g) :
    (neumannForcedSolutionMeanZeroCorrectorData_publicCoeffField w).toH1MeanZero.toH1Function.grad =
      w.toH1MeanZero.toH1Function.grad := by
  simp [neumannForcedSolutionMeanZeroCorrectorData_publicCoeffField]

theorem forcedSolutionGradientField_coarsePoincareRHSSn_le_expanded_publicCoeffField
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {s : ℝ}
    (u : ForcedCubeSolution Q a g) (hs : 0 < s) (hs_le : s ≤ 1)
    (hg : ForceBesovRegularity Q s g) (m : ℕ) :
    coarsePoincareRHSSn Q s (forcedSolutionGradientField u) m ≤
      250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a))⁻¹ *
          cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (forcedSolutionGradientField u)) +
        15000 * (s⁻¹) ^ 4 *
          ((lambdaSq Q (s / 2) (.finite 2)
            (publicCoeffField Q a))⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have hweak :
      IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a) (cubeSet Q)
        (publicH1ToCubeSet u.toH1) g :=
    isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
      (Q := Q) (a := a) (u := u.toH1) (g := g) u.weakSolution
  have hdet :=
    _root_.Homogenization.coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
      (Q := Q) (a := publicCoeffField Q a) (g := g)
      (u := (publicH1ToCubeSet u.toH1).grad) (s := s)
      (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      hs hs_le (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
      (publicH1ToCubeSet u.toH1).isPotentialOn
      (hweak.residual_solenoidal
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (memVectorL2_cubeSet_of_forceBesovRegularity hg))
      hg.memLp hg.partialSeminorms_bddAbove m
  simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using hdet

theorem isH1DirichletRhsWeakSolutionOn_constantCoeff_cubeSet_of_isConstantCoeffForcedEquation
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a0 : ConstantCoeffMatrix d}
    {u : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (h : IsConstantCoeffForcedEquation Q a0 u g) :
    IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0.matrix) (cubeSet Q)
      (publicH1ToCubeSet u) g := by
  have hopen :
      IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0.matrix)
        (openCubeSet Q) (castH1Domain (Ch02.cubeDomain_coe Q) u) g := by
    simpa [Ch02.cubeDomain_coe] using!
      isH1DirichletRhsWeakSolutionOn_constantCoeff_of_isConstantCoeffForcedEquation
        (Q := Q) (a0 := a0) (u := u) (g := g) h
  simpa [publicH1ToCubeSet] using
    isH1DirichletRhsWeakSolutionOn_cubeSet_of_openCubeSet
      (Q := Q) (a := constantCoeffField a0.matrix)
      (u := castH1Domain (Ch02.cubeDomain_coe Q) u) (g := g) hopen

theorem isZeroTraceDirichletRhsWeakSolution_publicCoeffField_cubeSet_of_zeroTraceForcedCubeSolution
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d}
    (u : ZeroTraceForcedCubeSolution Q a g) :
    IsZeroTraceDirichletRhsWeakSolution (publicCoeffField Q a) (cubeSet Q)
      (publicH10ToCubeSet u.toH10) g := by
  have hopen :
      IsZeroTraceDirichletRhsWeakSolution (publicCoeffField Q a)
        (openCubeSet Q) (castH10Domain (Ch02.cubeDomain_coe Q) u.toH10) g := by
    simpa [Ch02.cubeDomain_coe] using!
      isZeroTraceDirichletRhsWeakSolution_publicCoeffField_of_zeroTraceForcedCubeSolution
        (Q := Q) (a := a) (g := g) u
  simpa [publicH10ToCubeSet] using
    isZeroTraceDirichletRhsWeakSolution_cubeSet_of_openCubeSet
      (Q := Q) (a := publicCoeffField Q a)
      (u := castH10Domain (Ch02.cubeDomain_coe Q) u.toH10) (g := g) hopen

/-- Canonical public-coefficient zero-trace RHS corrector on the half-open
cube.  This is the public Chapter 3 bridge for the auxiliary zero-boundary
solution `v₀` used in the Dirichlet energy argument. -/
noncomputable def zeroTraceDirichletCorrectorData_publicCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {g : Vec d → Vec d} (hg : MemVectorL2 (cubeSet Q) g) :
    ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g :=
  zeroTraceDirichletCorrectorDataOf_isEllipticFieldOn_cubeSet
    (Q := Q) (a := publicCoeffField Q a) (g := g)
    (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
    hg (publicCoeffField_isEllipticFieldOn_cubeSet Q a)

theorem isHomogenizationComparisonPairOn_publicCoeffField_cubeSet_of_public_comparison
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d}
    (w : HomogenizationComparisonDatum Q a a0)
    (hzero :
      IsPotentialZeroTraceOn (cubeSet Q)
        (fun x => w.u.grad x - w.v.grad x)) :
    IsHomogenizationComparisonPairOn (cubeSet Q)
      (publicCoeffField Q a) a0.matrix
      (publicH1ToCubeSet w.u).grad (publicH1ToCubeSet w.v).grad := by
  have hsolOpenOriginal :
      IsSolenoidalOn (openCubeSet Q)
        (homogenizationComparisonFluxField Q a a0 w.u w.v) := by
    simpa [Ch02.cubeDomain_coe] using w.fluxComparisonSolenoidal
  have hfluxAE :
      homogenizationComparisonFluxField Q a a0 w.u w.v
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fluxComparison (publicCoeffField Q a) a0.matrix w.u.grad w.v.grad := by
    filter_upwards [publicCoeffField_ae_eq_openCubeSet Q a] with x hx
    ext i
    simp [homogenizationComparisonFluxField, fluxComparison, hx]
  have hsolOpen :
      IsSolenoidalOn (openCubeSet Q)
        (fluxComparison (publicCoeffField Q a) a0.matrix w.u.grad w.v.grad) :=
    IsSolenoidalOn.congr_ae hfluxAE hsolOpenOriginal
  have hsolCube :
      IsSolenoidalOn (cubeSet Q)
        (fluxComparison (publicCoeffField Q a) a0.matrix w.u.grad w.v.grad) :=
    isSolenoidalOn_cubeSet_triadicCube_of_openCubeSet hsolOpen
  constructor
  · simpa using hsolCube
  · simpa using hzero

theorem HomogenizationComparisonDatum.isHomogenizationComparisonPairOn_publicCoeffField_cubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d}
    (w : HomogenizationComparisonDatum Q a a0) :
    IsHomogenizationComparisonPairOn (cubeSet Q)
      (publicCoeffField Q a) a0.matrix
      (publicH1ToCubeSet w.u).grad (publicH1ToCubeSet w.v).grad :=
  isHomogenizationComparisonPairOn_publicCoeffField_cubeSet_of_public_comparison
    (Q := Q) (a := a) (a0 := a0) w
    w.isPotentialZeroTraceOn_cubeSet

theorem isHomogenizationComparisonPairOn_publicCoeffField_cubeSet_of_same_public_forcedEquations
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d}
    {u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (hu : IsForcedEquation Q a u g)
    (hv : IsConstantCoeffForcedEquation Q a0 v g)
    (hzero :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x)) :
    IsHomogenizationComparisonPairOn (cubeSet Q)
      (publicCoeffField Q a) a0.matrix
      (publicH1ToCubeSet u).grad (publicH1ToCubeSet v).grad := by
  have huWeak :
      IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a) (cubeSet Q)
        (publicH1ToCubeSet u) g :=
    isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
      (Q := Q) (a := a) (u := u) (g := g) hu
  have hvWeak :
      IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0.matrix) (cubeSet Q)
        (publicH1ToCubeSet v) g :=
    isH1DirichletRhsWeakSolutionOn_constantCoeff_cubeSet_of_isConstantCoeffForcedEquation
      (Q := Q) (a0 := a0) (u := v) (g := g) hv
  exact
    IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
      (hEll := publicCoeffField_isEllipticFieldOn_cubeSet Q a)
      (ha0 := a0.elliptic)
      (u := publicH1ToCubeSet u) (v := publicH1ToCubeSet v)
      (g := g) huWeak hvWeak (by simpa using hzero)

theorem CoarseGrainingComparisonDatum.isHomogenizationComparisonPairOn_publicCoeffField_cubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d} {g : Vec d → Vec d}
    (w : CoarseGrainingComparisonDatum Q a a0 g) :
    IsHomogenizationComparisonPairOn (cubeSet Q)
      (publicCoeffField Q a) a0.matrix
      (publicH1ToCubeSet w.u).grad (publicH1ToCubeSet w.v).grad :=
  isHomogenizationComparisonPairOn_publicCoeffField_cubeSet_of_same_public_forcedEquations
    (Q := Q) (a := a) (a0 := a0) (u := w.u) (v := w.v) (g := g)
    w.uWeakSolution w.vWeakSolution w.isPotentialZeroTraceOn_cubeSet

end

end Ch03
end Book
end Homogenization
