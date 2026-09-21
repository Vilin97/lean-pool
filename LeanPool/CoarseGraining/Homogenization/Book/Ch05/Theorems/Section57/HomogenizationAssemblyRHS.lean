/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssembly

/-! # Homogenization Assembly RHS -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal MatrixOrder

/-!
# Deterministic RHS compression for the Section 5.7 assembly

This file takes the controlled factors supplied by
`HomogenizationAssembly.lean` and substitutes them into the deterministic Ch3
coarse-graining RHS.
-/

noncomputable section

noncomputable def assemblyLowerEllipticityEnvelopeOfScalar {d : ℕ} [NeZero d]
    (σ0 : ℝ) (α τ r : ℝ) (X : RegCoeffField d → ℝ)
    (aω : RegCoeffField d) (m : ℕ) : ℝ :=
  Real.sqrt
    (σ0⁻¹ * assemblyEllipticityEnvelope (d := d) α τ r X aω m)

noncomputable def assemblyLowerEllipticityEnvelope {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (_hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (α τ r : ℝ) (X : RegCoeffField d → ℝ) (aω : RegCoeffField d)
    (m : ℕ) : ℝ :=
  assemblyLowerEllipticityEnvelopeOfScalar
    (barSigmaLimit hP hStruct) α τ r X aω m

/-- Scale-separated Ch3 RHS after substituting the collapsed minimal-scale
bounds.  The local coefficient/ellipticity factors are controlled at exponent
`r`, while the forcing is measured at exponent `r₂` and carries the inverse
depth weight from the repaired Ch3 estimate. -/
noncomputable def assemblyCompressedTwoExponentRHSOfScalar {d : ℕ} [NeZero d]
    (σ0 : ℝ) (hσ0 : 0 < σ0)
    (Ccg α τ s r r₂ : ℝ) (X : RegCoeffField d → ℝ)
    (aω : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m j : ℕ) (g : Vec d → Vec d)
    (w : assemblyComparisonDatumOfScalar σ0 hσ0 aω ha m g) : ℝ :=
  let Q : TriadicCube d := assemblyOriginCube d m
  let F : Ch02.TriadicCoeffFamily d := assemblyCoeffFamily aω ha
  let a0 : Ch03.ConstantCoeffMatrix d :=
    assemblyConstantCoeffMatrixOfScalar σ0 hσ0
  let B₁ : ℝ := assemblyErrorEnvelope (d := d) α τ r X aω m
  let M : ℝ := assemblyEllipticityEnvelope (d := d) α τ r X aω m
  let L : ℝ := assemblyLowerEllipticityEnvelopeOfScalar σ0 α τ r X aω m
  s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
    (Ccg *
      (r⁻¹ * Ch03.constantCoeffMatrixNormHalf a0 *
          (Ch03.coarseGrainingDepthWeight r j * B₁) *
          Ch03.h1EnergyNormOnCube Q F w.u +
        (Real.rpow r (-(5 / 2 : ℝ)) *
              Ch03.constantCoeffMatrixNormHalf a0 *
              Ch03.coarseGrainingDepthHalfWeight r j *
              L *
              (Ch03.coarseGrainingDepthWeight r j * B₁) +
            Real.rpow r (-(5 / 2 : ℝ)) *
              Ch03.coarseGrainingDepthWeight r j *
              M +
            Real.rpow r (-3 : ℝ) *
              Ch03.coarseGrainingDepthWeight r j *
              Ch03.constantCoeffMatrixNorm a0 *
              (σ0⁻¹ * M)) *
          (Ch03.coarseGrainingDepthInvWeight r₂ j *
            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q r₂ g)))

/-- Finite-`sigma` wrapper for the scale-separated compressed Ch3 RHS. -/
noncomputable def assemblyCompressedTwoExponentRHS {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (Ccg α τ s r r₂ : ℝ) (X : RegCoeffField d → ℝ)
    (aω : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m j : ℕ) (g : Vec d → Vec d)
    (w : assemblyComparisonDatum hP hStruct hΓ aω ha m g) : ℝ :=
  assemblyCompressedTwoExponentRHSOfScalar
    (barSigmaLimit hP hStruct) hΓ.barSigmaLimit_pos
    Ccg α τ s r r₂ X aω ha m j g w

theorem poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {s : ℝ} (_hs : 0 < s) :
    Ch03.poincareLowerEllipticityFactor Q a s (.finite 2) =
      Real.sqrt ((Ch02.lambdaSq Q s (.finite 2) a)⁻¹) := by
  have hleft :
      Real.sqrt ((Ch02.lambdaSq Q s (.finite 2) a)⁻¹) =
        Real.rpow (Ch02.lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
    rw [← Real.rpow_eq_pow]
    ring_nf
  have hExp : (-1 / 2 : ℝ) = (-(1 / 2 : ℝ)) := by ring
  simpa [Ch03.poincareLowerEllipticityFactor, hExp] using hleft.symm

theorem poincareUpperEllipticityFactor_finite_two_eq_sqrt
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {s : ℝ} (_hs : 0 < s) :
    Ch03.poincareUpperEllipticityFactor Q a s (.finite 2) =
      Real.sqrt (Ch02.LambdaSq Q s (.finite 2) a) := by
  simp [Ch03.poincareUpperEllipticityFactor, Real.sqrt_eq_rpow]

theorem lambdaSq_finite_two_rpow_neg_one_eq_inv
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    Real.rpow (Ch02.lambdaSq Q s (.finite 2) a) (-1 : ℝ) =
      (Ch02.lambdaSq Q s (.finite 2) a)⁻¹ := by
  have hlam : 0 < Ch02.lambdaSq Q s (.finite 2) a :=
    Ch02.lambdaSq_finite_pos Q a hs (by norm_num : (1 : ℝ) ≤ 2)
  simpa using (Real.rpow_neg hlam.le (1 : ℝ))

theorem coarseGrainingHomogenizationErrorAtDepth_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d)
    {s : ℝ} (hs : 0 < s) (j : ℕ) :
    0 ≤ Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 s j := by
  unfold Ch03.coarseGrainingHomogenizationErrorAtDepth
  exact Ch02.finsetSupReal_nonneg (descendantsAtDepth Q j) _
    (fun R _hR => Ch02.HomogenizationErrorOnCube_infinity_one_nonneg
      R a a0.matrix hs)

theorem assemblyLowerEllipticityFactor_le_ofScalar
    {d : ℕ} [NeZero d] {σ0 : ℝ} (hσ0 : 0 < σ0)
    {α τ r : ℝ} {X : RegCoeffField d → ℝ} {aω : RegCoeffField d}
    {m : ℕ} (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (hr : 0 < r)
    (hlambda :
      (Ch02.lambdaSq (assemblyOriginCube d m) (r / 2) (.finite 2)
          (assemblyCoeffFamily aω ha))⁻¹ ≤
        σ0⁻¹ *
          assemblyEllipticityEnvelope (d := d) α τ r X aω m) :
    Ch03.poincareLowerEllipticityFactor (assemblyOriginCube d m)
        (assemblyCoeffFamily aω ha) (r / 2) (.finite 2) ≤
      assemblyLowerEllipticityEnvelopeOfScalar σ0 α τ r X aω m := by
  have hr2 : 0 < r / 2 := half_pos hr
  have hM_nonneg :
      0 ≤ assemblyEllipticityEnvelope (d := d) α τ r X aω m := by
    dsimp [assemblyEllipticityEnvelope]
    positivity
  have htarget_nonneg :
      0 ≤ σ0⁻¹ *
        assemblyEllipticityEnvelope (d := d) α τ r X aω m :=
    mul_nonneg (inv_nonneg.mpr hσ0.le) hM_nonneg
  calc
    Ch03.poincareLowerEllipticityFactor (assemblyOriginCube d m)
        (assemblyCoeffFamily aω ha) (r / 2) (.finite 2)
        = Real.sqrt
            ((Ch02.lambdaSq (assemblyOriginCube d m) (r / 2)
              (.finite 2) (assemblyCoeffFamily aω ha))⁻¹) :=
          poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv
            (assemblyOriginCube d m) (assemblyCoeffFamily aω ha) hr2
    _ ≤ Real.sqrt
          (σ0⁻¹ *
            assemblyEllipticityEnvelope (d := d) α τ r X aω m) :=
          Real.sqrt_le_sqrt hlambda
    _ = assemblyLowerEllipticityEnvelopeOfScalar σ0 α τ r X aω m := rfl

theorem assemblyLowerEllipticityFactor_le
    {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {α τ r : ℝ} {X : RegCoeffField d → ℝ} {aω : RegCoeffField d}
    {m : ℕ} (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (hr : 0 < r)
    (hlambda :
      (Ch02.lambdaSq (assemblyOriginCube d m) (r / 2) (.finite 2)
          (assemblyCoeffFamily aω ha))⁻¹ ≤
        (barSigmaLimit hP hStruct)⁻¹ *
          assemblyEllipticityEnvelope (d := d) α τ r X aω m) :
    Ch03.poincareLowerEllipticityFactor (assemblyOriginCube d m)
        (assemblyCoeffFamily aω ha) (r / 2) (.finite 2) ≤
      assemblyLowerEllipticityEnvelope hP hStruct hΓ α τ r X aω m := by
  simpa [assemblyLowerEllipticityEnvelope] using
    assemblyLowerEllipticityFactor_le_ofScalar
      (σ0 := barSigmaLimit hP hStruct) hΓ.barSigmaLimit_pos
      (α := α) (τ := τ) (r := r) (X := X) (aω := aω)
      (m := m) ha hr hlambda

/-- Substitute the controlled factors into the repaired scale-separated Ch3
deterministic RHS. -/
theorem assemblyControlledFactors_lhs_le_compressedTwoExponentRHS_ofScalar
    {d : ℕ} [NeZero d] {σ0 : ℝ} (hσ0 : 0 < σ0)
    {Ccg α τ s r r₂ : ℝ} {X : RegCoeffField d → ℝ}
    {aω : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField aω)
    {m j : ℕ} {g : Vec d → Vec d}
    (w : assemblyComparisonDatumOfScalar σ0 hσ0 aω ha m g)
    (hCcg : 0 < Ccg) (hs : 0 < s) (hr : 0 < r)
    (hrs : r < s / 2) (hs_lt_one : s < 1)
    (hg : Ch03.ForceBesovRegularity (assemblyOriginCube d m) r₂ g)
    (hctrl :
      assemblyControlledFactorsTwoExponentConclusionOfScalar
        σ0 hσ0 Ccg α τ s r r₂ X aω ha m j g w) :
    Ch03.homogenizationComparisonNegativeBesovLHS
        (assemblyOriginCube d m) (assemblyCoeffFamily aω ha)
        (assemblyConstantCoeffMatrixOfScalar σ0 hσ0) s w.u w.v ≤
      assemblyCompressedTwoExponentRHSOfScalar
        σ0 hσ0 Ccg α τ s r r₂ X aω ha m j g w := by
  let Q : TriadicCube d := assemblyOriginCube d m
  let F : Ch02.TriadicCoeffFamily d := assemblyCoeffFamily aω ha
  let a0 : Ch03.ConstantCoeffMatrix d :=
    assemblyConstantCoeffMatrixOfScalar σ0 hσ0
  let B₁ : ℝ := assemblyErrorEnvelope (d := d) α τ r X aω m
  let M : ℝ := assemblyEllipticityEnvelope (d := d) α τ r X aω m
  let Lenv : ℝ := assemblyLowerEllipticityEnvelopeOfScalar σ0 α τ r X aω m
  dsimp [assemblyControlledFactorsTwoExponentConclusionOfScalar, Q, F, a0,
    B₁, M] at hctrl
  rcases hctrl with ⟨hcomparison, hH, _hweighted, hlambdaInv, hsqrtProd⟩
  have hr_half : 0 < r / 2 := half_pos hr
  have hLamRpow :
      Real.rpow (Ch02.lambdaSq Q (r / 2) (.finite 2) F) (-1 : ℝ) ≤
        σ0⁻¹ * M := by
    simpa [Q, F, M] using
      (lambdaSq_finite_two_rpow_neg_one_eq_inv Q F hr_half).trans_le
        hlambdaInv
  have hLower :
      Ch03.poincareLowerEllipticityFactor Q F (r / 2) (.finite 2) ≤
        Lenv := by
    simpa [Q, F, M, Lenv] using
      assemblyLowerEllipticityFactor_le_ofScalar (σ0 := σ0) hσ0
        (α := α) (τ := τ) (r := r) (X := X) (aω := aω)
        (m := m) ha hr hlambdaInv
  have hProd :
      Ch03.poincareUpperEllipticityFactor Q F (r / 2) (.finite 2) *
          Ch03.poincareLowerEllipticityFactor Q F (r / 2) (.finite 2) ≤
        M := by
    rw [poincareUpperEllipticityFactor_finite_two_eq_sqrt Q F hr_half,
      poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv Q F hr_half]
    exact hsqrtProd
  have hH_nonneg :
      0 ≤ Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j :=
    coarseGrainingHomogenizationErrorAtDepth_nonneg Q F a0 hr j
  have hHbd_nonneg : 0 ≤ Ch03.coarseGrainingDepthWeight r j * B₁ :=
    hH_nonneg.trans hH
  have hLenv_nonneg : 0 ≤ Lenv := by
    dsimp [Lenv, assemblyLowerEllipticityEnvelopeOfScalar]
    exact Real.sqrt_nonneg _
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, assemblyEllipticityEnvelope]
    positivity
  have hBsemi_nonneg :
      0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q r₂ g := by
    simpa [Q] using
      Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (Q := assemblyOriginCube d m) (s := r₂) (g := g) hg
  have hforceWeight_nonneg :
      0 ≤ Ch03.coarseGrainingDepthInvWeight r₂ j *
        Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q r₂ g := by
    exact mul_nonneg (by
      dsimp [Ch03.coarseGrainingDepthInvWeight, Ch03.coarseGrainingDepthWeight]
      positivity) hBsemi_nonneg
  have hEnergy_nonneg : 0 ≤ Ch03.h1EnergyNormOnCube Q F w.u := by
    dsimp [Ch03.h1EnergyNormOnCube]
    positivity
  have hMhalf_nonneg : 0 ≤ Ch03.constantCoeffMatrixNormHalf a0 := by
    dsimp [Ch03.constantCoeffMatrixNormHalf]
    exact Real.rpow_nonneg (Ch02.matrixNorm_nonneg a0.matrix) _
  have hMnorm_nonneg : 0 ≤ Ch03.constantCoeffMatrixNorm a0 := by
    dsimp [Ch03.constantCoeffMatrixNorm]
    exact Ch02.matrixNorm_nonneg a0.matrix
  have hdepth_nonneg : 0 ≤ Ch03.coarseGrainingDepthWeight r j := by
    dsimp [Ch03.coarseGrainingDepthWeight]
    positivity
  have hdepthHalf_nonneg : 0 ≤ Ch03.coarseGrainingDepthHalfWeight r j := by
    dsimp [Ch03.coarseGrainingDepthHalfWeight]
    positivity
  have houter_nonneg :
      0 ≤ s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ := by
    have hr_lt_half : r < (1 / 2 : ℝ) := by nlinarith
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr hs.le) (sq_nonneg r⁻¹))
      (inv_nonneg.mpr (sub_nonneg.mpr hr_lt_half.le))
  have hCcg_nonneg : 0 ≤ Ccg := hCcg.le
  have hterm₁ :
      r⁻¹ * Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j *
          Ch03.h1EnergyNormOnCube Q F w.u ≤
        r⁻¹ * Ch03.constantCoeffMatrixNormHalf a0 *
          (Ch03.coarseGrainingDepthWeight r j * B₁) *
          Ch03.h1EnergyNormOnCube Q F w.u := by
    have hcoeff :
        0 ≤ r⁻¹ * Ch03.constantCoeffMatrixNormHalf a0 :=
      mul_nonneg (inv_nonneg.mpr hr.le) hMhalf_nonneg
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hH hcoeff) hEnergy_nonneg
  have hterm₂a :
      Real.rpow r (-(5 / 2 : ℝ)) *
          Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.coarseGrainingDepthHalfWeight r j *
          Ch03.poincareLowerEllipticityFactor Q F (r / 2) (.finite 2) *
          Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j ≤
        Real.rpow r (-(5 / 2 : ℝ)) *
          Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.coarseGrainingDepthHalfWeight r j *
          Lenv *
          (Ch03.coarseGrainingDepthWeight r j * B₁) := by
    have hcoeff :
        0 ≤ Real.rpow r (-(5 / 2 : ℝ)) *
          Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.coarseGrainingDepthHalfWeight r j := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hr.le _) hMhalf_nonneg)
        hdepthHalf_nonneg
    calc
      Real.rpow r (-(5 / 2 : ℝ)) *
          Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.coarseGrainingDepthHalfWeight r j *
          Ch03.poincareLowerEllipticityFactor Q F (r / 2) (.finite 2) *
          Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j
          ≤
        Real.rpow r (-(5 / 2 : ℝ)) *
          Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.coarseGrainingDepthHalfWeight r j *
          Lenv *
          Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hLower hcoeff) hH_nonneg
      _ ≤
        Real.rpow r (-(5 / 2 : ℝ)) *
          Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.coarseGrainingDepthHalfWeight r j *
          Lenv *
          (Ch03.coarseGrainingDepthWeight r j * B₁) := by
            have hcoeff₂ :
                0 ≤ Real.rpow r (-(5 / 2 : ℝ)) *
                  Ch03.constantCoeffMatrixNormHalf a0 *
                  Ch03.coarseGrainingDepthHalfWeight r j *
                  Lenv := mul_nonneg hcoeff hLenv_nonneg
            exact mul_le_mul_of_nonneg_left hH hcoeff₂
  have hterm₂b :
      Real.rpow r (-(5 / 2 : ℝ)) *
          Ch03.coarseGrainingDepthWeight r j *
          Ch03.poincareUpperEllipticityFactor Q F (r / 2) (.finite 2) *
          Ch03.poincareLowerEllipticityFactor Q F (r / 2) (.finite 2) ≤
        Real.rpow r (-(5 / 2 : ℝ)) *
          Ch03.coarseGrainingDepthWeight r j *
          M := by
    have hcoeff :
        0 ≤ Real.rpow r (-(5 / 2 : ℝ)) *
          Ch03.coarseGrainingDepthWeight r j :=
      mul_nonneg (Real.rpow_nonneg hr.le _) hdepth_nonneg
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hProd hcoeff
  have hterm₂c :
      Real.rpow r (-3 : ℝ) *
          Ch03.coarseGrainingDepthWeight r j *
          Ch03.constantCoeffMatrixNorm a0 *
          Real.rpow (Ch02.lambdaSq Q (r / 2) (.finite 2) F) (-1 : ℝ) ≤
        Real.rpow r (-3 : ℝ) *
          Ch03.coarseGrainingDepthWeight r j *
          Ch03.constantCoeffMatrixNorm a0 *
          (σ0⁻¹ * M) := by
    have hcoeff :
        0 ≤ Real.rpow r (-3 : ℝ) *
          Ch03.coarseGrainingDepthWeight r j *
          Ch03.constantCoeffMatrixNorm a0 := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hr.le _) hdepth_nonneg)
        hMnorm_nonneg
    exact mul_le_mul_of_nonneg_left hLamRpow hcoeff
  have hbracket :
      r⁻¹ * Ch03.constantCoeffMatrixNormHalf a0 *
          Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j *
          Ch03.h1EnergyNormOnCube Q F w.u +
        (Real.rpow r (-(5 / 2 : ℝ)) *
              Ch03.constantCoeffMatrixNormHalf a0 *
              Ch03.coarseGrainingDepthHalfWeight r j *
              Ch03.poincareLowerEllipticityFactor Q F (r / 2) (.finite 2) *
              Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j +
            Real.rpow r (-(5 / 2 : ℝ)) *
              Ch03.coarseGrainingDepthWeight r j *
              Ch03.poincareUpperEllipticityFactor Q F (r / 2) (.finite 2) *
              Ch03.poincareLowerEllipticityFactor Q F (r / 2) (.finite 2) +
            Real.rpow r (-3 : ℝ) *
              Ch03.coarseGrainingDepthWeight r j *
              Ch03.constantCoeffMatrixNorm a0 *
              Real.rpow (Ch02.lambdaSq Q (r / 2) (.finite 2) F) (-1 : ℝ)) *
          (Ch03.coarseGrainingDepthInvWeight r₂ j *
            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q r₂ g)
        ≤
      r⁻¹ * Ch03.constantCoeffMatrixNormHalf a0 *
          (Ch03.coarseGrainingDepthWeight r j * B₁) *
          Ch03.h1EnergyNormOnCube Q F w.u +
        (Real.rpow r (-(5 / 2 : ℝ)) *
              Ch03.constantCoeffMatrixNormHalf a0 *
              Ch03.coarseGrainingDepthHalfWeight r j *
              Lenv *
              (Ch03.coarseGrainingDepthWeight r j * B₁) +
            Real.rpow r (-(5 / 2 : ℝ)) *
              Ch03.coarseGrainingDepthWeight r j *
              M +
            Real.rpow r (-3 : ℝ) *
              Ch03.coarseGrainingDepthWeight r j *
              Ch03.constantCoeffMatrixNorm a0 *
              (σ0⁻¹ * M)) *
          (Ch03.coarseGrainingDepthInvWeight r₂ j *
            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q r₂ g) := by
    exact add_le_add hterm₁
      (mul_le_mul_of_nonneg_right
        (add_le_add (add_le_add hterm₂a hterm₂b) hterm₂c)
        hforceWeight_nonneg)
  have hgeneral_le :
      Ch03.generalCoarseGrainingL2TwoExponentRHS Ccg Q F a0 s r r₂ j g w.u ≤
        assemblyCompressedTwoExponentRHSOfScalar
          σ0 hσ0 Ccg α τ s r r₂ X aω ha m j g w := by
    dsimp [Ch03.generalCoarseGrainingL2TwoExponentRHS,
      Ch03.generalCoarseGrainingL2TwoExponentFluxDefectRHS,
      assemblyCompressedTwoExponentRHSOfScalar, Q, F, a0, B₁, M, Lenv]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hbracket hCcg_nonneg) houter_nonneg
  exact hcomparison.trans hgeneral_le

/-- Finite-`sigma` wrapper for the scale-separated deterministic RHS
substitution. -/
theorem assemblyControlledFactors_lhs_le_compressedTwoExponentRHS
    {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {Ccg α τ s r r₂ : ℝ} {X : RegCoeffField d → ℝ}
    {aω : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField aω)
    {m j : ℕ} {g : Vec d → Vec d}
    (w : assemblyComparisonDatum hP hStruct hΓ aω ha m g)
    (hCcg : 0 < Ccg) (hs : 0 < s) (hr : 0 < r)
    (hrs : r < s / 2) (hs_lt_one : s < 1)
    (hg : Ch03.ForceBesovRegularity (assemblyOriginCube d m) r₂ g)
    (hctrl :
      assemblyControlledFactorsTwoExponentConclusion
        hP hStruct hΓ Ccg α τ s r r₂ X aω ha m j g w) :
    Ch03.homogenizationComparisonNegativeBesovLHS
        (assemblyOriginCube d m) (assemblyCoeffFamily aω ha)
        (assemblyConstantCoeffMatrix hP hStruct hΓ) s w.u w.v ≤
      assemblyCompressedTwoExponentRHS
        hP hStruct hΓ Ccg α τ s r r₂ X aω ha m j g w := by
  simpa [assemblyConstantCoeffMatrix, assemblyCompressedTwoExponentRHS,
    assemblyControlledFactorsTwoExponentConclusion] using
    assemblyControlledFactors_lhs_le_compressedTwoExponentRHS_ofScalar
      (σ0 := barSigmaLimit hP hStruct) hΓ.barSigmaLimit_pos
      (Ccg := Ccg) (α := α) (τ := τ) (s := s) (r := r)
      (r₂ := r₂) (X := X) (aω := aω) ha (m := m) (j := j)
      (g := g) w hCcg hs hr hrs hs_lt_one hg hctrl

/-- Sigma-agnostic a.e. handoff for the repaired two-exponent Ch3 assembly. -/
theorem ae_homogenizationComparison_compressedTwoExponentRHSOfScalar_of_ae_controlledFactors
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {σ0 : ℝ} (hσ0 : 0 < σ0)
    {Ccg α τ s r r₂ : ℝ} {X : RegCoeffField d → ℝ}
    (hCcg : 0 < Ccg) (hs : 0 < s) (hr : 0 < r)
    (hrs : r < s / 2) (hs_lt_one : s < 1)
    (hctrl :
      ∀ᵐ aω ∂P,
        ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
          {m j : ℕ} {g : Vec d → Vec d},
          (w : assemblyComparisonDatumOfScalar σ0 hσ0 aω ha m g) →
          X aω ≤ (3 : ℝ) ^ m →
          Ch03.ForceBesovRegularity (assemblyOriginCube d m) r₂ g →
          assemblyControlledFactorsTwoExponentConclusionOfScalar
            σ0 hσ0 Ccg α τ s r r₂ X aω ha m j g w) :
    ∀ᵐ aω ∂P,
      ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
        {m j : ℕ} {g : Vec d → Vec d}
        (w : assemblyComparisonDatumOfScalar σ0 hσ0 aω ha m g),
        X aω ≤ (3 : ℝ) ^ m →
        Ch03.ForceBesovRegularity (assemblyOriginCube d m) r₂ g →
        Ch03.homogenizationComparisonNegativeBesovLHS
            (assemblyOriginCube d m) (assemblyCoeffFamily aω ha)
            (assemblyConstantCoeffMatrixOfScalar σ0 hσ0) s w.u w.v ≤
          assemblyCompressedTwoExponentRHSOfScalar
            σ0 hσ0 Ccg α τ s r r₂ X aω ha m j g w := by
  filter_upwards [hctrl] with aω hpoint
  intro ha m j g w hXm hg
  exact
    assemblyControlledFactors_lhs_le_compressedTwoExponentRHS_ofScalar
      (σ0 := σ0) hσ0 (Ccg := Ccg) (α := α) (τ := τ)
      (s := s) (r := r) (r₂ := r₂) (X := X) (aω := aω) ha
      (m := m) (j := j) (g := g) w hCcg hs hr hrs hs_lt_one hg
      (hpoint ha w hXm hg)

/-- Finite-`sigma` homogenization comparison above one collapsed minimal scale,
using the repaired scale-separated forcing exponent. -/
theorem exists_homogenizationComparison_compressedTwoExponentRHS_interpolated_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccg α : ℝ, 0 < Ccg ∧ 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {σ τ s r r₂ : ℝ}, 0 < σ →
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 < s →
        0 < r →
        r < s / 2 →
        s < 1 →
        τ < r →
        r ≤ r₂ →
        let ηJ : ℝ := finiteQuenchedTailExponent d σ τ
        let ηU : ℝ := finiteQuenchedTailExponent d σ (τ / 2)
        let η : ℝ := min ηJ ηU
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
                    {m j : ℕ} {g : Vec d → Vec d}
                    (w : assemblyComparisonDatum hP hStruct hΓ aω ha m g),
                    X aω ≤ (3 : ℝ) ^ m →
                    Ch03.ForceBesovRegularity (assemblyOriginCube d m) r₂ g →
                    Ch03.homogenizationComparisonNegativeBesovLHS
                        (assemblyOriginCube d m) (assemblyCoeffFamily aω ha)
                        (assemblyConstantCoeffMatrix hP hStruct hΓ)
                        s w.u w.v ≤
                      assemblyCompressedTwoExponentRHS
                        hP hStruct hΓ Ccg α τ s r r₂ X aω ha m j g w := by
  obtain ⟨Ccg, α, hCcg, hα, hαmax, hcontrolled⟩ :=
    exists_homogenizationComparison_controlledFactors_twoExponent_interpolated_expLogSq
      (d := d) params
  refine ⟨Ccg, α, hCcg, hα, hαmax, ?_⟩
  intro σ τ s r r₂ hσ hτ hατ hτ_one hs hr hrs hs_one hτr hr₂
  dsimp only
  obtain ⟨Cscale, hCscale, hlaw⟩ :=
    hcontrolled hσ hτ hατ hτ_one hs hr hrs hs_one hτr hr₂
  refine ⟨Cscale, hCscale, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  obtain ⟨X, hXO, hXone, hAE⟩ :=
    hlaw hP hStruct hΓ hσ_eq hparams
  refine ⟨X, hXO, hXone, ?_⟩
  simpa [assemblyComparisonDatum, assemblyConstantCoeffMatrix,
    assemblyControlledFactorsTwoExponentConclusion,
    assemblyCompressedTwoExponentRHS] using
    ae_homogenizationComparison_compressedTwoExponentRHSOfScalar_of_ae_controlledFactors
      (P := P) (σ0 := barSigmaLimit hP hStruct) hΓ.barSigmaLimit_pos
      (Ccg := Ccg) (α := α) (τ := τ) (s := s) (r := r)
      (r₂ := r₂) (X := X) hCcg hs hr hrs hs_one hAE

end

end Section57
end Ch05
end Book
end Homogenization
