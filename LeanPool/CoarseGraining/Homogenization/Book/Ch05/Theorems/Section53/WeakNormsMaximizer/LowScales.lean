/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.EnergyDefect

/-! # Low Scales -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace WeakNormsMaximizer

/-!
# Low-scale tails for the weak-norm maximizer lemma

This file controls the low-depth part of the parent scalar-response maximizer
field by the parent response and the q=1 multiscale ellipticity observables.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

private theorem cubeAverage_nonneg_of_ae_nonneg {d : ℕ}
    {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : ∀ᵐ x ∂volume.restrict (cubeSet Q), 0 ≤ f x) :
    0 ≤ cubeAverage Q f := by
  unfold cubeAverage
  refine mul_nonneg (inv_nonneg.mpr (le_of_lt (cubeVolume_pos Q))) ?_
  exact MeasureTheory.integral_nonneg_of_ae hf

private theorem multiscaleDescendantWeight_sub_nat {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) s =
      Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) := by
  unfold Ch02.multiscaleDescendantWeight
  have hsub : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
    omega
  rw [hsub]
  norm_num

private theorem averageGradient_parentResponseSolutionOnDependentFamilyRestrictedToCube_eq_cubeAverageVec
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    Ch02.averageGradient (Ch02.cubeDomain R) (F.coeffOn R)
        (JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
          a ha Q hR p q) =
      cubeAverageVec R
        (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q) := by
  intro F
  ext i
  rw [Ch02.averageGradient, Ch02.averageVec,
    JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
  simp [cubeAverageVec, F,
    JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube_grad]

private theorem averageFlux_parentResponseSolutionOnDependentFamilyRestrictedToCube_eq_cubeAverageVec
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    Ch02.averageFlux (Ch02.cubeDomain R) (F.coeffOn R)
        (JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
          a ha Q hR p q) =
      cubeAverageVec R
        (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q) := by
  intro F
  ext i
  rw [Ch02.averageFlux, Ch02.averageVec,
    JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
  apply cubeAverage_eq_of_eq_on_cubeSet
  intro x _hx
  simp [JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube_grad,
    JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube, F]

private theorem variationEnergyValue_parentResponseSolutionOnDependentFamilyRestrictedToCube_eq
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    Ch02.variationEnergyValue (Ch02.cubeDomain R) (F.coeffOn R)
        (JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
          a ha Q hR p q) =
      2 * cubeAverage R (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q) := by
  intro F
  rw [Ch02.variationEnergyValue,
    JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
  have hpoint :
      Ch02.variationEnergyIntegrand (Ch02.cubeDomain R) (F.coeffOn R)
          (JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
            a ha Q hR p q) =
        fun x => 2 * JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q x := by
    funext x
    simp [Ch02.variationEnergyIntegrand,
      JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube_grad,
      JUpperBoundWeakNorms.topHalfEnergyDensityOnCube,
      JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube, F]
  rw [hpoint, cubeAverage_const_mul]

private theorem descendantsAverage_parentGradient_le_maxSigmaStarInv_mul_responseJ
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (cubeAverageVec R
              (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q))) ≤
      2 * Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) F *
        Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q := by
  intro F
  let M := Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) F
  let E : TriadicCube d → ℝ := fun R =>
    cubeAverage R (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q)
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      vecNormSq
          (cubeAverageVec R
            (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q)) ≤
        2 * M * E R := by
    intro R hR
    let w :=
      JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
        a ha Q hR p q
    have hraw :=
      Ch02.vecNormSq_averageGradient_le_matrixNorm_sigmaStarInvCoarse_mul_variationEnergyValue
        (Ch02.cubeDomain R) (F.coeffOn R) w
    have havg :
        Ch02.averageGradient (Ch02.cubeDomain R) (F.coeffOn R) w =
          cubeAverageVec R
            (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q) := by
      simpa [F, w] using
        averageGradient_parentResponseSolutionOnDependentFamilyRestrictedToCube_eq_cubeAverageVec
          a ha Q hR p q
    have henergy :
        Ch02.variationEnergyValue (Ch02.cubeDomain R) (F.coeffOn R) w =
          2 * E R := by
      simpa [F, E, w] using
        variationEnergyValue_parentResponseSolutionOnDependentFamilyRestrictedToCube_eq
          a ha Q hR p q
    have hlocal :
        vecNormSq
            (cubeAverageVec R
              (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q)) ≤
          2 * Ch02.coarseSigmaStarInvMatrixNorm R F * E R := by
      simpa [havg, henergy, Ch02.coarseSigmaStarInvMatrixNorm, mul_assoc,
        mul_comm, mul_left_comm] using hraw
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have hcoarse : Ch02.coarseSigmaStarInvMatrixNorm R F ≤ M := by
      simpa [M] using
        Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale
          F hRscale
    have hE_nonneg : 0 ≤ E R := by
      dsimp [E]
      have hsubset : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
      have hle : volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
        simpa [volumeMeasureOn] using
          MeasureTheory.Measure.restrict_mono_set volume hsubset
      exact cubeAverage_nonneg_of_ae_nonneg <|
        (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube_ae_nonneg_cubeSet
          Q (F.coeffOn Q) p q).filter_mono (MeasureTheory.ae_mono hle)
    have hreplace :
        2 * Ch02.coarseSigmaStarInvMatrixNorm R F * E R ≤ 2 * M * E R := by
      have hmul : Ch02.coarseSigmaStarInvMatrixNorm R F * E R ≤ M * E R :=
        mul_le_mul_of_nonneg_right hcoarse hE_nonneg
      nlinarith
    exact hlocal.trans hreplace
  have hdesc := descendantsAverage_le_descendantsAverage Q j hpoint
  calc
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (cubeAverageVec R
              (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q)))
        ≤ descendantsAverage Q j (fun R => 2 * M * E R) := hdesc
    _ = 2 * M * descendantsAverage Q j E := by
          rw [descendantsAverage_mul_left]
    _ = 2 * M * Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q := by
          rw [JUpperBoundWeakNorms.descendantsAverage_cubeAverage_topHalfEnergyOnCube_eq_responseJOnCube]

private theorem descendantsAverage_parentFlux_le_maxB_mul_responseJ
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (cubeAverageVec R
              (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q))) ≤
      2 * Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) F *
        Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q := by
  intro F
  let M := Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) F
  let E : TriadicCube d → ℝ := fun R =>
    cubeAverage R (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q)
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      vecNormSq
          (cubeAverageVec R
            (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q)) ≤
        2 * M * E R := by
    intro R hR
    let w :=
      JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
        a ha Q hR p q
    have hraw :=
      Ch02.vecNormSq_averageFlux_le_matrixNorm_bCoarse_mul_variationEnergyValue
        (Ch02.cubeDomain R) (F.coeffOn R) w
    have havg :
        Ch02.averageFlux (Ch02.cubeDomain R) (F.coeffOn R) w =
          cubeAverageVec R
            (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q) := by
      simpa [F, w] using
        averageFlux_parentResponseSolutionOnDependentFamilyRestrictedToCube_eq_cubeAverageVec
          a ha Q hR p q
    have henergy :
        Ch02.variationEnergyValue (Ch02.cubeDomain R) (F.coeffOn R) w =
          2 * E R := by
      simpa [F, E, w] using
        variationEnergyValue_parentResponseSolutionOnDependentFamilyRestrictedToCube_eq
          a ha Q hR p q
    have hlocal :
        vecNormSq
            (cubeAverageVec R
              (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q)) ≤
          2 * Ch02.coarseBMatrixNorm R F * E R := by
      simpa [havg, henergy, Ch02.coarseBMatrixNorm, mul_assoc, mul_comm,
        mul_left_comm] using hraw
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have hcoarse : Ch02.coarseBMatrixNorm R F ≤ M := by
      simpa [M] using
        Ch02.coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale_of_mem_descendantsAtScale
          F hRscale
    have hE_nonneg : 0 ≤ E R := by
      dsimp [E]
      have hsubset : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
      have hle : volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
        simpa [volumeMeasureOn] using
          MeasureTheory.Measure.restrict_mono_set volume hsubset
      exact cubeAverage_nonneg_of_ae_nonneg <|
        (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube_ae_nonneg_cubeSet
          Q (F.coeffOn Q) p q).filter_mono (MeasureTheory.ae_mono hle)
    have hreplace : 2 * Ch02.coarseBMatrixNorm R F * E R ≤ 2 * M * E R := by
      have hmul : Ch02.coarseBMatrixNorm R F * E R ≤ M * E R :=
        mul_le_mul_of_nonneg_right hcoarse hE_nonneg
      nlinarith
    exact hlocal.trans hreplace
  have hdesc := descendantsAverage_le_descendantsAverage Q j hpoint
  calc
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (cubeAverageVec R
              (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q)))
        ≤ descendantsAverage Q j (fun R => 2 * M * E R) := hdesc
    _ = 2 * M * descendantsAverage Q j E := by
          rw [descendantsAverage_mul_left]
    _ = 2 * M * Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q := by
          rw [JUpperBoundWeakNorms.descendantsAverage_cubeAverage_topHalfEnergyOnCube_eq_responseJOnCube]

theorem descendantsAverage_parentGradient_le_lambdaSqCoeffField_responseJ
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) {s' : ℝ} (hs' : 0 < s') (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (cubeAverageVec R
              (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q))) ≤
      ((2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
          Real.rpow (3 : ℝ) (s' * (j : ℝ))) ^ 2 *
        Ch04.restrictionResponseJObservableCubeSet Q p q a := by
  intro F
  let A := descendantsAverage Q j
        (fun R =>
          vecNormSq
            (cubeAverageVec R
              (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q)))
  let M := Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) F
  let D := Ch04.restrictionResponseJObservableCubeSet Q p q a
  let lamInv := (Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹
  let W := Real.rpow (3 : ℝ) (2 * s' * (j : ℝ))
  have hbase : A ≤ 2 * M * D := by
    have h :=
      descendantsAverage_parentGradient_le_maxSigmaStarInv_mul_responseJ a ha Q j p q
    simpa [A, M, D, F,
      JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
        a ha Q p q] using h
  have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  have hlocM : M ≤ W * lamInv := by
    have h1 :
        M ≤
          Ch02.maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (j : ℤ))
            s' (.finite 1) F := by
      simpa [M] using
        Ch02.maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv
          Q F hk hs' (by simp [Ch02.MultiscaleExponent.IsAdmissible])
    have h2 :
        Ch02.maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (j : ℤ))
            s' (.finite 1) F ≤
          Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) s' *
            (Ch02.lambdaSq Q s' (.finite 1) F)⁻¹ :=
      Ch02.maxDescendant_lambdaSq_inv_le Q F hk hs'
        (by simp [Ch02.MultiscaleExponent.IsAdmissible])
    calc
      M ≤
          Ch02.maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (j : ℤ))
            s' (.finite 1) F := h1
      _ ≤ Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) s' *
            (Ch02.lambdaSq Q s' (.finite 1) F)⁻¹ := h2
      _ = W * lamInv := by
            rw [multiscaleDescendantWeight_sub_nat]
            simp [W, lamInv, F, Ch04.lambdaSqCoeffField, ha]
  have hD_nonneg : 0 ≤ D := by
    change 0 ≤ Ch04.restrictionResponseJObservableCubeSet Q p q a
    rw [← JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
      a ha Q p q]
    exact Ch02.responseJ_nonneg (Ch02.cubeDomain Q) (F.coeffOn Q) p q
  have hlamInv_nonneg : 0 ≤ lamInv := by
    dsimp [lamInv]
    exact inv_nonneg.mpr <|
      Ch04.lambdaSqCoeffField_finite_nonneg Q a hs' (by norm_num : (1 : ℝ) ≤ 1)
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hA1 : A ≤ 2 * (W * lamInv) * D := by
    have hmul : M * D ≤ (W * lamInv) * D :=
      mul_le_mul_of_nonneg_right hlocM hD_nonneg
    nlinarith
  have hfactor_nonneg : 0 ≤ W * lamInv * D :=
    mul_nonneg (mul_nonneg hW_nonneg hlamInv_nonneg) hD_nonneg
  have hrhs_eq :
      ((2 * Real.sqrt lamInv) * Real.rpow (3 : ℝ) (s' * (j : ℝ))) ^ 2 * D =
        4 * (W * lamInv) * D := by
    have hpow : (Real.rpow (3 : ℝ) (s' * (j : ℝ))) ^ 2 = W := by
      dsimp [W]
      calc
        (Real.rpow (3 : ℝ) (s' * (j : ℝ))) ^ 2
            = Real.rpow (3 : ℝ) (s' * (j : ℝ) * 2) := by
              simpa [Real.rpow_natCast] using
                (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
                  (s' * (j : ℝ)) (2 : ℝ)).symm
        _ = Real.rpow (3 : ℝ) (2 * s' * (j : ℝ)) := by
              ring_nf
    rw [mul_pow, mul_pow, Real.sq_sqrt hlamInv_nonneg, hpow]
    ring
  rw [hrhs_eq]
  nlinarith [hA1, hfactor_nonneg]

theorem descendantsAverage_parentFlux_le_LambdaSqCoeffField_responseJ
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) {t' : ℝ} (ht' : 0 < t') (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (cubeAverageVec R
              (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q))) ≤
      ((2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
          Real.rpow (3 : ℝ) (t' * (j : ℝ))) ^ 2 *
        Ch04.restrictionResponseJObservableCubeSet Q p q a := by
  intro F
  let A := descendantsAverage Q j
        (fun R =>
          vecNormSq
            (cubeAverageVec R
              (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q)))
  let M := Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) F
  let D := Ch04.restrictionResponseJObservableCubeSet Q p q a
  let Lam := Ch04.LambdaSqCoeffField Q t' (.finite 1) a
  let W := Real.rpow (3 : ℝ) (2 * t' * (j : ℝ))
  have hbase : A ≤ 2 * M * D := by
    have h := descendantsAverage_parentFlux_le_maxB_mul_responseJ a ha Q j p q
    simpa [A, M, D, F,
      JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
        a ha Q p q] using h
  have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  have hlocM : M ≤ W * Lam := by
    have h1 :
        M ≤
          Ch02.maxDescendantUpperEllipticityAtScale Q (Q.scale - (j : ℤ))
            t' (.finite 1) F := by
      simpa [M] using
        Ch02.maxDescendant_b_le_maxDescendant_LambdaSq
          Q F hk ht' (by simp [Ch02.MultiscaleExponent.IsAdmissible])
    have h2 :
        Ch02.maxDescendantUpperEllipticityAtScale Q (Q.scale - (j : ℤ))
            t' (.finite 1) F ≤
          Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) t' *
            Ch02.LambdaSq Q t' (.finite 1) F :=
      Ch02.maxDescendant_LambdaSq_le Q F hk ht'
        (by simp [Ch02.MultiscaleExponent.IsAdmissible])
    calc
      M ≤
          Ch02.maxDescendantUpperEllipticityAtScale Q (Q.scale - (j : ℤ))
            t' (.finite 1) F := h1
      _ ≤ Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) t' *
            Ch02.LambdaSq Q t' (.finite 1) F := h2
      _ = W * Lam := by
            rw [multiscaleDescendantWeight_sub_nat]
            simp [W, Lam, F, Ch04.LambdaSqCoeffField, ha]
  have hD_nonneg : 0 ≤ D := by
    change 0 ≤ Ch04.restrictionResponseJObservableCubeSet Q p q a
    rw [← JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
      a ha Q p q]
    exact Ch02.responseJ_nonneg (Ch02.cubeDomain Q) (F.coeffOn Q) p q
  have hLam_nonneg : 0 ≤ Lam := by
    dsimp [Lam]
    exact Ch04.LambdaSqCoeffField_finite_nonneg Q a ht'
      (by norm_num : (1 : ℝ) ≤ 1)
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hA1 : A ≤ 2 * (W * Lam) * D := by
    have hmul : M * D ≤ (W * Lam) * D :=
      mul_le_mul_of_nonneg_right hlocM hD_nonneg
    nlinarith
  have hfactor_nonneg : 0 ≤ W * Lam * D :=
    mul_nonneg (mul_nonneg hW_nonneg hLam_nonneg) hD_nonneg
  have hrhs_eq :
      ((2 * Real.sqrt Lam) * Real.rpow (3 : ℝ) (t' * (j : ℝ))) ^ 2 * D =
        4 * (W * Lam) * D := by
    have hpow : (Real.rpow (3 : ℝ) (t' * (j : ℝ))) ^ 2 = W := by
      dsimp [W]
      calc
        (Real.rpow (3 : ℝ) (t' * (j : ℝ))) ^ 2
            = Real.rpow (3 : ℝ) (t' * (j : ℝ) * 2) := by
              simpa [Real.rpow_natCast] using
                (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
                  (t' * (j : ℝ)) (2 : ℝ)).symm
        _ = Real.rpow (3 : ℝ) (2 * t' * (j : ℝ)) := by
              ring_nf
    rw [mul_pow, mul_pow, Real.sq_sqrt hLam_nonneg, hpow]
    ring
  rw [hrhs_eq]
  nlinarith [hA1, hfactor_nonneg]

theorem gradientLowScaleDepthSum_le_lambdaSqCoeffField_responseJ
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (N L : ℕ) {s s' : ℝ}
    (hs' : 0 < s') (hgap : 0 < s - s') (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    (∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
        cubeBesovNegativeVectorDepthSeminorm Q s
          (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q) j) ≤
      (2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
        (Real.rpow (3 : ℝ) (-(s - s') * (L : ℝ)) *
          (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹) *
          Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a) := by
  intro F
  let low : ℕ → Prop := fun j => ¬ j < L
  let C := 2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)
  let J := Ch04.restrictionResponseJObservableCubeSet Q p q a
  have hshift :
      (∑ j ∈ (Finset.range (N + 1)).filter low,
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt
              (descendantsAverage Q j fun R =>
                vecNormSq
                  (cubeAverageVec R
                    (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q)))) ≤
        C *
          ∑ j ∈ (Finset.range (N + 1)).filter low,
            Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) * Real.sqrt J := by
    refine
      sum_filter_triadicDepthWeight_mul_sqrt_descendantsAverage_vecNormSq_le_const_mul_shifted_weighted_sqrt
        Q s s' C N low
        (fun _j R =>
          cubeAverageVec R
            (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q))
        (fun _j => J) ?_ ?_
    · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    · intro j _hj
      simpa [C, J, F] using
        descendantsAverage_parentGradient_le_lambdaSqCoeffField_responseJ a ha Q j hs' p q
  have hgeom :
      (∑ j ∈ (Finset.range (N + 1)).filter low,
          Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) * Real.sqrt J) ≤
        (Real.rpow (3 : ℝ) (-(s - s') * (L : ℝ)) *
          (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹) * Real.sqrt J := by
    have htail :=
      sum_range_filter_not_lt_triadicDepthWeight_le_geometric_tail
        (s - s') N L hgap
    calc
      (∑ j ∈ (Finset.range (N + 1)).filter low,
          Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) * Real.sqrt J)
          =
        (∑ j ∈ (Finset.range (N + 1)).filter low,
          Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ))) * Real.sqrt J := by
        rw [Finset.sum_mul]
      _ ≤
        (Real.rpow (3 : ℝ) (-(s - s') * (L : ℝ)) *
          (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹) * Real.sqrt J :=
        mul_le_mul_of_nonneg_right htail (Real.sqrt_nonneg J)
  have hC_nonneg : 0 ≤ C := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hmain := hshift.trans (mul_le_mul_of_nonneg_left hgeom hC_nonneg)
  simpa [cubeBesovNegativeVectorDepthSeminorm, cubeBesovNegativeVectorDepthAverage,
    low, C, J, F, mul_assoc] using hmain

theorem fluxLowScaleDepthSum_le_LambdaSqCoeffField_responseJ
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (N L : ℕ) {t t' : ℝ}
    (ht' : 0 < t') (hgap : 0 < t - t') (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    (∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
        cubeBesovNegativeVectorDepthSeminorm Q t
          (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q) j) ≤
      (2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
        (Real.rpow (3 : ℝ) (-(t - t') * (L : ℝ)) *
          (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹) *
          Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a) := by
  intro F
  let low : ℕ → Prop := fun j => ¬ j < L
  let C := 2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)
  let J := Ch04.restrictionResponseJObservableCubeSet Q p q a
  have hshift :
      (∑ j ∈ (Finset.range (N + 1)).filter low,
          Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
            Real.sqrt
              (descendantsAverage Q j fun R =>
                vecNormSq
                  (cubeAverageVec R
                    (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q)))) ≤
        C *
          ∑ j ∈ (Finset.range (N + 1)).filter low,
            Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) * Real.sqrt J := by
    refine
      sum_filter_triadicDepthWeight_mul_sqrt_descendantsAverage_vecNormSq_le_const_mul_shifted_weighted_sqrt
        Q t t' C N low
        (fun _j R =>
          cubeAverageVec R
            (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q))
        (fun _j => J) ?_ ?_
    · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    · intro j _hj
      simpa [C, J, F] using
        descendantsAverage_parentFlux_le_LambdaSqCoeffField_responseJ a ha Q j ht' p q
  have hgeom :
      (∑ j ∈ (Finset.range (N + 1)).filter low,
          Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) * Real.sqrt J) ≤
        (Real.rpow (3 : ℝ) (-(t - t') * (L : ℝ)) *
          (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹) * Real.sqrt J := by
    have htail :=
      sum_range_filter_not_lt_triadicDepthWeight_le_geometric_tail
        (t - t') N L hgap
    calc
      (∑ j ∈ (Finset.range (N + 1)).filter low,
          Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) * Real.sqrt J)
          =
        (∑ j ∈ (Finset.range (N + 1)).filter low,
          Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ))) * Real.sqrt J := by
        rw [Finset.sum_mul]
      _ ≤
        (Real.rpow (3 : ℝ) (-(t - t') * (L : ℝ)) *
          (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹) * Real.sqrt J :=
        mul_le_mul_of_nonneg_right htail (Real.sqrt_nonneg J)
  have hC_nonneg : 0 ≤ C := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hmain := hshift.trans (mul_le_mul_of_nonneg_left hgeom hC_nonneg)
  simpa [cubeBesovNegativeVectorDepthSeminorm, cubeBesovNegativeVectorDepthAverage,
    low, C, J, F, mul_assoc] using hmain

end

end WeakNormsMaximizer
end Section53
end Ch05
end Book
end Homogenization
