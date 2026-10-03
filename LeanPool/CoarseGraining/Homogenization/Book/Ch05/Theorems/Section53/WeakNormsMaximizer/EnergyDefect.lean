/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.Splitting
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.FiveTermSplit
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.CoarseGrainingEstimates
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesPositiveQTwo

/-! # Energy Defect -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace WeakNormsMaximizer

/-!
# Response-defect identifications for the weak-norm maximizer lemma

This file connects the defect term used in the second Section 5.3 lemma to
the deterministic response partition defect already developed for the first
Section 5.3 lemma.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- For the Ch4 dependent coefficient family, the descendant average of Ch4
response observables minus the parent response is the raw deterministic
partition defect. -/
theorem descendantsAverage_restrictionResponseJObservableCubeSet_sub_eq_responseJPartitionDefectOnDependentFamily
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    descendantsAverage Q j (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) -
        Ch04.restrictionResponseJObservableCubeSet Q p q a =
      JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        Q j p q := by
  unfold JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
    JUpperBoundWeakNorms.childResponseJAverageOnFamilyAtDepth
  congr 1
  · exact JUpperBoundWeakNorms.descendantsAverage_congr_of_eq_on_descendants Q j
      (by
        intro R _hR
        exact
          (JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
            a ha R p q).symm)
  · exact
      (JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
        a ha Q p q).symm

/-- The scale-indexed defect in the weak-norm maximizer RHS is the deterministic
response partition defect for the dependent coefficient family. -/
theorem responseDefectAverageAtScale_eq_responseJPartitionDefectOnDependentFamily
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m n : ℤ) (p q : Vec d) :
    responseDefectAverageAtScale m n p q a =
      JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (originCube d m) (Int.toNat (m - n)) p q := by
  simpa [responseDefectAverageAtScale] using
    descendantsAverage_restrictionResponseJObservableCubeSet_sub_eq_responseJPartitionDefectOnDependentFamily
      a ha (originCube d m) (Int.toNat (m - n)) p q

/-- Deterministic nonnegativity of the raw response partition defect. -/
theorem responseJPartitionDefectOnFamilyAtDepth_nonneg
    {d : ℕ} [NeZero d] (F : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    0 ≤ JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q := by
  unfold JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
  exact sub_nonneg.mpr
    (JUpperBoundWeakNorms.responseJOnCube_le_childResponseJAverageOnFamilyAtDepth
      F Q j p q)

/-- Deterministic nonnegativity of the weak-norm maximizer response-defect
term on the a.e.-elliptic support. -/
theorem responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m n : ℤ) (p q : Vec d) :
    0 ≤ responseDefectAverageAtScale m n p q a := by
  rw [responseDefectAverageAtScale_eq_responseJPartitionDefectOnDependentFamily a ha]
  exact responseJPartitionDefectOnFamilyAtDepth_nonneg
    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
    (originCube d m) (Int.toNat (m - n)) p q

/-- The Ch4 gradient average mismatch is the cube average of the raw
parent-minus-child canonical maximizer gradients. -/
theorem cubeAverageVec_parentChildCanonicalGradientMismatchOnDependentFamily_eq_ch04
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    cubeAverageVec R
        (fun x =>
          JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q x -
            JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube R (F.coeffOn R) p q x) =
      Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
        Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun := by
  intro F
  let parentGrad :=
    JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q
  let childGrad :=
    JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube R (F.coeffOn R) p q
  have hparent_mem :
      MemLp parentGrad (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    simpa [F, parentGrad] using
      JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube_memLp_descendant
        Q R (F.coeffOn Q) hR p q
  have hchild_mem :
      MemLp childGrad (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    have hRR : R ∈ descendantsAtDepth R 0 := by
      simp [descendantsAtDepth_zero]
    simpa [F, childGrad] using
      JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube_memLp_descendant
        R R (F.coeffOn R) hRR p q
  have hparent_avg :
      Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun =
        cubeAverageVec R parentGrad := by
    simpa [F, parentGrad, JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube,
      JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube] using!
      Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
        a ha hR p q
  have hchild_avg :
      Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun =
        cubeAverageVec R childGrad := by
    have hRR : R ∈ descendantsAtDepth R 0 := by
      simp [descendantsAtDepth_zero]
    simpa [F, childGrad, JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube,
      JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube] using!
      Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
        a ha hRR p q
  calc
    cubeAverageVec R (fun x => parentGrad x - childGrad x)
        = cubeAverageVec R parentGrad - cubeAverageVec R childGrad := by
            exact cubeAverageVec_sub_memLp R parentGrad childGrad hparent_mem hchild_mem
    _ = Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
          Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun := by
          rw [← hparent_avg, ← hchild_avg]

/-- The Ch4 flux average mismatch is the cube average of the raw
parent-minus-child canonical maximizer fluxes. -/
theorem cubeAverageVec_parentChildCanonicalFluxMismatchOnDependentFamily_eq_ch04
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    cubeAverageVec R
        (fun x =>
          JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q x -
            JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube R (F.coeffOn R) p q x) =
      Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
        Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun := by
  intro F
  let parentFlux :=
    JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q
  let childFlux :=
    JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube R (F.coeffOn R) p q
  have hparent_mem :
      MemLp parentFlux (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    simpa [F, parentFlux] using
      JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube_memLp_descendant
        Q R (F.coeffOn Q) hR p q
  have hchild_mem :
      MemLp childFlux (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    have hRR : R ∈ descendantsAtDepth R 0 := by
      simp [descendantsAtDepth_zero]
    simpa [F, childFlux] using
      JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube_memLp_descendant
        R R (F.coeffOn R) hRR p q
  have hparent_avg :
      Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun =
        cubeAverageVec R parentFlux := by
    simpa [F, parentFlux, JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube,
      JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube,
      JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube] using!
      Ch04.canonicalScalarResponseFluxAverageCubeSet_eq_cubeAverageVec_canonicalMaximizerFlux
        a ha hR p q
  have hchild_avg :
      Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun =
        cubeAverageVec R childFlux := by
    have hRR : R ∈ descendantsAtDepth R 0 := by
      simp [descendantsAtDepth_zero]
    simpa [F, childFlux, JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube,
      JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube,
      JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube] using!
      Ch04.canonicalScalarResponseFluxAverageCubeSet_eq_cubeAverageVec_canonicalMaximizerFlux
        a ha hRR p q
  calc
    cubeAverageVec R (fun x => parentFlux x - childFlux x)
        = cubeAverageVec R parentFlux - cubeAverageVec R childFlux := by
            exact cubeAverageVec_sub_memLp R parentFlux childFlux hparent_mem hchild_mem
    _ = Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
          Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun := by
          rw [← hparent_avg, ← hchild_avg]

/-- The parent-child canonical difference as an honest Chapter 2 solution on
the child cube.  This is the deterministic object whose variation energy is
the additivity defect. -/
noncomputable def parentChildCanonicalDifferenceSolutionOnDependentFamily
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    Ch02.Solution (Ch02.cubeDomain R)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let parent :=
    JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
      a ha Q hR p q
  let child :=
    JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube R (F.coeffOn R) p q
  have hparent_int :
      ∀ φ : H10Function (openCubeSet R),
        IntegrableOn
          (fun x =>
            vecDot
              (matVecMul ((F.coeffOn R).toCoeffField x) (parent.toH1.grad x))
              (φ.toH1Function.grad x))
          (openCubeSet R) volume := by
    intro φ
    simpa [parent, Ch02.cubeDomain_coe] using!
      integrableOn_vecDot_of_memVectorL2
        (Ch02.Solution.flux_memVectorL2 parent)
        φ.toH1Function.grad_memVectorL2
  have hchild_int :
      ∀ φ : H10Function (openCubeSet R),
        IntegrableOn
          (fun x =>
            vecDot
              (matVecMul ((F.coeffOn R).toCoeffField x) (child.toH1.grad x))
              (φ.toH1Function.grad x))
          (openCubeSet R) volume := by
    intro φ
    simpa [child, Ch02.cubeDomain_coe] using
      integrableOn_vecDot_of_memVectorL2
        (Ch02.Solution.flux_memVectorL2 child)
        φ.toH1Function.grad_memVectorL2
  exact AHarmonicFunction.addSMulOfIntegrable parent child hparent_int hchild_int (-1)

/-- The gradient of the parent-child difference solution is the raw
parent-minus-child canonical maximizer gradient. -/
theorem parentChildCanonicalDifferenceSolutionOnDependentFamily_grad
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    (parentChildCanonicalDifferenceSolutionOnDependentFamily a ha Q hR p q).toH1.grad =
      fun x =>
        JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q x -
          JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube R
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)
            p q x := by
  have hgrad :
      (parentChildCanonicalDifferenceSolutionOnDependentFamily a ha Q hR p q).toH1.grad =
        (JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
              a ha Q hR p q).toH1.grad +
          (-1 : ℝ) •
            (JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube R
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)
                p q).toH1.grad :=
    rfl
  funext x i
  rw [hgrad]
  simp only [JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube_grad,
    JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube,
    Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, sub_eq_add_neg]
  ring

/-- The averaged gradient of the parent-child difference solution is the raw
parent-minus-child gradient cube average. -/
theorem averageGradient_parentChildCanonicalDifferenceSolutionOnDependentFamily_eq_cubeAverageVec
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    Ch02.averageGradient (Ch02.cubeDomain R) (F.coeffOn R)
        (parentChildCanonicalDifferenceSolutionOnDependentFamily a ha Q hR p q) =
      cubeAverageVec R
        (fun x =>
          JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q x -
            JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube R (F.coeffOn R) p q x) := by
  intro F
  ext i
  rw [Ch02.averageGradient, Ch02.averageVec,
    JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
  simp [cubeAverageVec, F,
    parentChildCanonicalDifferenceSolutionOnDependentFamily_grad]

/-- The averaged flux of the parent-child difference solution is the raw
parent-minus-child flux cube average. -/
theorem averageFlux_parentChildCanonicalDifferenceSolutionOnDependentFamily_eq_cubeAverageVec
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    Ch02.averageFlux (Ch02.cubeDomain R) (F.coeffOn R)
        (parentChildCanonicalDifferenceSolutionOnDependentFamily a ha Q hR p q) =
      cubeAverageVec R
        (fun x =>
          JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q x -
            JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube R (F.coeffOn R) p q x) := by
  intro F
  ext i
  rw [Ch02.averageFlux, Ch02.averageVec,
    JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
  apply cubeAverage_eq_of_eq_on_cubeSet
  intro x _hx
  simp [parentChildCanonicalDifferenceSolutionOnDependentFamily_grad,
    JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube, F, sub_eq_add_neg,
    matVecMul_add, matVecMul_neg]

/-- The variation energy of the parent-child difference solution is twice the
local additivity half-energy. -/
theorem variationEnergyValue_parentChildCanonicalDifferenceSolutionOnDependentFamily_eq
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    Ch02.variationEnergyValue (Ch02.cubeDomain R) (F.coeffOn R)
        (parentChildCanonicalDifferenceSolutionOnDependentFamily a ha Q hR p q) =
      2 * cubeAverage R
        (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q) := by
  intro F
  rw [Ch02.variationEnergyValue,
    JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
  have hpoint :
      Ch02.variationEnergyIntegrand (Ch02.cubeDomain R) (F.coeffOn R)
          (parentChildCanonicalDifferenceSolutionOnDependentFamily a ha Q hR p q) =
        fun x =>
          2 *
            JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q x := by
    funext x
    simp [Ch02.variationEnergyIntegrand,
      parentChildCanonicalDifferenceSolutionOnDependentFamily_grad,
      JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube, F]
  rw [hpoint, cubeAverage_const_mul]

/-- One-child averaged parent-child gradient mismatch is controlled by the
local `σ_*^{-1}` norm and the additivity defect energy. -/
theorem vecNormSq_cubeAverageVec_parentChildCanonicalGradientMismatchOnDependentFamily_le
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    vecNormSq
        (cubeAverageVec R
          (fun x =>
            JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q x -
              JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube R (F.coeffOn R) p q x)) ≤
      2 * Ch02.coarseSigmaStarInvMatrixNorm R F *
        cubeAverage R
          (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q) := by
  intro F
  let w :=
    parentChildCanonicalDifferenceSolutionOnDependentFamily a ha Q hR p q
  have hraw :=
    Ch02.vecNormSq_averageGradient_le_matrixNorm_sigmaStarInvCoarse_mul_variationEnergyValue
      (Ch02.cubeDomain R) (F.coeffOn R) w
  have havg :
      Ch02.averageGradient (Ch02.cubeDomain R) (F.coeffOn R) w =
        cubeAverageVec R
          (fun x =>
            JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q x -
              JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube R (F.coeffOn R) p q x) := by
    simpa [F, w] using
      averageGradient_parentChildCanonicalDifferenceSolutionOnDependentFamily_eq_cubeAverageVec
        a ha Q hR p q
  have henergy :
      Ch02.variationEnergyValue (Ch02.cubeDomain R) (F.coeffOn R) w =
        2 * cubeAverage R
          (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q) := by
    simpa [F, w] using
      variationEnergyValue_parentChildCanonicalDifferenceSolutionOnDependentFamily_eq
        a ha Q hR p q
  simpa [havg, henergy, Ch02.coarseSigmaStarInvMatrixNorm, mul_assoc, mul_left_comm,
    mul_comm] using hraw

/-- One-child averaged parent-child flux mismatch is controlled by the local
`b` norm and the additivity defect energy. -/
theorem vecNormSq_cubeAverageVec_parentChildCanonicalFluxMismatchOnDependentFamily_le
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    vecNormSq
        (cubeAverageVec R
          (fun x =>
            JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q x -
              JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube R (F.coeffOn R) p q x)) ≤
      2 * Ch02.coarseBMatrixNorm R F *
        cubeAverage R
          (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q) := by
  intro F
  let w :=
    parentChildCanonicalDifferenceSolutionOnDependentFamily a ha Q hR p q
  have hraw :=
    Ch02.vecNormSq_averageFlux_le_matrixNorm_bCoarse_mul_variationEnergyValue
      (Ch02.cubeDomain R) (F.coeffOn R) w
  have havg :
      Ch02.averageFlux (Ch02.cubeDomain R) (F.coeffOn R) w =
        cubeAverageVec R
          (fun x =>
            JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q x -
              JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube R (F.coeffOn R) p q x) := by
    simpa [F, w] using
      averageFlux_parentChildCanonicalDifferenceSolutionOnDependentFamily_eq_cubeAverageVec
        a ha Q hR p q
  have henergy :
      Ch02.variationEnergyValue (Ch02.cubeDomain R) (F.coeffOn R) w =
        2 * cubeAverage R
          (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q) := by
    simpa [F, w] using
      variationEnergyValue_parentChildCanonicalDifferenceSolutionOnDependentFamily_eq
        a ha Q hR p q
  simpa [havg, henergy, Ch02.coarseBMatrixNorm, mul_assoc, mul_left_comm,
    mul_comm] using hraw

private theorem cubeAverage_nonneg_of_ae_nonneg {d : ℕ}
    {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : ∀ᵐ x ∂volume.restrict (cubeSet Q), 0 ≤ f x) :
    0 ≤ cubeAverage Q f := by
  unfold cubeAverage
  refine mul_nonneg (inv_nonneg.mpr (le_of_lt (cubeVolume_pos Q))) ?_
  exact MeasureTheory.integral_nonneg_of_ae hf

private theorem cubeAverage_additivityDiffHalfEnergyDensityOnDependentFamily_nonneg
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (_hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    0 ≤ cubeAverage R
      (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q) := by
  intro F
  have hEllOpen :
      IsAEEllipticFieldOn (F.coeffOn R).lam (F.coeffOn R).Lam
        (openCubeSet R) (F.coeffOn R).toCoeffField := by
    simpa [F, Ch02.cubeDomain_coe] using
      JUpperBoundWeakNorms.ch02_coeffOn_isAEEllipticFieldOn (F.coeffOn R)
  have hEllCube :
      IsAEEllipticFieldOn (F.coeffOn R).lam (F.coeffOn R).Lam
        (cubeSet R) (F.coeffOn R).toCoeffField :=
    hEllOpen.cubeSet_of_openCubeSet
  exact cubeAverage_nonneg_of_ae_nonneg <|
    hEllCube.ae_isEllipticMatrix.mono fun x hx =>
      JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube_nonneg_of_isEllipticMatrix
        F Q R p q x hx

/-- At one depth, the Ch4 gradient parent-child mismatch average is controlled
by the max descendant `σ_*^{-1}` norm and the response partition defect. -/
theorem descendantsAverage_ch04GradientMismatch_le_maxSigmaStarInv_mul_responseDefect
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun)) ≤
      2 * Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) F *
        JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q := by
  intro F
  let M := Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) F
  let E : TriadicCube d → ℝ := fun R =>
    cubeAverage R
      (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q)
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq
            (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun) ≤
          2 * M * E R := by
    intro R hR
    have hEq :
        Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
            Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun =
          cubeAverageVec R
            (fun x =>
              JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q x -
                JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube R (F.coeffOn R) p q x) := by
      simpa [F] using
        (cubeAverageVec_parentChildCanonicalGradientMismatchOnDependentFamily_eq_ch04
          a ha hR p q).symm
    have hraw :=
      vecNormSq_cubeAverageVec_parentChildCanonicalGradientMismatchOnDependentFamily_le
        a ha Q hR p q
    have hlocal :
        vecNormSq
            (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun) ≤
          2 * Ch02.coarseSigmaStarInvMatrixNorm R F * E R := by
      simpa [F, E, hEq] using hraw
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have hcoarse :
        Ch02.coarseSigmaStarInvMatrixNorm R F ≤ M := by
      simpa [M] using
        Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale
          F hRscale
    have hE_nonneg : 0 ≤ E R := by
      simpa [F, E] using
        cubeAverage_additivityDiffHalfEnergyDensityOnDependentFamily_nonneg
          a ha Q hR p q
    have hreplace :
        2 * Ch02.coarseSigmaStarInvMatrixNorm R F * E R ≤ 2 * M * E R := by
      have hmul :
          Ch02.coarseSigmaStarInvMatrixNorm R F * E R ≤ M * E R :=
        mul_le_mul_of_nonneg_right hcoarse hE_nonneg
      nlinarith
    exact hlocal.trans hreplace
  have hdesc := descendantsAverage_le_descendantsAverage Q j hpoint
  calc
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun))
        ≤ descendantsAverage Q j (fun R => 2 * M * E R) := hdesc
    _ = 2 * M * descendantsAverage Q j E := by
          rw [descendantsAverage_mul_left]
    _ =
        2 * M *
          JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q := by
          rw [JUpperBoundWeakNorms.descendantsAverage_additivityDiffHalfEnergyOnDependentFamily_eq_responseJPartitionDefectOnFamilyAtDepth
            a ha Q j p q]

/-- At one depth, the Ch4 flux parent-child mismatch average is controlled by
the max descendant `b` norm and the response partition defect. -/
theorem descendantsAverage_ch04FluxMismatch_le_maxB_mul_responseDefect
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun)) ≤
      2 * Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) F *
        JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q := by
  intro F
  let M := Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) F
  let E : TriadicCube d → ℝ := fun R =>
    cubeAverage R
      (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q)
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq
            (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun) ≤
          2 * M * E R := by
    intro R hR
    have hEq :
        Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
            Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun =
          cubeAverageVec R
            (fun x =>
              JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q (F.coeffOn Q) p q x -
                JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube R (F.coeffOn R) p q x) := by
      simpa [F] using
        (cubeAverageVec_parentChildCanonicalFluxMismatchOnDependentFamily_eq_ch04
          a ha hR p q).symm
    have hraw :=
      vecNormSq_cubeAverageVec_parentChildCanonicalFluxMismatchOnDependentFamily_le
        a ha Q hR p q
    have hlocal :
        vecNormSq
            (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun) ≤
          2 * Ch02.coarseBMatrixNorm R F * E R := by
      simpa [F, E, hEq] using hraw
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have hcoarse :
        Ch02.coarseBMatrixNorm R F ≤ M := by
      simpa [M] using
        Ch02.coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale_of_mem_descendantsAtScale
          F hRscale
    have hE_nonneg : 0 ≤ E R := by
      simpa [F, E] using
        cubeAverage_additivityDiffHalfEnergyDensityOnDependentFamily_nonneg
          a ha Q hR p q
    have hreplace :
        2 * Ch02.coarseBMatrixNorm R F * E R ≤ 2 * M * E R := by
      have hmul : Ch02.coarseBMatrixNorm R F * E R ≤ M * E R :=
        mul_le_mul_of_nonneg_right hcoarse hE_nonneg
      nlinarith
    exact hlocal.trans hreplace
  have hdesc := descendantsAverage_le_descendantsAverage Q j hpoint
  calc
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun))
        ≤ descendantsAverage Q j (fun R => 2 * M * E R) := hdesc
    _ = 2 * M * descendantsAverage Q j E := by
          rw [descendantsAverage_mul_left]
    _ =
        2 * M *
          JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q := by
          rw [JUpperBoundWeakNorms.descendantsAverage_additivityDiffHalfEnergyOnDependentFamily_eq_responseJPartitionDefectOnFamilyAtDepth
            a ha Q j p q]

/-- Square-root form of the depth-`j` gradient mismatch estimate. -/
theorem sqrt_descendantsAverage_ch04GradientMismatch_le_two_mul_sqrt_maxSigmaStarInv_mul_sqrt_responseDefect
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    Real.sqrt
        (descendantsAverage Q j
          (fun R =>
            vecNormSq
              (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
                Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun))) ≤
      2 *
        Real.sqrt (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) F) *
          Real.sqrt
            (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q) := by
  intro F
  let M := Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) F
  let D := JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q
  let A :=
    descendantsAverage Q j
      (fun R =>
        vecNormSq
          (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
            Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun))
  have hmain : A ≤ 2 * M * D := by
    simpa [A, M, D, F] using
      descendantsAverage_ch04GradientMismatch_le_maxSigmaStarInv_mul_responseDefect
        a ha Q j p q
  have hM_nonneg : 0 ≤ M := by
    have hj : Q.scale - (j : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le j)
    simpa [M] using
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hj F
  have hD_nonneg : 0 ≤ D := by
    simpa [D, F] using
      responseJPartitionDefectOnFamilyAtDepth_nonneg F Q j p q
  have hfour : A ≤ 4 * (M * D) := by
    have hMD : 0 ≤ M * D := mul_nonneg hM_nonneg hD_nonneg
    nlinarith
  calc
    Real.sqrt A ≤ 2 * Real.sqrt (M * D) :=
      JUpperBoundWeakNorms.sqrt_le_two_mul_sqrt_of_le_four_mul hfour
    _ = 2 * Real.sqrt M * Real.sqrt D := by
      rw [Real.sqrt_mul hM_nonneg]
      ring

/-- Square-root form of the depth-`j` flux mismatch estimate. -/
theorem sqrt_descendantsAverage_ch04FluxMismatch_le_two_mul_sqrt_maxB_mul_sqrt_responseDefect
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    Real.sqrt
        (descendantsAverage Q j
          (fun R =>
            vecNormSq
              (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
                Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun))) ≤
      2 *
        Real.sqrt (Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) F) *
          Real.sqrt
            (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q) := by
  intro F
  let M := Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) F
  let D := JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q
  let A :=
    descendantsAverage Q j
      (fun R =>
        vecNormSq
          (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
            Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun))
  have hmain : A ≤ 2 * M * D := by
    simpa [A, M, D, F] using
      descendantsAverage_ch04FluxMismatch_le_maxB_mul_responseDefect
        a ha Q j p q
  have hM_nonneg : 0 ≤ M := by
    have hj : Q.scale - (j : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le j)
    simpa [M] using
      Ch02.maxDescendantBMatrixNormAtScale_nonneg Q hj F
  have hD_nonneg : 0 ≤ D := by
    simpa [D, F] using
      responseJPartitionDefectOnFamilyAtDepth_nonneg F Q j p q
  have hfour : A ≤ 4 * (M * D) := by
    have hMD : 0 ≤ M * D := mul_nonneg hM_nonneg hD_nonneg
    nlinarith
  calc
    Real.sqrt A ≤ 2 * Real.sqrt (M * D) :=
      JUpperBoundWeakNorms.sqrt_le_two_mul_sqrt_of_le_four_mul hfour
    _ = 2 * Real.sqrt M * Real.sqrt D := by
      rw [Real.sqrt_mul hM_nonneg]
      ring

private theorem multiscaleDescendantWeight_sub_nat {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) s =
      Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) := by
  unfold Ch02.multiscaleDescendantWeight
  have hsub : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
    omega
  rw [hsub]
  norm_num

/-- Depth-`j` gradient mismatch localized by the q=1 lower ellipticity
observable on the parent cube. -/
theorem descendantsAverage_ch04GradientMismatch_le_lambdaSqCoeffField_responseDefect
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) {s' : ℝ} (hs' : 0 < s') (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun)) ≤
      ((2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
          Real.rpow (3 : ℝ) (s' * (j : ℝ))) ^ 2 *
        JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q := by
  intro F
  let A := descendantsAverage Q j
        (fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun))
  let M := Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) F
  let D := JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q
  let lamInv := (Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹
  let W := Real.rpow (3 : ℝ) (2 * s' * (j : ℝ))
  have hbase : A ≤ 2 * M * D := by
    simpa [A, M, D, F] using
      descendantsAverage_ch04GradientMismatch_le_maxSigmaStarInv_mul_responseDefect
        a ha Q j p q
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
    simpa [D, F] using responseJPartitionDefectOnFamilyAtDepth_nonneg F Q j p q
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

/-- Depth-`j` flux mismatch localized by the q=1 upper ellipticity observable
on the parent cube. -/
theorem descendantsAverage_ch04FluxMismatch_le_LambdaSqCoeffField_responseDefect
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) {t' : ℝ} (ht' : 0 < t') (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun)) ≤
      ((2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
          Real.rpow (3 : ℝ) (t' * (j : ℝ))) ^ 2 *
        JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q := by
  intro F
  let A := descendantsAverage Q j
        (fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun))
  let M := Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (j : ℤ)) F
  let D := JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth F Q j p q
  let Lam := Ch04.LambdaSqCoeffField Q t' (.finite 1) a
  let W := Real.rpow (3 : ℝ) (2 * t' * (j : ℝ))
  have hbase : A ≤ 2 * M * D := by
    simpa [A, M, D, F] using
      descendantsAverage_ch04FluxMismatch_le_maxB_mul_responseDefect a ha Q j p q
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
    simpa [D, F] using responseJPartitionDefectOnFamilyAtDepth_nonneg F Q j p q
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

/-- Finite high-depth gradient mismatch sum localized by the q=1 lower
ellipticity observable and the response partition defect. -/
theorem gradientHighMismatchSum_le_lambdaSqCoeffField_responseDefectSum
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (N : ℕ) (high : ℕ → Prop) [DecidablePred high]
    {s s' : ℝ} (hs' : 0 < s') (p q : Vec d) :
    (∑ j ∈ (Finset.range (N + 1)).filter high,
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt
            (descendantsAverage Q j fun R =>
              vecNormSq
                (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
                  Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun))) ≤
      (2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
        ∑ j ∈ (Finset.range (N + 1)).filter high,
          Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) *
            Real.sqrt
              (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                Q j p q) := by
  refine
    sum_filter_triadicDepthWeight_mul_sqrt_descendantsAverage_vecNormSq_le_const_mul_shifted_weighted_sqrt
      Q s s' (2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹))
      N high
      (fun _j R =>
        Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
          Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun)
      (fun j =>
        JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q)
      ?_ ?_
  · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · intro j _hj
    simpa using
      descendantsAverage_ch04GradientMismatch_le_lambdaSqCoeffField_responseDefect
        a ha Q j hs' p q

/-- Finite high-depth flux mismatch sum localized by the q=1 upper ellipticity
observable and the response partition defect. -/
theorem fluxHighMismatchSum_le_LambdaSqCoeffField_responseDefectSum
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (N : ℕ) (high : ℕ → Prop) [DecidablePred high]
    {t t' : ℝ} (ht' : 0 < t') (p q : Vec d) :
    (∑ j ∈ (Finset.range (N + 1)).filter high,
        Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
          Real.sqrt
            (descendantsAverage Q j fun R =>
              vecNormSq
                (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
                  Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun))) ≤
      (2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
        ∑ j ∈ (Finset.range (N + 1)).filter high,
          Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) *
            Real.sqrt
              (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                Q j p q) := by
  refine
    sum_filter_triadicDepthWeight_mul_sqrt_descendantsAverage_vecNormSq_le_const_mul_shifted_weighted_sqrt
      Q t t' (2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a))
      N high
      (fun _j R =>
        Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
          Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun)
      (fun j =>
        JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q)
      ?_ ?_
  · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · intro j _hj
    simpa using
      descendantsAverage_ch04FluxMismatch_le_LambdaSqCoeffField_responseDefect
        a ha Q j ht' p q

end

end WeakNormsMaximizer
end Section53
end Ch05
end Book
end Homogenization
