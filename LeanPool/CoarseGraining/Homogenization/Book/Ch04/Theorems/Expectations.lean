/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CoarseObservables
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.AnnealedDefinitions
import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.Basic

/-! # Expectations -/

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Expectations and finite response moments

This file is the public Chapter 4 surface for taking expectations of the
scalar response observables already exposed in `CoarseObservables`.

The surface is intentionally small: it names the observable, its expectation,
the centered observable used in the manuscript, and the finite descendant
average expectation theorem.  Integrability remains an explicit theorem
hypothesis; there is no extra moment carrier or section-local wrapper track.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.Elementwise

/-- Finite-dimensional matrix quadratic forms commute with entrywise
expectation under entrywise integrability. -/
theorem integral_vecDot_matVecMul_eq_entrywise_integral
    {d : ℕ} {P : RestrictionCoeffLaw d} {M : RegCoeffField d → Mat d}
    (hM : ∀ i j, Integrable (fun a => M a i j) P) (x y : Vec d) :
    ∫ a, vecDot x (matVecMul (M a) y) ∂P =
      vecDot x (matVecMul (fun i j => ∫ a, M a i j ∂P) y) := by
  simp [vecDot, matVecMul]
  rw [MeasureTheory.integral_finsetSum Finset.univ]
  · congr 1
    ext i
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finsetSum Finset.univ]
    · simp_rw [MeasureTheory.integral_mul_const]
    · intro j _hj
      exact (hM i j).mul_const (y j)
  · intro i _hi
    exact (MeasureTheory.integrable_finsetSum Finset.univ fun j _hj =>
      (hM i j).mul_const (y j)).const_mul (x i)

/-- Full coarse-block integrability gives entrywise integrability of the
corresponding doubled coarse matrix. -/
private theorem integrable_blockMatEntry_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} {P : RestrictionCoeffLaw d} {Q : TriadicCube d}
    (hInt : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    ∀ α β,
      Integrable
        (fun a : RegCoeffField d => blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) α β) P := by
  intro α β
  have hα : Integrable (fun a : RegCoeffField d => coarseFullBlockMatrixAtCube Q a α) P :=
    MeasureTheory.Integrable.eval hInt α
  have hαβ : Integrable (fun a : RegCoeffField d => coarseFullBlockMatrixAtCube Q a α β) P :=
    MeasureTheory.Integrable.eval hα β
  simpa [coarseFullBlockMatrixAtCube, coarseFullBlockMatrixObservable, toFullBlockMat,
    blockMatEntry] using hαβ

/-- Scalar response observable on a deterministic triadic cube. -/
noncomputable def restrictionResponseJObservableCubeSet {d : ℕ}
    (Q : TriadicCube d) (p q : Vec d) : RegCoeffField d → ℝ :=
  fun a => ResponseJ (cubeSet Q) p q a.toFun

@[simp]
theorem restrictionResponseJObservableCubeSet_apply {d : ℕ}
    (Q : TriadicCube d) (p q : Vec d) (a : RegCoeffField d) :
    restrictionResponseJObservableCubeSet Q p q a = ResponseJ (cubeSet Q) p q a.toFun :=
  rfl

/-- The scalar response observable is pointwise nonnegative. -/
theorem restrictionResponseJObservableCubeSet_nonneg {d : ℕ}
    (Q : TriadicCube d) (p q : Vec d) (a : RegCoeffField d) :
    0 ≤ restrictionResponseJObservableCubeSet Q p q a := by
  simpa [restrictionResponseJObservableCubeSet] using responseJ_nonneg (cubeSet Q) p q a.toFun

theorem restrictionResponseJObservableCubeSet_ae_eq_quadratic_coarseBlockMatrix_of_lawCarrier
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    (fun a : RegCoeffField d => restrictionResponseJObservableCubeSet Q p q a) =ᵐ[P]
      (fun a : RegCoeffField d =>
        (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft p)) := by
  filter_upwards
    [hP.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot_ae Q p q,
      hP.ae_exists_coarseBlockMatrix_openCubeSet Q] with a hResponse hex
  have hCoarse :
      IsCoarseBlockMatrix (openCubeSet Q) a.toFun (coarseBlockMatrix (openCubeSet Q) a.toFun) :=
    isCoarseBlockMatrix_coarseBlockMatrix hex
  calc
    restrictionResponseJObservableCubeSet Q p q a = ResponseJ (cubeSet Q) p q a.toFun := rfl
    _ = Mu (cubeSet Q) (-p, q) a.toFun - vecDot p q := hResponse
    _ = Mu (openCubeSet Q) (-p, q) a.toFun - vecDot p q := by
      rw [Mu_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (P := (-p, q)) (a := a.toFun)]
    _ =
        (1 / 2 : ℝ) *
            blockVecDot (-p, q)
              (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun) (-p, q)) -
          vecDot p q := by
        rw [Mu_eq_half_blockVecDot_coarseBlockMatrix hex (-p, q)]
    _ =
        (1 / 2 : ℝ) *
            vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerLeft p) +
          (1 / 2 : ℝ) *
            vecDot p (matVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun).upperLeft p) := by
        rw [magic_half_blockVecDot_neg_left_of_isSymmetricBlockMat hCoarse.1 p q]
        ring
    _ =
        (1 / 2 : ℝ) *
            vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft p) +
          (1 / 2 : ℝ) *
            vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft p) := by
        rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a.toFun]

private theorem integrable_responseJQuadratic_coarseBlockMatrix_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} {P : RestrictionCoeffLaw d} [IsFiniteMeasure P] {Q : TriadicCube d} (p q : Vec d)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    Integrable
      (fun a : RegCoeffField d =>
        (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft p)) P := by
  let M : RegCoeffField d → BlockMat d := fun a => coarseBlockMatrix (cubeSet Q) a.toFun
  have hEntry := integrable_blockMatEntry_of_integrable_coarseFullBlockMatrixAtCube hBlock
  have hLR : ∀ i j, Integrable (fun a : RegCoeffField d => (M a).lowerRight i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inr j)
  have hLL : ∀ i j, Integrable (fun a : RegCoeffField d => (M a).lowerLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inl j)
  have hUL : ∀ i j, Integrable (fun a : RegCoeffField d => (M a).upperLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inl i) (Sum.inl j)
  have hTermLR :
      Integrable (fun a : RegCoeffField d => vecDot q (matVecMul (M a).lowerRight q)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
        (hLR i j).mul_const (q j)).const_mul (q i)
  have hTermLL :
      Integrable (fun a : RegCoeffField d => vecDot q (matVecMul (M a).lowerLeft p)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
        (hLL i j).mul_const (p j)).const_mul (q i)
  have hTermUL :
      Integrable (fun a : RegCoeffField d => vecDot p (matVecMul (M a).upperLeft p)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
        (hUL i j).mul_const (p j)).const_mul (p i)
  simpa [M] using!
    (((hTermLR.const_mul (1 / 2 : ℝ)).sub (integrable_const _)).sub hTermLL).add
      (hTermUL.const_mul (1 / 2 : ℝ))

namespace RestrictionLawCarrier

/-- Full coarse-block integrability makes the scalar response integrable.

The law carrier supplies the a.s. elliptic support and the deterministic
`ResponseJ = Mu(-p,q) - p·q` identity; the only remaining analytic input is
integrability of the finite-dimensional coarse block. -/
theorem integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (p q : Vec d)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    Integrable (restrictionResponseJObservableCubeSet Q p q) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  exact
    (integrable_responseJQuadratic_coarseBlockMatrix_of_integrable_coarseFullBlockMatrixAtCube
      (P := P) (Q := Q) p q hBlock).congr
        (restrictionResponseJObservableCubeSet_ae_eq_quadratic_coarseBlockMatrix_of_lawCarrier
          hP Q p q).symm

/-- Expected scalar response expressed through the annealed coarse block
matrix, with the stochastic hypotheses packaged in `RestrictionLawCarrier`.

This is the note-facing Chapter 4 source identity: Ch5 should call this rather
than passing deterministic coarse-data witnesses. -/
theorem integral_restrictionResponseJObservableCubeSet_eq_quadratic_annealedBlockMatrix
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (p q : Vec d)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    ∫ a, restrictionResponseJObservableCubeSet Q p q a ∂P =
      (1 / 2 : ℝ) * vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (annealedBlockMatrix P (cubeSet Q)).upperLeft p) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let M : RegCoeffField d → BlockMat d := fun a => coarseBlockMatrix (cubeSet Q) a.toFun
  have hEntry := integrable_blockMatEntry_of_integrable_coarseFullBlockMatrixAtCube hBlock
  have hLR : ∀ i j, Integrable (fun a : RegCoeffField d => (M a).lowerRight i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inr j)
  have hLL : ∀ i j, Integrable (fun a : RegCoeffField d => (M a).lowerLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inl j)
  have hUL : ∀ i j, Integrable (fun a : RegCoeffField d => (M a).upperLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inl i) (Sum.inl j)
  have hFormula :=
    restrictionResponseJObservableCubeSet_ae_eq_quadratic_coarseBlockMatrix_of_lawCarrier hP Q p q
  have hLRint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hLR q q
  have hLLint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hLL q p
  have hULint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hUL p p
  calc
    ∫ a, restrictionResponseJObservableCubeSet Q p q a ∂P
        =
      ∫ a,
        (1 / 2 : ℝ) * vecDot q (matVecMul (M a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (M a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (M a).upperLeft p) ∂P :=
        integral_congr_ae hFormula
    _ =
      (1 / 2 : ℝ) * ∫ a, vecDot q (matVecMul (M a).lowerRight q) ∂P -
        vecDot p q -
        ∫ a, vecDot q (matVecMul (M a).lowerLeft p) ∂P +
        (1 / 2 : ℝ) * ∫ a, vecDot p (matVecMul (M a).upperLeft p) ∂P := by
        let f : RegCoeffField d → ℝ := fun a => vecDot q (matVecMul (M a).lowerRight q)
        let g : RegCoeffField d → ℝ := fun a => vecDot q (matVecMul (M a).lowerLeft p)
        let h : RegCoeffField d → ℝ := fun a => vecDot p (matVecMul (M a).upperLeft p)
        have hf : Integrable f P := by
          simp [f, vecDot, matVecMul]
          exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
            (MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
              (hLR i j).mul_const (q j)).const_mul (q i)
        have hg : Integrable g P := by
          simp [g, vecDot, matVecMul]
          exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
            (MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
              (hLL i j).mul_const (p j)).const_mul (q i)
        have hh : Integrable h P := by
          simp [h, vecDot, matVecMul]
          exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
            (MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
              (hUL i j).mul_const (p j)).const_mul (p i)
        rw [integral_add]
        · rw [integral_sub]
          · rw [integral_sub]
            · rw [integral_const_mul]
              rw [integral_const]
              rw [integral_const_mul]
              simp [Measure.real, IsProbabilityMeasure.measure_univ]
            · exact hf.const_mul (1 / 2 : ℝ)
            · exact integrable_const _
          · exact (hf.const_mul (1 / 2 : ℝ)).sub (integrable_const _)
          · exact hg
        · exact ((hf.const_mul (1 / 2 : ℝ)).sub (integrable_const _)).sub hg
        · exact hh.const_mul (1 / 2 : ℝ)
    _ =
      (1 / 2 : ℝ) * vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (annealedBlockMatrix P (cubeSet Q)).upperLeft p) := by
        rw [hLRint, hLLint, hULint]
        rfl

end RestrictionLawCarrier

/-- Centered scalar response observable on a deterministic triadic cube. -/
noncomputable def restrictionCenteredResponseJObservableCubeSet {d : ℕ}
    (Q : TriadicCube d) (p q p0 q0 : Vec d) : RegCoeffField d → ℝ :=
  fun a => restrictionResponseJObservableCubeSet Q p q a - (1 / 2 : ℝ) * vecDot p0 q0

@[simp]
theorem restrictionCenteredResponseJObservableCubeSet_apply {d : ℕ}
    (Q : TriadicCube d) (p q p0 q0 : Vec d) (a : RegCoeffField d) :
    restrictionCenteredResponseJObservableCubeSet Q p q p0 q0 a =
      restrictionResponseJObservableCubeSet Q p q a - (1 / 2 : ℝ) * vecDot p0 q0 :=
  rfl

/-- Annealed scalar response on a deterministic triadic cube. -/
noncomputable def expectedResponseJCubeSet {d : ℕ}
    (P : RestrictionCoeffLaw d) (Q : TriadicCube d) (p q : Vec d) : ℝ :=
  ∫ a, restrictionResponseJObservableCubeSet Q p q a ∂P

/-- Expected scalar response expressed through the annealed coarse block matrix.

The only stochastic hypotheses are the deterministic coarse-data identity
almost surely and integrability of the full coarse block.  Scalarization is
not used here; Ch5 gets its scalar formula by specializing this source
identity. -/
theorem integral_restrictionResponseJObservableCubeSet_eq_quadratic_annealedBlockMatrix
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (Q : TriadicCube d) (p q : Vec d)
    (hData : ∀ᵐ a ∂P, OpenCubeDeterministicCoarseData Q a.toFun)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    ∫ a, restrictionResponseJObservableCubeSet Q p q a ∂P =
      (1 / 2 : ℝ) * vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (annealedBlockMatrix P (cubeSet Q)).upperLeft p) := by
  let M : RegCoeffField d → BlockMat d := fun a => coarseBlockMatrix (cubeSet Q) a.toFun
  have hEntry := integrable_blockMatEntry_of_integrable_coarseFullBlockMatrixAtCube hBlock
  have hLR : ∀ i j, Integrable (fun a : RegCoeffField d => (M a).lowerRight i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inr j)
  have hLL : ∀ i j, Integrable (fun a : RegCoeffField d => (M a).lowerLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inl j)
  have hUL : ∀ i j, Integrable (fun a : RegCoeffField d => (M a).upperLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inl i) (Sum.inl j)
  have hTermLR :
      Integrable (fun a : RegCoeffField d => vecDot q (matVecMul (M a).lowerRight q)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
        (hLR i j).mul_const (q j)).const_mul (q i)
  have hTermLL :
      Integrable (fun a : RegCoeffField d => vecDot q (matVecMul (M a).lowerLeft p)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
        (hLL i j).mul_const (p j)).const_mul (q i)
  have hTermUL :
      Integrable (fun a : RegCoeffField d => vecDot p (matVecMul (M a).upperLeft p)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
        (hUL i j).mul_const (p j)).const_mul (p i)
  have hFormula :
      (fun a : RegCoeffField d => restrictionResponseJObservableCubeSet Q p q a) =ᵐ[P]
        (fun a : RegCoeffField d =>
          (1 / 2 : ℝ) * vecDot q (matVecMul (M a).lowerRight q) -
            vecDot p q -
            vecDot q (matVecMul (M a).lowerLeft p) +
            (1 / 2 : ℝ) * vecDot p (matVecMul (M a).upperLeft p)) := by
    filter_upwards [hData] with a ha
    calc
      restrictionResponseJObservableCubeSet Q p q a = ResponseJ (cubeSet Q) p q a.toFun := rfl
      _ = ResponseJ (openCubeSet Q) p q a.toFun :=
        responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a.toFun
      _ =
        (1 / 2 : ℝ) *
            vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerLeft p) +
          (1 / 2 : ℝ) *
            vecDot p (matVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun).upperLeft p) :=
        responseJ_formula_coarseBlockMatrix_openCubeSet_of_deterministicCoarseData ha p q
      _ =
        (1 / 2 : ℝ) * vecDot q (matVecMul (M a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (M a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (M a).upperLeft p) := by
        rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a.toFun]
  have hLRint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hLR q q
  have hLLint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hLL q p
  have hULint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hUL p p
  calc
    ∫ a, restrictionResponseJObservableCubeSet Q p q a ∂P
        =
      ∫ a,
        (1 / 2 : ℝ) * vecDot q (matVecMul (M a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (M a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (M a).upperLeft p) ∂P :=
        integral_congr_ae hFormula
    _ =
      (1 / 2 : ℝ) * ∫ a, vecDot q (matVecMul (M a).lowerRight q) ∂P -
        vecDot p q -
        ∫ a, vecDot q (matVecMul (M a).lowerLeft p) ∂P +
        (1 / 2 : ℝ) * ∫ a, vecDot p (matVecMul (M a).upperLeft p) ∂P := by
        rw [integral_add]
        · rw [integral_sub]
          · rw [integral_sub]
            · rw [integral_const_mul]
              rw [integral_const]
              rw [integral_const_mul]
              simp [Measure.real, IsProbabilityMeasure.measure_univ]
            · exact hTermLR.const_mul (1 / 2 : ℝ)
            · exact integrable_const _
          · exact (hTermLR.const_mul (1 / 2 : ℝ)).sub (integrable_const _)
          · exact hTermLL
        · exact ((hTermLR.const_mul (1 / 2 : ℝ)).sub (integrable_const _)).sub hTermLL
        · exact hTermUL.const_mul (1 / 2 : ℝ)
    _ =
      (1 / 2 : ℝ) * vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (annealedBlockMatrix P (cubeSet Q)).upperLeft p) := by
        rw [hLRint, hLLint, hULint]
        rfl

/-- Annealed finite descendant average of scalar responses. -/
noncomputable def expectedDescendantsAverageResponseJCubeSet {d : ℕ}
    (P : RestrictionCoeffLaw d) (Q : TriadicCube d) (j : ℕ) (p q : Vec d) : ℝ :=
  descendantsAverage Q j (fun R => expectedResponseJCubeSet P R p q)

/-- Difference of two annealed scalar responses, the basic `τ`-type quantity. -/
noncomputable def tauResponseJCubeSet {d : ℕ}
    (P : RestrictionCoeffLaw d) (Qchild Qparent : TriadicCube d) (p q : Vec d) : ℝ :=
  expectedResponseJCubeSet P Qchild p q - expectedResponseJCubeSet P Qparent p q

/-- Finite descendant averages preserve integrability. -/
theorem integrable_descendantsAverage
    {d : ℕ} {P : RestrictionCoeffLaw d} {Q : TriadicCube d} {j : ℕ}
    {F : TriadicCube d → RegCoeffField d → ℝ}
    (hF : ∀ R, R ∈ descendantsAtDepth Q j → Integrable (F R) P) :
    Integrable
      (fun a : RegCoeffField d => descendantsAverage Q j (fun R => F R a)) P := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hsum :
      Integrable (fun a : RegCoeffField d => ∑ R ∈ D, F R a) P := by
    exact MeasureTheory.integrable_finsetSum D
      (fun R hR => hF R (by simpa [D] using hR))
  simpa [descendantsAverage, D] using hsum.const_mul ((D.card : ℝ)⁻¹)

/-- Finite descendant averages commute with expectation under childwise
integrability. -/
theorem integral_descendantsAverage_eq_descendantsAverage_integral
    {d : ℕ} {P : RestrictionCoeffLaw d} {Q : TriadicCube d} {j : ℕ}
    {F : TriadicCube d → RegCoeffField d → ℝ}
    (hF : ∀ R, R ∈ descendantsAtDepth Q j → Integrable (F R) P) :
    ∫ a, descendantsAverage Q j (fun R => F R a) ∂P =
      descendantsAverage Q j (fun R => ∫ a, F R a ∂P) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  calc
    ∫ a, descendantsAverage Q j (fun R => F R a) ∂P
        =
      ∫ a,
        (D.card : ℝ)⁻¹ * (∑ R ∈ D, F R a) ∂P := by
          rfl
    _ =
      (D.card : ℝ)⁻¹ *
        ∫ a, ∑ R ∈ D, F R a ∂P := by
          rw [integral_const_mul]
    _ =
      (D.card : ℝ)⁻¹ *
        (∑ R ∈ D, ∫ a, F R a ∂P) := by
          rw [MeasureTheory.integral_finsetSum D
            (fun R hR => hF R (by simpa [D] using hR))]
    _ = descendantsAverage Q j (fun R => ∫ a, F R a ∂P) := by
          simp [descendantsAverage, D]

/-- Finite descendant averages preserve `MemLp`. -/
theorem memLp_descendantsAverage
    {d : ℕ} {P : RestrictionCoeffLaw d} {Q : TriadicCube d} {j : ℕ} {r : ℝ≥0∞}
    {F : TriadicCube d → RegCoeffField d → ℝ}
    (hF : ∀ R, R ∈ descendantsAtDepth Q j → MemLp (F R) r P) :
    MemLp
      (fun a : RegCoeffField d => descendantsAverage Q j (fun R => F R a)) r P := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hsum :
      MemLp (fun a : RegCoeffField d => ∑ R ∈ D, F R a) r P := by
    exact MeasureTheory.memLp_finsetSum D
      (fun R hR => hF R (by simpa [D] using hR))
  simpa [descendantsAverage, D] using hsum.const_mul ((D.card : ℝ)⁻¹)

/-- Finite descendant averages of response observables are integrable if the
child responses are integrable. -/
theorem integrable_descendantsAverage_restrictionResponseJObservableCubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} {Q : TriadicCube d} {j : ℕ} {p q : Vec d}
    (hJ : ∀ R, R ∈ descendantsAtDepth Q j →
      Integrable (restrictionResponseJObservableCubeSet R p q) P) :
    Integrable
      (fun a : RegCoeffField d =>
        descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a)) P :=
  integrable_descendantsAverage
    (P := P) (Q := Q) (j := j)
    (F := fun R a => restrictionResponseJObservableCubeSet R p q a) hJ

/-- Finite descendant averages of response observables are in `L^r` if the
child responses are in `L^r`. -/
theorem memLp_descendantsAverage_restrictionResponseJObservableCubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} {Q : TriadicCube d} {j : ℕ} {r : ℝ≥0∞}
    {p q : Vec d}
    (hJ : ∀ R, R ∈ descendantsAtDepth Q j →
      MemLp (restrictionResponseJObservableCubeSet R p q) r P) :
    MemLp
      (fun a : RegCoeffField d =>
        descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a)) r P :=
  memLp_descendantsAverage
    (P := P) (Q := Q) (j := j) (r := r)
    (F := fun R a => restrictionResponseJObservableCubeSet R p q a) hJ

/-- Centering by a deterministic scalar preserves integrability. -/
theorem integrable_restrictionCenteredResponseJObservableCubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} [IsFiniteMeasure P]
    (Q : TriadicCube d) (p q p0 q0 : Vec d)
    (hJ : Integrable (restrictionResponseJObservableCubeSet Q p q) P) :
    Integrable (restrictionCenteredResponseJObservableCubeSet Q p q p0 q0) P := by
  simpa [restrictionCenteredResponseJObservableCubeSet] using! hJ.sub (integrable_const _)

/-- Centering by a deterministic scalar preserves `MemLp` under a finite
measure. -/
theorem memLp_restrictionCenteredResponseJObservableCubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} {r : ℝ≥0∞} [IsFiniteMeasure P]
    (Q : TriadicCube d) (p q p0 q0 : Vec d)
    (hJ : MemLp (restrictionResponseJObservableCubeSet Q p q) r P) :
    MemLp (restrictionCenteredResponseJObservableCubeSet Q p q p0 q0) r P := by
  convert
    hJ.sub
      (MeasureTheory.memLp_const
        (μ := P) (p := r) (c := (1 / 2 : ℝ) * vecDot p0 q0)) using 1
  funext a
  simp [restrictionCenteredResponseJObservableCubeSet, Pi.sub_apply]

/-- The integral of the centered response is the annealed response minus the
deterministic centering scalar. -/
theorem integral_restrictionCenteredResponseJObservableCubeSet_eq_expectedResponseJCubeSet_sub_half_dot
    {d : ℕ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (Q : TriadicCube d) (p q p0 q0 : Vec d)
    (hJ : Integrable (restrictionResponseJObservableCubeSet Q p q) P) :
    ∫ a, restrictionCenteredResponseJObservableCubeSet Q p q p0 q0 a ∂P =
      expectedResponseJCubeSet P Q p q - (1 / 2 : ℝ) * vecDot p0 q0 := by
  have hConst :
      Integrable (fun _ : RegCoeffField d => (1 / 2 : ℝ) * vecDot p0 q0) P :=
    integrable_const _
  calc
    ∫ a, restrictionCenteredResponseJObservableCubeSet Q p q p0 q0 a ∂P
        = ∫ a,
            restrictionResponseJObservableCubeSet Q p q a -
              (1 / 2 : ℝ) * vecDot p0 q0 ∂P := by
          rfl
    _ = ∫ a, restrictionResponseJObservableCubeSet Q p q a ∂P -
          ∫ _a : RegCoeffField d, (1 / 2 : ℝ) * vecDot p0 q0 ∂P := by
          rw [integral_sub hJ hConst]
    _ = expectedResponseJCubeSet P Q p q - (1 / 2 : ℝ) * vecDot p0 q0 := by
          rw [integral_const]
          simp [expectedResponseJCubeSet, Measure.real, IsProbabilityMeasure.measure_univ]

/-- Finite descendant response averages commute with expectation, assuming
childwise integrability. -/
theorem integral_descendantsAverage_restrictionResponseJObservableCubeSet_eq_expectedDescendantsAverageResponseJCubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d}
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d)
    (hJ : ∀ R, R ∈ descendantsAtDepth Q j →
      Integrable (restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a,
        descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a) ∂P =
      expectedDescendantsAverageResponseJCubeSet P Q j p q := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  calc
    ∫ a,
        descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a) ∂P
        =
      ∫ a,
        (D.card : ℝ)⁻¹ *
          (∑ R ∈ D, restrictionResponseJObservableCubeSet R p q a) ∂P := by
          rfl
    _ =
      (D.card : ℝ)⁻¹ *
        ∫ a, ∑ R ∈ D, restrictionResponseJObservableCubeSet R p q a ∂P := by
          rw [integral_const_mul]
    _ =
      (D.card : ℝ)⁻¹ *
        (∑ R ∈ D, ∫ a, restrictionResponseJObservableCubeSet R p q a ∂P) := by
          rw [MeasureTheory.integral_finsetSum D
            (fun R hR => hJ R (by simpa [D] using hR))]
    _ = expectedDescendantsAverageResponseJCubeSet P Q j p q := by
          simp [expectedDescendantsAverageResponseJCubeSet, expectedResponseJCubeSet,
            descendantsAverage, D]

namespace RestrictionLawCarrier

/-- The named response observable is a.e.-measurable under a law carrier. -/
theorem aemeasurable_restrictionResponseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEMeasurable (restrictionResponseJObservableCubeSet Q p q) P := by
  simpa [restrictionResponseJObservableCubeSet] using! hP.aemeasurable_ResponseJ_cubeSet Q p q

/-- The named response observable is a.e.-strongly-measurable under a law
carrier. -/
theorem aestronglyMeasurable_restrictionResponseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEStronglyMeasurable (restrictionResponseJObservableCubeSet Q p q) P :=
  (hP.aemeasurable_restrictionResponseJObservableCubeSet Q p q).aestronglyMeasurable

/-- Centered response observables are a.e.-measurable under a law carrier. -/
theorem aemeasurable_restrictionCenteredResponseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (p q p0 q0 : Vec d) :
    AEMeasurable (restrictionCenteredResponseJObservableCubeSet Q p q p0 q0) P := by
  simpa [restrictionCenteredResponseJObservableCubeSet] using!
    (hP.aemeasurable_restrictionResponseJObservableCubeSet Q p q).sub aemeasurable_const

/-- Centered response observables are a.e.-strongly-measurable under a law
carrier. -/
theorem aestronglyMeasurable_restrictionCenteredResponseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (p q p0 q0 : Vec d) :
    AEStronglyMeasurable (restrictionCenteredResponseJObservableCubeSet Q p q p0 q0) P :=
  (hP.aemeasurable_restrictionCenteredResponseJObservableCubeSet Q p q p0 q0).aestronglyMeasurable

/-- Finite descendant averages of the named response observables are
a.e.-measurable under a law carrier. -/
theorem aemeasurable_descendantsAverage_restrictionResponseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a)) P := by
  simpa [restrictionResponseJObservableCubeSet] using
    hP.aemeasurable_descendantsAverage_ResponseJ_cubeSet Q j p q

/-- Finite descendant averages of the named response observables are
a.e.-strongly-measurable under a law carrier. -/
theorem aestronglyMeasurable_descendantsAverage_restrictionResponseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    AEStronglyMeasurable
      (fun a : RegCoeffField d =>
        descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a)) P :=
  (hP.aemeasurable_descendantsAverage_restrictionResponseJObservableCubeSet Q j p q).aestronglyMeasurable

end RestrictionLawCarrier

end

end Ch04
end Book
end Homogenization
