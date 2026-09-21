/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.CoarseObservableMeasurability.Basic

/-! # Mu -/

namespace Homogenization

/-!
# Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

**Internal claim:** the `Mu` block quadratic form
`X ↦ (½) ⟨X, A X⟩` is measurable in the coefficient field via the
unfolded `2d × 2d` block-matrix representation. This is the measurable
bridge from full-block measurability to the scalar `Mu` energy used by
all downstream operator/recovery machinery.

**Consumed by:** every `FixedCompetitorEnergyMeasurability/*.lean` file
(`Measurability`, `LipschitzBounds`, `Integrals`, `BlockEnergyAverage`,
`MuObservable`), which in turn feeds the AEE assembly and ultimately
`Theorems/Mu.lean :: aemeasurable_Mu_cubeSet` and
`Theorems/CanonicalSolutions.lean ::
aestronglyMeasurable_canonicalMuHilbertMinimizer_cubeSet`.

If the single-claim summary above grows into three or more distinct
claims, split or refactor per the rebuild contract.
-/

/-- Measurability of the quadratic form `X ↦ (1/2) X · (A X)` when the block
matrix observable is supplied in unfolded `2d × 2d` coordinates. -/
theorem measurable_half_blockVecDot_blockMatVecMul_of_measurable_fullBlockMat
    {α : Type*} [MeasurableSpace α]
    {d : ℕ} {f : α → FullBlockMat d}
    (hf : Measurable f) (X : BlockVec d) :
    Measurable
      (fun a => (1 / 2 : ℝ) *
        blockVecDot X (blockMatVecMul (ofFullBlockMat (f a)) X)) := by
  let v : FullBlockVec d := toFullBlockVec X
  have hf' : ∀ i, Measurable (fun a : α => f a i) := measurable_pi_iff.1 hf
  have hEntry : ∀ i j, Measurable (fun a : α => f a i j) := by
    intro i j
    simpa using (Measurable.eval (hf' i) : Measurable fun a : α => f a i j)
  have hTerm : ∀ i j, Measurable (fun a : α => v i * v j * f a i j) := by
    intro i j
    simpa [mul_assoc] using (hEntry i j).const_mul (v i * v j)
  have hSum :
      Measurable (fun a : α => ∑ i, ∑ j, v i * v j * f a i j) := by
    refine Finset.measurable_sum Finset.univ ?_
    intro i hi
    exact Finset.measurable_sum Finset.univ (fun j _ => hTerm i j)
  have hEq :
      (fun a => (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (ofFullBlockMat (f a)) X)) =
        (fun a => (1 / 2 : ℝ) * ∑ i, ∑ j, v i * v j * f a i j) := by
    funext a
    rw [blockVecDot_blockMatVecMul_eq_toLinearMap₂', toFullBlockMat_ofFullBlockMat,
      Matrix.toLinearMap₂'_apply]
    simp [v, smul_eq_mul, mul_assoc, mul_left_comm]
  rw [hEq]
  exact measurable_const.mul hSum

/-- The lower-right coarse entry is measurable once the pure-flux `Mu`
coordinate slices are measurable. -/
theorem measurable_coarseSigmaStarInvEntryObservable_of_measurable_Mu_pureFlux
    {d : ℕ} {U : Set (Vec d)}
    (hDiag : ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (0, Pi.single i 1) a))
    (hPair :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((0, Pi.single i 1) + (0, Pi.single j 1)) a))
    (r c : Fin d) :
    Measurable (coarseSigmaStarInvEntryObservable U r c) := by
  by_cases hrc : r = c
  · subst c
    have hEq :
        coarseSigmaStarInvEntryObservable U r r =
          (fun a : CoeffField d => (2 : ℝ) * Mu U (0, Pi.single r 1) a) := by
      funext a
      simp [coarseSigmaStarInvEntryObservable, coarseBlockMatrix_lowerRight_apply]
    rw [hEq]
    exact measurable_const.mul (hDiag r)
  · have hsum : Measurable fun a : CoeffField d =>
      Mu U ((0, Pi.single r 1) + (0, Pi.single c 1)) a := hPair r c
    have hr : Measurable fun a : CoeffField d => Mu U (0, Pi.single r 1) a := hDiag r
    have hc : Measurable fun a : CoeffField d => Mu U (0, Pi.single c 1) a := hDiag c
    have hEq :
        coarseSigmaStarInvEntryObservable U r c =
          (fun a : CoeffField d =>
            Mu U ((0, Pi.single r 1) + (0, Pi.single c 1)) a
              - Mu U (0, Pi.single r 1) a
              - Mu U (0, Pi.single c 1) a) := by
      funext a
      simp [coarseSigmaStarInvEntryObservable, coarseBlockMatrix_lowerRight_apply, hrc]
    rw [hEq]
    exact (hsum.sub hr).sub hc

/-- The upper-left coarse entry is measurable once the pure-gradient `Mu`
coordinate slices are measurable. -/
theorem measurable_coarseBEntryObservable_of_measurable_Mu_pureGradient
    {d : ℕ} {U : Set (Vec d)}
    (hDiag : ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (Pi.single i 1, 0) a))
    (hPair :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((Pi.single i 1, 0) + (Pi.single j 1, 0)) a))
    (r c : Fin d) :
    Measurable (coarseBEntryObservable U r c) := by
  by_cases hrc : r = c
  · subst c
    have hEq :
        coarseBEntryObservable U r r =
          (fun a : CoeffField d => (2 : ℝ) * Mu U (Pi.single r 1, 0) a) := by
      funext a
      simp [coarseBEntryObservable, coarseBlockMatrix_upperLeft_apply]
    rw [hEq]
    exact measurable_const.mul (hDiag r)
  · have hsum : Measurable fun a : CoeffField d =>
      Mu U ((Pi.single r 1, 0) + (Pi.single c 1, 0)) a := hPair r c
    have hr : Measurable fun a : CoeffField d => Mu U (Pi.single r 1, 0) a := hDiag r
    have hc : Measurable fun a : CoeffField d => Mu U (Pi.single c 1, 0) a := hDiag c
    have hEq :
        coarseBEntryObservable U r c =
          (fun a : CoeffField d =>
            Mu U ((Pi.single r 1, 0) + (Pi.single c 1, 0)) a
              - Mu U (Pi.single r 1, 0) a
              - Mu U (Pi.single c 1, 0) a) := by
      funext a
      simp [coarseBEntryObservable, coarseBlockMatrix_upperLeft_apply, hrc]
    rw [hEq]
    exact (hsum.sub hr).sub hc

/-- The mixed mean entry is measurable once the mixed and pure coordinate
`Mu` slices are measurable. -/
theorem measurable_coarseSigmaStarInvKappaMeanEntryObservable_of_measurable_Mu_mixed
    {d : ℕ} {U : Set (Vec d)}
    (hFlux : ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (0, Pi.single i 1) a))
    (hGrad :
      ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (Pi.single i 1, 0) a))
    (hMixed :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((Pi.single i 1, 0) + (0, Pi.single j 1)) a))
    (r c : Fin d) :
    Measurable (coarseSigmaStarInvKappaMeanEntryObservable U r c) := by
  have hsum : Measurable fun a : CoeffField d =>
      Mu U ((0, Pi.single r 1) + (Pi.single c 1, 0)) a := by
    simpa [add_comm] using hMixed c r
  have hr : Measurable fun a : CoeffField d => Mu U (0, Pi.single r 1) a := hFlux r
  have hc : Measurable fun a : CoeffField d => Mu U (Pi.single c 1, 0) a := hGrad c
  have hEq :
      coarseSigmaStarInvKappaMeanEntryObservable U r c =
        (fun a : CoeffField d =>
          -(Mu U ((0, Pi.single r 1) + (Pi.single c 1, 0)) a
            - Mu U (0, Pi.single r 1) a
            - Mu U (Pi.single c 1, 0) a)) := by
    funext a
    simp [coarseSigmaStarInvKappaMeanEntryObservable, coarseBlockMatrix_lowerLeft_apply]
  rw [hEq]
  exact ((hsum.sub hr).sub hc).neg

/-- The upper-right coarse entry is measurable once the mixed and pure
coordinate `Mu` slices are measurable. -/
theorem measurable_coarseUpperRightEntryObservable_of_measurable_Mu_mixed
    {d : ℕ} {U : Set (Vec d)}
    (hFlux : ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (0, Pi.single i 1) a))
    (hGrad :
      ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (Pi.single i 1, 0) a))
    (hMixed :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((Pi.single i 1, 0) + (0, Pi.single j 1)) a))
    (r c : Fin d) :
    Measurable (coarseUpperRightEntryObservable U r c) := by
  have hsum : Measurable fun a : CoeffField d =>
      Mu U ((Pi.single r 1, 0) + (0, Pi.single c 1)) a := hMixed r c
  have hr : Measurable fun a : CoeffField d => Mu U (Pi.single r 1, 0) a := hGrad r
  have hc : Measurable fun a : CoeffField d => Mu U (0, Pi.single c 1) a := hFlux c
  have hEq :
      coarseUpperRightEntryObservable U r c =
        (fun a : CoeffField d =>
          Mu U ((Pi.single r 1, 0) + (0, Pi.single c 1)) a
            - Mu U (Pi.single r 1, 0) a
            - Mu U (0, Pi.single c 1) a) := by
    funext a
    simp [coarseUpperRightEntryObservable, coarseBlockMatrix_upperRight_apply]
  rw [hEq]
  exact (hsum.sub hr).sub hc

/-- The lower-left coarse entry is measurable once the mixed and pure
coordinate `Mu` slices are measurable. -/
theorem measurable_coarseLowerLeftEntryObservable_of_measurable_Mu_mixed
    {d : ℕ} {U : Set (Vec d)}
    (hFlux : ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (0, Pi.single i 1) a))
    (hGrad :
      ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (Pi.single i 1, 0) a))
    (hMixed :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((Pi.single i 1, 0) + (0, Pi.single j 1)) a))
    (r c : Fin d) :
    Measurable (coarseLowerLeftEntryObservable U r c) := by
  have hsum : Measurable fun a : CoeffField d =>
      Mu U ((0, Pi.single r 1) + (Pi.single c 1, 0)) a := by
    simpa [add_comm] using hMixed c r
  have hr : Measurable fun a : CoeffField d => Mu U (0, Pi.single r 1) a := hFlux r
  have hc : Measurable fun a : CoeffField d => Mu U (Pi.single c 1, 0) a := hGrad c
  have hEq :
      coarseLowerLeftEntryObservable U r c =
        (fun a : CoeffField d =>
          Mu U ((0, Pi.single r 1) + (Pi.single c 1, 0)) a
            - Mu U (0, Pi.single r 1) a
            - Mu U (Pi.single c 1, 0) a) := by
    funext a
    simp [coarseLowerLeftEntryObservable, coarseBlockMatrix_lowerLeft_apply]
  rw [hEq]
  exact (hsum.sub hr).sub hc

/-- Measurability of the full coarse block matrix from the finite coordinate
`Mu` slices that generate its entries. -/
theorem measurable_coarseFullBlockMatrixObservable_of_measurable_coordinate_Mu
    {d : ℕ} {U : Set (Vec d)}
    (hFlux : ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (0, Pi.single i 1) a))
    (hFluxPair :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((0, Pi.single i 1) + (0, Pi.single j 1)) a))
    (hGrad :
      ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (Pi.single i 1, 0) a))
    (hGradPair :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((Pi.single i 1, 0) + (Pi.single j 1, 0)) a))
    (hMixed :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((Pi.single i 1, 0) + (0, Pi.single j 1)) a)) :
    Measurable (coarseFullBlockMatrixObservable U) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine measurable_pi_iff.2 fun j => ?_
  cases i with
  | inl r =>
      cases j with
      | inl c =>
          simpa [coarseFullBlockMatrixObservable, coarseBObservable, Function.comp,
            fullBlockMatUpperLeft, coarseBEntryObservable] using!
            measurable_coarseBEntryObservable_of_measurable_Mu_pureGradient
              (U := U) hGrad hGradPair r c
      | inr c =>
          simpa [coarseFullBlockMatrixObservable, coarseUpperRightEntryObservable] using!
            measurable_coarseUpperRightEntryObservable_of_measurable_Mu_mixed
              (U := U) hFlux hGrad hMixed r c
  | inr r =>
      cases j with
      | inl c =>
          simpa [coarseFullBlockMatrixObservable, coarseLowerLeftEntryObservable] using!
            measurable_coarseLowerLeftEntryObservable_of_measurable_Mu_mixed
              (U := U) hFlux hGrad hMixed r c
      | inr c =>
          simpa [coarseFullBlockMatrixObservable, coarseSigmaStarInvObservable, Function.comp,
            fullBlockMatLowerRight, coarseSigmaStarInvEntryObservable] using!
            measurable_coarseSigmaStarInvEntryObservable_of_measurable_Mu_pureFlux
              (U := U) hFlux hFluxPair r c

/-- Once the coarse block matrix is measurable and `Mu` is known to be
quadratic pointwise, the full ambient `Mu` family is measurable. -/
theorem hasMeasurableMuFamily_of_measurable_coarseFullBlockMatrixObservable_of_hasQuadraticMu
    {d : ℕ} {U : Set (Vec d)}
    (hBlockMeas : Measurable (coarseFullBlockMatrixObservable U))
    (hquad : ∀ a : CoeffField d, HasQuadraticMu U a) :
    HasMeasurableMuFamily U := by
  intro P0
  have hQuadratic :
      Measurable
        (fun a : CoeffField d =>
          (1 / 2 : ℝ) *
            blockVecDot P0 (blockMatVecMul (coarseBlockMatrix U a) P0)) := by
    simpa [coarseFullBlockMatrixObservable] using
      measurable_half_blockVecDot_blockMatVecMul_of_measurable_fullBlockMat
        (f := coarseFullBlockMatrixObservable U) hBlockMeas P0
  have hEq :
      (fun a : CoeffField d => Mu U P0 a) =
        (fun a : CoeffField d =>
          (1 / 2 : ℝ) *
            blockVecDot P0 (blockMatVecMul (coarseBlockMatrix U a) P0)) := by
    funext a
    exact Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu (hquad a) P0
  rw [hEq]
  exact hQuadratic

/-- Finite coordinate `Mu` measurability plus pointwise quadraticity upgrades
to the full ambient `Mu` family. -/
theorem hasMeasurableMuFamily_of_measurable_coordinate_Mu_of_hasQuadraticMu
    {d : ℕ} {U : Set (Vec d)}
    (hFlux : ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (0, Pi.single i 1) a))
    (hFluxPair :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((0, Pi.single i 1) + (0, Pi.single j 1)) a))
    (hGrad :
      ∀ i : Fin d, Measurable (fun a : CoeffField d => Mu U (Pi.single i 1, 0) a))
    (hGradPair :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((Pi.single i 1, 0) + (Pi.single j 1, 0)) a))
    (hMixed :
      ∀ i j : Fin d,
        Measurable (fun a : CoeffField d => Mu U ((Pi.single i 1, 0) + (0, Pi.single j 1)) a))
    (hquad : ∀ a : CoeffField d, HasQuadraticMu U a) :
    HasMeasurableMuFamily U :=
  hasMeasurableMuFamily_of_measurable_coarseFullBlockMatrixObservable_of_hasQuadraticMu
    (U := U)
    (measurable_coarseFullBlockMatrixObservable_of_measurable_coordinate_Mu
      (U := U) hFlux hFluxPair hGrad hGradPair hMixed)
    hquad

end Homogenization
