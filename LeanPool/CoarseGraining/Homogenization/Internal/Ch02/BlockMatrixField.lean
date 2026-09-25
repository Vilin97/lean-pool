/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BlockMatrixFieldDefinitions
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism.EllipticBounds
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives

/-! # Block Matrix Field -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

theorem book_blockMatrixField_eq_blockCoeffField {d : ℕ}
    {U : Domain d} (a : CoeffOn U) (x : Vec d) :
    Book.Ch02.blockMatrixField a x = blockCoeffField a.toCoeffField x :=
  rfl

theorem book_blockMatrixInverseField_eq_blockReflect {d : ℕ}
    {U : Domain d} (a : CoeffOn U) (x : Vec d) :
    Book.Ch02.blockMatrixInverseField a x =
      blockReflect (Book.Ch02.blockMatrixField a x) := by
  simp [Book.Ch02.blockMatrixInverseField, Book.Ch02.blockMatrixField, blockReflect]

theorem blockMatrixOfCoeff_factorization {d : ℕ} (A : Mat d) :
    blockMatrixOfCoeff A =
      Book.Ch02.blockMatMul
        (Book.Ch02.blockMatTranspose (Book.Ch02.blockG (-skewPart A)))
        (Book.Ch02.blockMatMul
          (Book.Ch02.blockDiag (symmPart A) ((symmPart A)⁻¹))
          (Book.Ch02.blockG (-skewPart A))) := by
  have hTskew : matTranspose (-skewPart A) = skewPart A := by
    ext i j
    simp [matTranspose, skewPart]
    ring
  have hTone : matTranspose (1 : Mat d) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [matTranspose]
    · have hji : j ≠ i := by
        intro hji
        exact hij hji.symm
      simp [matTranspose, hij, hji]
  have hTzero : matTranspose (0 : Mat d) = 0 := by
    ext i j
    simp [matTranspose]
  apply blockMat_ext
  · simp [blockMatrixOfCoeff, Book.Ch02.blockMatMul, Book.Ch02.blockMatTranspose,
      Book.Ch02.blockDiag, Book.Ch02.blockG, hTskew, hTone, hTzero, Matrix.mul_assoc]
  · simp [blockMatrixOfCoeff, Book.Ch02.blockMatMul, Book.Ch02.blockMatTranspose,
      Book.Ch02.blockDiag, Book.Ch02.blockG, hTskew, hTone, hTzero, Matrix.mul_assoc]
  · simp [blockMatrixOfCoeff, Book.Ch02.blockMatMul, Book.Ch02.blockMatTranspose,
      Book.Ch02.blockDiag, Book.Ch02.blockG, hTskew, hTone, hTzero, Matrix.mul_assoc]
  · simp [blockMatrixOfCoeff, Book.Ch02.blockMatMul, Book.Ch02.blockMatTranspose,
      Book.Ch02.blockDiag, Book.Ch02.blockG, hTskew, hTone, hTzero, Matrix.mul_assoc]

theorem blockMatrixField_factorization {d : ℕ}
    {U : Domain d} (a : CoeffOn U) (x : Vec d) :
    Book.Ch02.blockMatrixField a x =
      Book.Ch02.blockMatMul
        (Book.Ch02.blockMatTranspose
          (Book.Ch02.blockG (-skewPart (a.toCoeffField x))))
        (Book.Ch02.blockMatMul
          (Book.Ch02.blockDiag (symmPart (a.toCoeffField x))
            ((symmPart (a.toCoeffField x))⁻¹))
          (Book.Ch02.blockG (-skewPart (a.toCoeffField x)))) := by
  simpa [book_blockMatrixField_eq_blockCoeffField] using!
    blockMatrixOfCoeff_factorization (a.toCoeffField x)

theorem blockMatrixFieldAlgebraTheory_of_coeffOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    BlockMatrixFieldAlgebraTheory U a where
  field_symmetric := by
    exact Filter.Eventually.of_forall fun x => by
      simpa [book_blockMatrixField_eq_blockCoeffField] using!
        isSymmetricBlockMat_blockMatrixOfCoeff (a.toCoeffField x)
  field_posDef := by
    filter_upwards [a.aeElliptic] with x hx
    intro X hX
    rcases X with ⟨p, q⟩
    simpa [Book.Ch02.BlockPosDef, book_blockMatrixField_eq_blockCoeffField] using!
      blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix
        (A := a.toCoeffField x) hx hX
  factorization := by
    exact Filter.Eventually.of_forall fun x =>
      blockMatrixField_factorization a x
  inverse_formula := by
    exact Filter.Eventually.of_forall fun x =>
      book_blockMatrixInverseField_eq_blockReflect a x
  energy_density := by
    exact Filter.Eventually.of_forall fun _x X => rfl

theorem blockMatrixFieldAlgebraTheory {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    BlockMatrixFieldAlgebraTheory U a :=
  blockMatrixFieldAlgebraTheory_of_coeffOn U a

end BookCh02

end

end Ch02
end Internal
end Homogenization
