/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator
public import LeanPool.NavierStokesAndEuler.Euler.PacketCrossProduct
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

/-!
The finite-dimensional algebra in the curl Piola identity.  Antisymmetrizing
`Fᵀ A F` transforms by the actual adjugate of `F`.  In particular, a
determinant-one change of variables transforms curl by `F⁻¹`.
-/

noncomputable section

namespace EulerPacketPiola

open EulerSmoothLimit EulerMeanBoundary Matrix InnerProductSpace

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def matrixAntisym (A : Mat3) : Fin 3 → ℝ :=
  ![A 2 1 - A 1 2, A 0 2 - A 2 0, A 1 0 - A 0 1]

/-- The adjugate transformation law is a polynomial identity, without invertibility assumptions. -/
theorem matrixAntisym_congruence (F A : Mat3) :
    matrixAntisym (F.transpose * A * F) = F.adjugate.mulVec (matrixAntisym A) := by
  ext i
  fin_cases i <;>
    norm_num [matrixAntisym, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.adjugate_fin_three,
      Matrix.cons_val_two] <;>
    ring

def operatorMatrix (A : Space →L[ℝ] Space) : Mat3 :=
  fun i j => (A (EuclideanSpace.single j 1)) i

theorem operatorMatrix_apply (A : Space →L[ℝ] Space) (x : Space) (i : Fin 3) :
    (A x) i = (operatorMatrix A).mulVec (WithLp.ofLp x) i := by
  have hx : (∑ j : Fin 3, x j • EuclideanSpace.single j (1 : ℝ)) = x := by
    ext j
    simp [Pi.single_apply, mul_ite]
  calc
    (A x) i = (A (∑ j : Fin 3, x j • EuclideanSpace.single j (1 : ℝ))) i := by rw [hx]
    _ = (operatorMatrix A).mulVec (WithLp.ofLp x) i := by
      simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.mulVec, dotProduct, operatorMatrix]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _

theorem operatorMatrix_comp (A B : Space →L[ℝ] Space) :
    operatorMatrix (A.comp B) = operatorMatrix A * operatorMatrix B := by
  ext i j
  exact operatorMatrix_apply A (B (EuclideanSpace.single j 1)) i

theorem operatorMatrix_id : operatorMatrix (ContinuousLinearMap.id ℝ Space) = 1 := by
  ext i j
  simp [operatorMatrix, Matrix.one_apply]

theorem operatorMatrix_adjoint (A : Space →L[ℝ] Space) :
    operatorMatrix A.adjoint = (operatorMatrix A).transpose := by
  ext i j
  have hi := A.adjoint_inner_right (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simpa only [operatorMatrix, Matrix.transpose_apply, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, mul_one] using hi

theorem matrixAntisym_operator (A : Space →L[ℝ] Space) :
    matrixAntisym (operatorMatrix A) = WithLp.ofLp (curlMatrix A) := by
  ext i
  fin_cases i <;> rfl

theorem operatorMatrix_inverse (F : Space ≃L[ℝ] Space) :
    operatorMatrix F.toContinuousLinearMap * operatorMatrix F.symm.toContinuousLinearMap = 1 := by
  rw [← operatorMatrix_comp]
  have he : F.toContinuousLinearMap.comp F.symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ Space := by ext x; simp
  rw [he, operatorMatrix_id]

theorem adjugate_operatorMatrix (F : Space ≃L[ℝ] Space)
    (hdet : (operatorMatrix F.toContinuousLinearMap).det = 1) :
    (operatorMatrix F.toContinuousLinearMap).adjugate =
      operatorMatrix F.symm.toContinuousLinearMap := by
  calc
    (operatorMatrix F.toContinuousLinearMap).adjugate =
        (operatorMatrix F.toContinuousLinearMap).adjugate *
          (operatorMatrix F.toContinuousLinearMap * operatorMatrix F.symm.toContinuousLinearMap) :=
            by
      rw [operatorMatrix_inverse, Matrix.mul_one]
    _ = ((operatorMatrix F.toContinuousLinearMap).adjugate *
          operatorMatrix F.toContinuousLinearMap) * operatorMatrix F.symm.toContinuousLinearMap :=
      (Matrix.mul_assoc _ _ _).symm
    _ = operatorMatrix F.symm.toContinuousLinearMap := by
      rw [Matrix.adjugate_mul, hdet, one_smul, Matrix.one_mul]

/-- The actual Euclidean curl tensor transforms by the inverse under a unit Jacobian. -/
theorem curlMatrix_congruence (F : Space ≃L[ℝ] Space)
    (hdet : (operatorMatrix F.toContinuousLinearMap).det = 1)
    (A : Space →L[ℝ] Space) :
    curlMatrix (F.toContinuousLinearMap.adjoint.comp (A.comp F.toContinuousLinearMap)) =
      F.symm (curlMatrix A) := by
  have hm := matrixAntisym_congruence (operatorMatrix F.toContinuousLinearMap) (operatorMatrix A)
  rw [adjugate_operatorMatrix F hdet] at hm
  ext i
  change (curlMatrix (F.toContinuousLinearMap.adjoint.comp (A.comp F.toContinuousLinearMap))) i =
    (F.symm.toContinuousLinearMap (curlMatrix A)) i
  rw [operatorMatrix_apply F.symm.toContinuousLinearMap (curlMatrix A) i]
  have he := congrFun hm i
  rw [Matrix.mul_assoc, ← operatorMatrix_adjoint, ← operatorMatrix_comp, ← operatorMatrix_comp,
    matrixAntisym_operator, matrixAntisym_operator] at he
  exact he

/-- Algebraic Piola curl identity for a genuine first derivative in label coordinates. -/
theorem curlMatrix_piola (F : Space ≃L[ℝ] Space)
    (hdet : (operatorMatrix F.toContinuousLinearMap).det = 1)
    (B : Space →L[ℝ] Space) :
    curlMatrix (F.toContinuousLinearMap.adjoint.comp B) =
      F.symm (curlMatrix (B.comp F.symm.toContinuousLinearMap)) := by
  have h := curlMatrix_congruence F hdet (B.comp F.symm.toContinuousLinearMap)
  have he : (B.comp F.symm.toContinuousLinearMap).comp F.toContinuousLinearMap = B := by
    ext x
    simp
  rw [he] at h
  exact h

end EulerPacketPiola
