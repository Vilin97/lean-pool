/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.MatrixOrder
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Real matrix to CStarMatrix bridge

This module contains the thin representation bridge needed to reuse Mathlib's
CStar functional-calculus order API from the real-matrix RandomMatrix layer.
It deliberately does not prove Lieb, Golden-Thompson, Bernstein CFC, or Matrix
Bernstein.  The positive/order/log transport targets at the end are explicit
statement surfaces for future proof leaves.
-/

namespace HighDimProb

noncomputable section

open scoped ComplexOrder MatrixOrder Matrix.Norms.Operator Matrix.Norms.L2Operator

/-- Embed a real square matrix into Mathlib's complex `CStarMatrix` model.

The map is entrywise `Real -> Complex` followed by `CStarMatrix.ofMatrix`.
It is a representation bridge only; it does not change HighDimProb's public
real-matrix order or random-matrix vocabulary. -/
def realMatrixToCStarMatrix {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) :
    CStarMatrix (Fin n) (Fin n) Complex :=
  CStarMatrix.ofMatrix (A.map (algebraMap Real Complex))

@[simp]
theorem realMatrixToCStarMatrix_apply {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (i j : Fin n) :
    realMatrixToCStarMatrix A i j = (A i j : Complex) :=
  rfl

@[simp]
theorem realMatrixToCStarMatrix_zero {n : Nat} :
    realMatrixToCStarMatrix (0 : Matrix (Fin n) (Fin n) Real) = 0 := by
  ext i j
  simp [realMatrixToCStarMatrix]

@[simp]
theorem realMatrixToCStarMatrix_add {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Real) :
    realMatrixToCStarMatrix (A + B) =
      realMatrixToCStarMatrix A + realMatrixToCStarMatrix B := by
  ext i j
  simp [realMatrixToCStarMatrix]

@[simp]
theorem realMatrixToCStarMatrix_neg {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) :
    realMatrixToCStarMatrix (-A) = -realMatrixToCStarMatrix A := by
  ext i j
  simp [realMatrixToCStarMatrix]

@[simp]
theorem realMatrixToCStarMatrix_sub {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Real) :
    realMatrixToCStarMatrix (A - B) =
      realMatrixToCStarMatrix A - realMatrixToCStarMatrix B := by
  ext i j
  simp [realMatrixToCStarMatrix, sub_eq_add_neg]

/-- Self-adjoint real matrices transport to self-adjoint CStar matrices. -/
theorem isSelfAdjoint_realMatrixToCStarMatrix {n : Nat}
    {A : Matrix (Fin n) (Fin n) Real} (hA : IsSelfAdjointMatrix A) :
    IsSelfAdjoint (realMatrixToCStarMatrix A) := by
  rw [IsSelfAdjoint]
  apply CStarMatrix.ext
  intro i j
  rw [CStarMatrix.star_apply]
  have hsym : A j i = A i j := by
    have h := Matrix.IsHermitian.apply hA j i
    simpa using h.symm
  simp [realMatrixToCStarMatrix, hsym]

/-! ## Statement targets for the remaining transport layer -/

/-- Target: strict positivity survives the real-to-CStar representation. -/
abbrev realMatrixToCStarStrictlyPositiveStatement {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) : Prop :=
  IsStrictlyPositive A -> IsStrictlyPositive (realMatrixToCStarMatrix A)

/-- Target: HighDimProb `MatrixLE` survives the real-to-CStar representation. -/
abbrev realMatrixToCStarMatrixLEStatement {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Real) : Prop :=
  MatrixLE A B -> realMatrixToCStarMatrix A <= realMatrixToCStarMatrix B

/-- Target: CStar logarithm commutes with the real-to-CStar representation. -/
abbrev realMatrixToCStarLogBackStatement {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) : Prop :=
  CFC.log (realMatrixToCStarMatrix A) =
    realMatrixToCStarMatrix (CFC.log A)

end

end HighDimProb
