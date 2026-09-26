/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff


/-!
# The Artinian triangular trace calculation

This file formalizes the terminal finite-dimensional trace core used in
Singh--Kumar, Proposition 3.2.
After choosing a coefficient field in the commutative Artinian special fibre
and a basis adapted to powers of its maximal ideal, the action of a lifted
maximal-ideal element is strictly triangular.  The first-order commutator
calculation then represents the bracket-cofactor action as

`R + (ΘA - AΘ) + (BΓ - ΓB)`,

where `R` is strictly upper triangular.  Its trace is zero.  On the other
hand, the residue decomposition of that action is a scalar matrix plus a
nilpotent matrix.  In positive dimension and characteristic zero the scalar
must therefore vanish.

The faithful terminal theorem assumes only that the induced operator has trace
zero.  This is exactly what the source proves from equation (3.3); it does not
identify the correction terms with commutators of same-size matrices over the
coefficient field.  A stronger commutator-shaped corollary is retained as an
abstract convenience, but is not claimed to follow directly from the source.

This file does not construct the coefficient field or adapted basis, derive
the trace-zero operator from a square-zero module, or connect it to the
localized right Rees module.
-/

@[expose] public section

namespace Stafford38.Characteristic.ArtinianTriangularTrace

open Matrix

noncomputable section

universe u

variable {K : Type u} [Field K]
variable {n : ℕ}

/-- A square matrix is strictly upper triangular when every entry on or below
the diagonal is zero. -/
def IsStrictUpperTriangular
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : Prop :=
  ∀ i j, j ≤ i → M i j = 0

/-- A strictly upper triangular matrix has zero trace. -/
theorem trace_eq_zero_of_isStrictUpperTriangular
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hM : IsStrictUpperTriangular M) :
    Matrix.trace M = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro i _hi
  exact hM i i le_rfl

/-- Written-order matrix commutator. -/
def matrixCommutator
    (X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  X * Y - Y * X

/-- Cyclicity of matrix trace kills a matrix commutator over the coefficient
field. -/
theorem trace_matrixCommutator_eq_zero
    (X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix.trace (matrixCommutator X Y) = 0 := by
  rw [matrixCommutator, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- The matrix left after the maximal-ideal-adapted first-order calculation.
The order of both commutators is the order occurring in the published
calculation. -/
def adaptedFirstOrderMatrix
    (R Θ A B Γ : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  R + matrixCommutator Θ A + matrixCommutator B Γ

/-- The adapted first-order matrix has trace zero.  No triangularity of
`A`, `B`, `Γ`, or `Θ` is needed after the calculation has isolated the
strictly triangular remainder `R`. -/
theorem trace_adaptedFirstOrderMatrix_eq_zero
    (R Θ A B Γ : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hR : IsStrictUpperTriangular R) :
    Matrix.trace (adaptedFirstOrderMatrix R Θ A B Γ) = 0 := by
  simp only [adaptedFirstOrderMatrix, Matrix.trace_add,
    trace_eq_zero_of_isStrictUpperTriangular hR,
    trace_matrixCommutator_eq_zero, zero_add]

/-- Faithful terminal trace calculation used by Proposition 3.2.

The source-specific work upstream proves that the induced operator `T` has
trace zero.  The coefficient-field decomposition gives `q I + U = T`, where
maximal-ideal multiplication makes `U` nilpotent.  Positive dimension and
characteristic zero then force `q = 0`.
-/
theorem scalar_eq_zero_of_trace_identity
    [CharZero K]
    (q : K)
    (U T : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hU : IsNilpotent U)
    (htraceT : Matrix.trace T = 0)
    (hidentity :
      q • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) + U = T) :
    q = 0 := by
  have htraceU : Matrix.trace U = 0 := by
    exact isNilpotent_iff_eq_zero.mp
      (Matrix.isNilpotent_trace_of_isNilpotent hU)
  have htrace := congrArg Matrix.trace hidentity
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, htraceU,
    add_zero, htraceT, smul_eq_mul] at htrace
  exact (mul_eq_zero.mp htrace).resolve_right
    (Nat.cast_ne_zero.mpr (by simp))

/-- Stronger abstract corollary with an explicit commutator decomposition.

This implication is correct, but Proposition 3.2 does not directly provide its
same-size coefficient-field matrix identity.  The source-specific adapter
should instead establish the zero-trace hypothesis of
`scalar_eq_zero_of_trace_identity`.
-/
theorem scalar_eq_zero_of_adapted_triangular_matrix_identity
    [CharZero K]
    (q : K)
    (U R Θ A B Γ : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hU : IsNilpotent U)
    (hR : IsStrictUpperTriangular R)
    (hidentity :
      q • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) + U =
        adaptedFirstOrderMatrix R Θ A B Γ) :
    q = 0 :=
  scalar_eq_zero_of_trace_identity q U
    (adaptedFirstOrderMatrix R Θ A B Γ) hU
    (trace_adaptedFirstOrderMatrix_eq_zero R Θ A B Γ hR) hidentity


end

end Stafford38.Characteristic.ArtinianTriangularTrace
