/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Ideal.Maps

/-!
# Matrix trace reductions for equation (3.3)

This file isolates the matrix implication actually used after Singh--Kumar,
Proposition 3.2, equation (3.3).  The calculation has three coefficient
layers, which must not be conflated.

Over the deformation ring, equation (3.3) produces a strict
upper-triangular remainder and two correction matrices.  The corrections need
not have zero trace there: the source proves separately that each trace lies in
the parameter ideal. Reduction modulo the parameter kills those traces, and a
second map to the coefficient field preserves their vanishing.

In particular, no same-size coefficient-field commutator decomposition is
assumed.  This file does not construct the matrices from a deformation module,
instantiate the localized right-Rees ring, identify the reduced matrix with
the induced `z`-action, or prove the high-power Artinian reduction.
-/

namespace Stafford38.Characteristic.ArtinianEquation33TraceProducer

open Matrix

noncomputable section

universe u

variable {B Abar K : Type u}
variable [Ring B] [CommRing Abar] [Field K]
variable {n : ℕ}

/-- A parameter reduction whose kernel is its principal two-sided ideal. -/
structure ParameterIdealReduction
    (B Abar : Type u) [Ring B] [CommRing Abar] where
  parameter : B
  modParameter : B →+* Abar
  ker_modParameter : RingHom.ker modParameter = Ideal.span {parameter}

/-- Strict upper triangularity over an arbitrary coefficient ring. -/
def IsStrictUpperTriangularOver {S : Type u} [Zero S]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) : Prop :=
  ∀ i j, j ≤ i → M i j = 0

/-- A correction trace has precisely the source-level property used after
equation (3.3): it lies in the parameter ideal before reduction. -/
def CorrectionTraceInParameter
    (S : ParameterIdealReduction B Abar)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) B) : Prop :=
  Matrix.trace Q ∈ Ideal.span {S.parameter}

/-- Coefficientwise reduction of the three terms retained from equation
(3.3), first modulo the parameter and then to the coefficient field.  The
correction matrices are not replaced by coefficient-field commutators. -/
def reducedEquation33Matrix
    (S : ParameterIdealReduction B Abar)
    (residue : Abar →+* K)
    (R Q₁ Q₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) B) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  (R.map S.modParameter).map residue +
    (Q₁.map S.modParameter).map residue +
    (Q₂.map S.modParameter).map residue

/-- A strict upper-triangular deformation-ring remainder stays strict upper
triangular in the Artinian quotient. -/
theorem modParameter_isStrictUpperTriangular
    (S : ParameterIdealReduction B Abar)
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hR : IsStrictUpperTriangularOver R) :
    IsStrictUpperTriangularOver (R.map S.modParameter) := by
  intro i j hji
  simp [Matrix.map_apply, hR i j hji]

/-- A strict upper-triangular matrix over the Artinian quotient has zero
trace, before passing to the coefficient field. -/
theorem modParameter_remainder_trace_eq_zero
    (S : ParameterIdealReduction B Abar)
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hR : IsStrictUpperTriangularOver R) :
    Matrix.trace (R.map S.modParameter) = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro i _hi
  exact modParameter_isStrictUpperTriangular S R hR i i le_rfl

/-- A correction can have nonzero trace before reduction.  Membership of that
trace in the parameter ideal is exactly what makes its trace zero in the
Artinian quotient. -/
theorem modParameter_correction_trace_eq_zero
    (S : ParameterIdealReduction B Abar)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hQ : CorrectionTraceInParameter S Q) :
    Matrix.trace (Q.map S.modParameter) = 0 := by
  have hker : Matrix.trace Q ∈ RingHom.ker S.modParameter := by
    rw [S.ker_modParameter]
    exact hQ
  have hreduce : S.modParameter (Matrix.trace Q) = 0 := hker
  simpa using
    (AddMonoidHom.map_trace S.modParameter.toAddMonoidHom Q).symm.trans hreduce

/-- Zero trace in the Artinian quotient remains zero after the separate
residue/coefficient-field projection. -/
theorem residue_trace_eq_zero
    (residue : Abar →+* K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Abar)
    (hM : Matrix.trace M = 0) :
    Matrix.trace (M.map residue) = 0 := by
  calc
    Matrix.trace (M.map residue) = residue (Matrix.trace M) := by
      simpa using (AddMonoidHom.map_trace residue.toAddMonoidHom M).symm
    _ = 0 := by rw [hM, map_zero]

/-- The separate source reductions imply trace zero for the coefficient-field
matrix represented by equation (3.3). -/
theorem reducedEquation33Matrix_trace_eq_zero
    (S : ParameterIdealReduction B Abar)
    (residue : Abar →+* K)
    (R Q₁ Q₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) B)
    (hR : IsStrictUpperTriangularOver R)
    (hQ₁ : CorrectionTraceInParameter S Q₁)
    (hQ₂ : CorrectionTraceInParameter S Q₂) :
    Matrix.trace (reducedEquation33Matrix S residue R Q₁ Q₂) = 0 := by
  rw [reducedEquation33Matrix, Matrix.trace_add, Matrix.trace_add,
    residue_trace_eq_zero residue (R.map S.modParameter)
      (modParameter_remainder_trace_eq_zero S R hR),
    residue_trace_eq_zero residue (Q₁.map S.modParameter)
      (modParameter_correction_trace_eq_zero S Q₁ hQ₁),
    residue_trace_eq_zero residue (Q₂.map S.modParameter)
      (modParameter_correction_trace_eq_zero S Q₂ hQ₂)]
  simp


end

end Stafford38.Characteristic.ArtinianEquation33TraceProducer
