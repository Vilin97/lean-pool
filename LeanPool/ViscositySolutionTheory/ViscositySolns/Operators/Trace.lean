/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Operators.Linear

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Trace-form linear second-order operators

This file records the standard trace-form Hessian contribution

`X ↦ - trace ((A x) * X)`.

In the usual elliptic case, `A x` is positive semidefinite for every `x`.
The matrix lemma connecting that hypothesis to monotonicity is kept as a
separate future theorem: if `A x` is positive semidefinite and `Y ≤ X`, then
`- trace ((A x) * X) ≤ - trace ((A x) * Y)`.
-/

@[expose] public noncomputable section

open Matrix
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/-- The Hessian contribution `- trace ((A x) * X)`. -/
def traceHessianContribution (A : Point n -> Hessian n) (x : Point n)
    (X : Hessian n) : Real :=
  -Matrix.trace (A x * X)

/--
The linear second-order operator
`- trace ((A x) * X) + b x · p + c x * r - f x`.
-/
def traceSecondOrderOperator (A : Point n -> Hessian n)
    (b : Point n -> Point n) (c f : Point n -> Real) : Operator n :=
  affineSecondOrderOperator (traceHessianContribution A) b c f

@[simp]
theorem traceHessianContribution_apply (A : Point n -> Hessian n)
    (x : Point n) (X : Hessian n) :
    traceHessianContribution A x X = -Matrix.trace (A x * X) :=
  rfl

@[simp]
theorem traceSecondOrderOperator_apply (A : Point n -> Hessian n)
    (b : Point n -> Point n) (c f : Point n -> Real)
    (x : Point n) (r : Real) (p : Point n) (X : Hessian n) :
    traceSecondOrderOperator A b c f x r p X =
      -Matrix.trace (A x * X) + dotProduct (b x) p + c x * r - f x :=
  rfl

/--
If for every `x`, `X`, and `Y`, the implication
`Y ≤ X -> - trace ((A x) * X) ≤ - trace ((A x) * Y)` holds, then the
trace-form operator is degenerate elliptic.
-/
theorem degenerateElliptic_traceSecondOrderOperator
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (hA : ∀ x : Point n, ∀ X Y : Hessian n, Y <= X ->
      -Matrix.trace (A x * X) <= -Matrix.trace (A x * Y)) :
    DegenerateElliptic (traceSecondOrderOperator A b c f) :=
  degenerateElliptic_affineSecondOrderOperator hA

/--
If the trace-form Hessian contribution is antitone in the Loewner order and
`0 ≤ c x` for every `x`, then the trace-form operator is proper.
-/
theorem proper_traceSecondOrderOperator
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (hA : ∀ x : Point n, ∀ X Y : Hessian n, Y <= X ->
      -Matrix.trace (A x * X) <= -Matrix.trace (A x * Y))
    (hc : ∀ x : Point n, 0 <= c x) :
    Proper (traceSecondOrderOperator A b c f) :=
  proper_affineSecondOrderOperator hA hc

/--
Continuity of the trace-form operator follows from continuity of the
trace-form Hessian summand and the other affine summands.
-/
theorem operatorContinuous_traceSecondOrderOperator
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (hA : Continuous fun z : (Point n × Real) × Jet n =>
      -Matrix.trace (A z.1.1 * z.2.hessian))
    (hb : Continuous fun z : (Point n × Real) × Jet n => dotProduct (b z.1.1) z.2.gradient)
    (hc : Continuous fun z : (Point n × Real) × Jet n => c z.1.1 * z.1.2)
    (hf : Continuous fun z : (Point n × Real) × Jet n => f z.1.1) :
    OperatorContinuous (traceSecondOrderOperator A b c f) :=
  operatorContinuous_affineSecondOrderOperator hA hb hc hf

/--
If `A` and `B` are positive semidefinite real matrices, then
`0 ≤ trace (A * B)`.
-/
theorem trace_mul_nonneg_of_posSemidef {A B : Hessian n}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 <= Matrix.trace (A * B) := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  subst A
  simp only [star_eq_conjTranspose]
  have hcycle₁ :
      Matrix.trace ((Sᴴ * S) * B) = Matrix.trace (B * Sᴴ * S) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle Sᴴ S B
  have hcycle₂ :
      Matrix.trace (B * Sᴴ * S) = Matrix.trace (S * B * Sᴴ) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle B Sᴴ S
  rw [hcycle₁, hcycle₂]
  exact (hB.mul_mul_conjTranspose_same S).trace_nonneg

/--
If `A` is positive semidefinite and `Y ≤ X`, then the trace-form Hessian
contribution is antitone:
`- trace (A * X) ≤ - trace (A * Y)`.
-/
theorem trace_mul_antitone_of_posSemidef {A : Hessian n}
    (hA : A.PosSemidef) :
    ∀ X Y : Hessian n, Y <= X ->
      -Matrix.trace (A * X) <= -Matrix.trace (A * Y) := by
  intro X Y hYX
  have hdiff : (X - Y).PosSemidef := Matrix.le_iff.mp hYX
  have hnonneg : 0 <= Matrix.trace (A * (X - Y)) :=
    trace_mul_nonneg_of_posSemidef hA hdiff
  have htrace :
      Matrix.trace (A * (X - Y)) = Matrix.trace (A * X) - Matrix.trace (A * Y) := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  linarith

/--
If `A x` is positive semidefinite for every `x`, then the trace-form operator
is degenerate elliptic.
-/
theorem degenerateElliptic_traceSecondOrderOperator_of_posSemidef
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (hA : ∀ x : Point n, (A x).PosSemidef) :
    DegenerateElliptic (traceSecondOrderOperator A b c f) :=
  degenerateElliptic_traceSecondOrderOperator fun x =>
    trace_mul_antitone_of_posSemidef (hA x)

/--
If `A x` is positive semidefinite and `0 ≤ c x` for every `x`, then the
trace-form operator is proper.
-/
theorem proper_traceSecondOrderOperator_of_posSemidef
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (hA : ∀ x : Point n, (A x).PosSemidef) (hc : ∀ x : Point n, 0 <= c x) :
    Proper (traceSecondOrderOperator A b c f) :=
  proper_traceSecondOrderOperator (fun x => trace_mul_antitone_of_posSemidef (hA x)) hc

/--
For a diagonal coefficient matrix with nonnegative diagonal entries, the
trace-form Hessian contribution is antitone in the Loewner order:
if `Y ≤ X`, then
`- trace ((diagonal a) * X) ≤ - trace ((diagonal a) * Y)`.
-/
theorem trace_diagonal_mul_antitone_of_nonneg
    {a : Fin n -> Real} (ha : ∀ i : Fin n, 0 <= a i) :
    ∀ X Y : Hessian n, Y <= X ->
      -Matrix.trace (Matrix.diagonal a * X) <= -Matrix.trace (Matrix.diagonal a * Y) := by
  intro X Y hYX
  have hdiff : (X - Y).PosSemidef := Matrix.le_iff.mp hYX
  have hdiag : ∀ i : Fin n, Y i i <= X i i := by
    intro i
    have hi : 0 <= (X - Y) i i := hdiff.diag_nonneg
    simpa using hi
  have htrace :
      Matrix.trace (Matrix.diagonal a * Y) <= Matrix.trace (Matrix.diagonal a * X) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hYsum : (∑ j : Fin n, Matrix.diagonal a i j * Y j i) = a i * Y i i := by
      rw [Finset.sum_eq_single i]
      · simp [Matrix.diagonal]
      · intro j _hj hji
        have hij : i ≠ j := fun hij => hji hij.symm
        simp [Matrix.diagonal, hij]
      · intro h_empty
        exact (h_empty (Finset.mem_univ i)).elim
    have hXsum : (∑ j : Fin n, Matrix.diagonal a i j * X j i) = a i * X i i := by
      rw [Finset.sum_eq_single i]
      · simp [Matrix.diagonal]
      · intro j _hj hji
        have hij : i ≠ j := fun hij => hji hij.symm
        simp [Matrix.diagonal, hij]
      · intro h_empty
        exact (h_empty (Finset.mem_univ i)).elim
    rw [hYsum, hXsum]
    exact mul_le_mul_of_nonneg_left (hdiag i) (ha i)
  linarith

/--
The trace-form operator with a diagonal nonnegative Hessian coefficient is
degenerate elliptic.
-/
theorem degenerateElliptic_traceSecondOrderOperator_diagonal
    {a : Point n -> Fin n -> Real} {b : Point n -> Point n} {c f : Point n -> Real}
    (ha : ∀ x : Point n, ∀ i : Fin n, 0 <= a x i) :
    DegenerateElliptic
      (traceSecondOrderOperator (fun x => Matrix.diagonal (a x)) b c f) :=
  degenerateElliptic_traceSecondOrderOperator fun x =>
    trace_diagonal_mul_antitone_of_nonneg (ha x)

/--
The trace-form operator with a diagonal nonnegative Hessian coefficient and
`0 ≤ c x` is proper.
-/
theorem proper_traceSecondOrderOperator_diagonal
    {a : Point n -> Fin n -> Real} {b : Point n -> Point n} {c f : Point n -> Real}
    (ha : ∀ x : Point n, ∀ i : Fin n, 0 <= a x i)
    (hc : ∀ x : Point n, 0 <= c x) :
    Proper (traceSecondOrderOperator (fun x => Matrix.diagonal (a x)) b c f) :=
  proper_traceSecondOrderOperator
    (fun x => trace_diagonal_mul_antitone_of_nonneg (ha x)) hc

end ViscositySolns
