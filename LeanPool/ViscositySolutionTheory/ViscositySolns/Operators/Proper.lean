/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Foundation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Proper and degenerate elliptic operators

This file contains the basic monotonicity hypotheses for fully nonlinear
second-order operators, together with small operator-level constructions used
by the solution theory.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Degenerate ellipticity: `F` is antitone in the Hessian variable for the Loewner
order on matrices. This is condition (0.2) in CIL.
-/
def DegenerateElliptic (F : Operator n) : Prop :=
  forall (x : Point n) (r : Real) (p : Point n) (X Y : Hessian n),
    Y <= X -> F x r p X <= F x r p Y

/--
The operator only depends on the symmetric part of its Hessian argument.

Classical viscosity equations are evaluated on symmetric Hessians; this
predicate records that an operator written on all coordinate matrices ignores
the skew-symmetric part.
-/
def HessianSymmetricInvariant (F : Operator n) : Prop :=
  ∀ (x : Point n) (r : Real) (p : Point n) (X : Hessian n),
    F x r p X = F x r p (symHessian X)

/--
Properness: `F` is nondecreasing in the scalar variable and degenerate elliptic.
This packages the two monotonicity assumptions in CIL condition (0.1).
-/
def Proper (F : Operator n) : Prop :=
  (forall (x : Point n) (p : Point n) (X : Hessian n) {r s : Real},
    r <= s -> F x r p X <= F x s p X) /\
    DegenerateElliptic F

theorem Proper.mono_value {F : Operator n} (hF : Proper F) (x : Point n) (p : Point n)
    (X : Hessian n) {r s : Real} (hrs : r <= s) :
    F x r p X <= F x s p X :=
  hF.1 x p X hrs

theorem Proper.degenerateElliptic {F : Operator n} (hF : Proper F) :
    DegenerateElliptic F :=
  hF.2

/-- Evaluate a second-order operator on a point of the closed-semijet graph space. -/
def operatorGraphEval (F : Operator n) (z : (Point n × Real) × Jet n) : Real :=
  F z.1.1 z.1.2 z.2.gradient z.2.hessian

/--
The negated operator: `negOperator F x r p X = -F x (-r) (-p) (-X)`.

This is the operator for which `-u` is a supersolution whenever `u` is a
subsolution of `F = 0`; it encodes the symmetry principle of CIL Remark 2.6.
-/
def negOperator (F : Operator n) : Operator n :=
  fun x r p X => -F x (-r) (-p) (-X)

@[simp]
theorem negOperator_negOperator (F : Operator n) : negOperator (negOperator F) = F := by
  ext x r p X
  simp [negOperator]

end ViscositySolns
