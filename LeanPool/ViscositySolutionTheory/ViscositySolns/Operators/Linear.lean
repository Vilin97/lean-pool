/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Operators.Examples

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Affine linear operator forms

This file contains reusable declarations for operators that are affine in the
unknown `r`, the gradient `p`, and the Hessian `X`.

The Hessian contribution is represented by a function `G x X`. Concrete
trace-form linear elliptic operators can later instantiate `G`; the monotonicity
theorems in this file only require the standard antitonicity condition in the
Hessian variable.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
An affine second-order operator of the form
`G x X + b x · p + c x * r - f x`.
-/
def affineSecondOrderOperator (G : Point n -> Hessian n -> Real)
    (b : Point n -> Point n) (c f : Point n -> Real) : Operator n :=
  fun x r p X => G x X + dotProduct (b x) p + c x * r - f x

@[simp]
theorem affineSecondOrderOperator_apply (G : Point n -> Hessian n -> Real)
    (b : Point n -> Point n) (c f : Point n -> Real)
    (x : Point n) (r : Real) (p : Point n) (X : Hessian n) :
    affineSecondOrderOperator G b c f x r p X =
      G x X + dotProduct (b x) p + c x * r - f x :=
  rfl

/--
If the Hessian contribution `G x X` is antitone in `X`, then the affine
operator is degenerate elliptic.
-/
theorem degenerateElliptic_affineSecondOrderOperator
    {G : Point n -> Hessian n -> Real} {b : Point n -> Point n}
    {c f : Point n -> Real}
    (hG : ∀ x : Point n, ∀ X Y : Hessian n, Y <= X -> G x X <= G x Y) :
    DegenerateElliptic (affineSecondOrderOperator G b c f) := by
  intro x r p X Y hYX
  dsimp [affineSecondOrderOperator]
  linarith [hG x X Y hYX]

/--
If the Hessian contribution is antitone in `X` and `0 ≤ c x` for every `x`,
then the affine operator is proper.
-/
theorem proper_affineSecondOrderOperator
    {G : Point n -> Hessian n -> Real} {b : Point n -> Point n}
    {c f : Point n -> Real}
    (hG : ∀ x : Point n, ∀ X Y : Hessian n, Y <= X -> G x X <= G x Y)
    (hc : ∀ x : Point n, 0 <= c x) :
    Proper (affineSecondOrderOperator G b c f) := by
  constructor
  · intro x p X r s hrs
    dsimp [affineSecondOrderOperator]
    have hmul : c x * r <= c x * s := mul_le_mul_of_nonneg_left hrs (hc x)
    linarith
  · exact degenerateElliptic_affineSecondOrderOperator hG

/--
Continuity of an affine second-order operator follows from continuity of its
four graph-space summands.
-/
theorem operatorContinuous_affineSecondOrderOperator
    {G : Point n -> Hessian n -> Real} {b : Point n -> Point n}
    {c f : Point n -> Real}
    (hG : Continuous fun z : (Point n × Real) × Jet n => G z.1.1 z.2.hessian)
    (hb : Continuous fun z : (Point n × Real) × Jet n => dotProduct (b z.1.1) z.2.gradient)
    (hc : Continuous fun z : (Point n × Real) × Jet n => c z.1.1 * z.1.2)
    (hf : Continuous fun z : (Point n × Real) × Jet n => f z.1.1) :
    OperatorContinuous (affineSecondOrderOperator G b c f) := by
  exact
    ((hG.add hb).add hc).sub hf

/-- A first-order operator, independent of its Hessian argument. -/
def firstOrderOperator (G : Point n -> Real -> Point n -> Real) : Operator n :=
  fun x r p _X => G x r p

@[simp]
theorem firstOrderOperator_apply (G : Point n -> Real -> Point n -> Real)
    (x : Point n) (r : Real) (p : Point n) (X : Hessian n) :
    firstOrderOperator G x r p X = G x r p :=
  rfl

theorem degenerateElliptic_firstOrderOperator
    (G : Point n -> Real -> Point n -> Real) :
    DegenerateElliptic (firstOrderOperator (n := n) G) :=
  degenerateElliptic_of_independent_hessian G

theorem proper_firstOrderOperator
    {G : Point n -> Real -> Point n -> Real}
    (hmono : ∀ x : Point n, ∀ p : Point n, Monotone fun r : Real => G x r p) :
    Proper (firstOrderOperator (n := n) G) :=
  proper_of_independent_hessian G hmono

/--
Continuity of a first-order operator follows from continuity of its graph-space
expression.
-/
theorem operatorContinuous_firstOrderOperator
    {G : Point n -> Real -> Point n -> Real}
    (hG : Continuous fun z : (Point n × Real) × Jet n => G z.1.1 z.1.2 z.2.gradient) :
    OperatorContinuous (firstOrderOperator (n := n) G) := by
  exact hG

/-- A zero-order operator, independent of gradient and Hessian arguments. -/
def zeroOrderOperator (g : Point n -> Real -> Real) : Operator n :=
  fun x r _p _X => g x r

@[simp]
theorem zeroOrderOperator_apply (g : Point n -> Real -> Real)
    (x : Point n) (r : Real) (p : Point n) (X : Hessian n) :
    zeroOrderOperator g x r p X = g x r :=
  rfl

theorem degenerateElliptic_zeroOrderOperator (g : Point n -> Real -> Real) :
    DegenerateElliptic (zeroOrderOperator (n := n) g) :=
  degenerateElliptic_of_independent_hessian fun x r _p => g x r

theorem proper_zeroOrderOperator {g : Point n -> Real -> Real}
    (hmono : ∀ x : Point n, Monotone fun r : Real => g x r) :
    Proper (zeroOrderOperator (n := n) g) :=
  proper_of_independent_hessian (fun x r _p => g x r) fun x _p => hmono x

/--
Continuity of a zero-order operator follows from continuity of its graph-space
expression.
-/
theorem operatorContinuous_zeroOrderOperator
    {g : Point n -> Real -> Real}
    (hg : Continuous fun z : (Point n × Real) × Jet n => g z.1.1 z.1.2) :
    OperatorContinuous (zeroOrderOperator (n := n) g) := by
  exact hg

end ViscositySolns
