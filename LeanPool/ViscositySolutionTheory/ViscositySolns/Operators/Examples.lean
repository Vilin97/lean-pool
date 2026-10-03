/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Operators.Continuity

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Basic examples of proper operators

This file collects small reusable constructors for operators satisfying the
monotonicity, continuity, and boundedness hypotheses used in the viscosity
solution theory.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/-- The constant operator. -/
def constOperator (c : Real) : Operator n :=
  fun _x _r _p _X => c

/-- Pointwise sum of two operators. -/
def addOperator (F G : Operator n) : Operator n :=
  fun x r p X => F x r p X + G x r p X

/-- Scalar multiple of an operator. -/
def smulOperator (a : Real) (F : Operator n) : Operator n :=
  fun x r p X => a * F x r p X

@[simp]
theorem constOperator_apply (c : Real) (x : Point n) (r : Real) (p : Point n)
    (X : Hessian n) :
    constOperator c x r p X = c :=
  rfl

@[simp]
theorem addOperator_apply (F G : Operator n) (x : Point n) (r : Real) (p : Point n)
    (X : Hessian n) :
    addOperator F G x r p X = F x r p X + G x r p X :=
  rfl

@[simp]
theorem smulOperator_apply (a : Real) (F : Operator n) (x : Point n) (r : Real)
    (p : Point n) (X : Hessian n) :
    smulOperator a F x r p X = a * F x r p X :=
  rfl

/--
An operator independent of its Hessian argument is automatically degenerate
elliptic.
-/
theorem degenerateElliptic_of_independent_hessian (G : Point n -> Real -> Point n -> Real) :
    DegenerateElliptic (fun x r p _X => G x r p) := by
  intro x r p X Y hYX
  exact le_rfl

/--
An operator independent of its Hessian argument is proper when it is monotone in
the scalar argument.
-/
theorem proper_of_independent_hessian (G : Point n -> Real -> Point n -> Real)
    (hmono : forall (x : Point n) (p : Point n), Monotone (fun r : Real => G x r p)) :
    Proper (fun x r p _X => G x r p) := by
  constructor
  · intro x p X r s hrs
    exact hmono x p hrs
  · exact degenerateElliptic_of_independent_hessian G

/-- The zero operator is proper. -/
theorem proper_zero_operator : Proper (fun (_x : Point n) (_r : Real) (_p : Point n)
    (_X : Hessian n) => (0 : Real)) := by
  constructor
  · intro x p X r s hrs
    exact le_rfl
  · intro x r p X Y hYX
    exact le_rfl

theorem degenerateElliptic_constOperator (c : Real) :
    DegenerateElliptic (constOperator (n := n) c) :=
  degenerateElliptic_of_independent_hessian (fun _x _r _p => c)

theorem proper_constOperator (c : Real) :
    Proper (constOperator (n := n) c) :=
  proper_of_independent_hessian (fun _x _r _p => c) fun _x _p _r _s _hrs => le_rfl

theorem DegenerateElliptic.add {F G : Operator n}
    (hF : DegenerateElliptic F) (hG : DegenerateElliptic G) :
    DegenerateElliptic (addOperator F G) := by
  intro x r p X Y hYX
  exact add_le_add (hF x r p X Y hYX) (hG x r p X Y hYX)

theorem Proper.add {F G : Operator n} (hF : Proper F) (hG : Proper G) :
    Proper (addOperator F G) := by
  constructor
  · intro x p X r s hrs
    exact add_le_add (hF.mono_value x p X hrs) (hG.mono_value x p X hrs)
  · exact hF.degenerateElliptic.add hG.degenerateElliptic

theorem DegenerateElliptic.smul_nonneg {F : Operator n} {a : Real}
    (ha : 0 <= a) (hF : DegenerateElliptic F) :
    DegenerateElliptic (smulOperator a F) := by
  intro x r p X Y hYX
  exact mul_le_mul_of_nonneg_left (hF x r p X Y hYX) ha

theorem Proper.smul_nonneg {F : Operator n} {a : Real}
    (ha : 0 <= a) (hF : Proper F) :
    Proper (smulOperator a F) := by
  constructor
  · intro x p X r s hrs
    exact mul_le_mul_of_nonneg_left (hF.mono_value x p X hrs) ha
  · exact hF.degenerateElliptic.smul_nonneg ha

theorem operatorContinuous_constOperator (c : Real) :
    OperatorContinuous (constOperator (n := n) c) := by
  exact
    (continuous_const : Continuous fun _ : (Point n × Real) × Jet n => c)

theorem OperatorContinuous.add {F G : Operator n}
    (hF : OperatorContinuous F) (hG : OperatorContinuous G) :
    OperatorContinuous (addOperator F G) := by
  exact
    hF.continuous.add hG.continuous

theorem OperatorContinuous.smul {F : Operator n} (a : Real)
    (hF : OperatorContinuous F) :
    OperatorContinuous (smulOperator a F) := by
  exact
    (continuous_const.mul hF.continuous : Continuous fun z => a * operatorGraphEval F z)

theorem operatorLocallyBounded_constOperator (c : Real) :
    OperatorLocallyBounded (constOperator (n := n) c) := by
  intro z
  refine ⟨|c|, Filter.Eventually.of_forall ?_⟩
  intro y
  simp [operatorGraphEval, constOperator]

theorem OperatorLocallyBounded.add {F G : Operator n}
    (hF : OperatorLocallyBounded F) (hG : OperatorLocallyBounded G) :
    OperatorLocallyBounded (addOperator F G) := by
  intro z
  rcases hF z with ⟨MF, hMF⟩
  rcases hG z with ⟨MG, hMG⟩
  refine ⟨MF + MG, ?_⟩
  filter_upwards [hMF, hMG] with y hyF hyG
  calc
    |operatorGraphEval (addOperator F G) y| =
        |operatorGraphEval F y + operatorGraphEval G y| := by
      rfl
    _ <= |operatorGraphEval F y| + |operatorGraphEval G y| :=
      abs_add_le (operatorGraphEval F y) (operatorGraphEval G y)
    _ <= MF + MG := add_le_add hyF hyG

theorem OperatorLocallyBounded.smul {F : Operator n} (a : Real)
    (hF : OperatorLocallyBounded F) :
    OperatorLocallyBounded (smulOperator a F) := by
  intro z
  rcases hF z with ⟨M, hM⟩
  refine ⟨|a| * |M|, ?_⟩
  filter_upwards [hM] with y hy
  calc
    |operatorGraphEval (smulOperator a F) y| =
        |a| * |operatorGraphEval F y| := by
      simp [operatorGraphEval, smulOperator, abs_mul]
    _ <= |a| * |M| :=
      mul_le_mul_of_nonneg_left (hy.trans (le_abs_self M)) (abs_nonneg a)

theorem OperatorLocallyBoundedOn.add {S : Set ((Point n × Real) × Jet n)}
    {F G : Operator n}
    (hF : OperatorLocallyBoundedOn S F) (hG : OperatorLocallyBoundedOn S G) :
    OperatorLocallyBoundedOn S (addOperator F G) := by
  intro z hz
  rcases hF z hz with ⟨MF, hMF⟩
  rcases hG z hz with ⟨MG, hMG⟩
  refine ⟨MF + MG, ?_⟩
  filter_upwards [hMF, hMG] with y hyF hyG
  calc
    |operatorGraphEval (addOperator F G) y| =
        |operatorGraphEval F y + operatorGraphEval G y| := by
      rfl
    _ <= |operatorGraphEval F y| + |operatorGraphEval G y| :=
      abs_add_le (operatorGraphEval F y) (operatorGraphEval G y)
    _ <= MF + MG := add_le_add hyF hyG

theorem OperatorLocallyBoundedOn.smul {S : Set ((Point n × Real) × Jet n)}
    {F : Operator n} (a : Real)
    (hF : OperatorLocallyBoundedOn S F) :
    OperatorLocallyBoundedOn S (smulOperator a F) := by
  intro z hz
  rcases hF z hz with ⟨M, hM⟩
  refine ⟨|a| * |M|, ?_⟩
  filter_upwards [hM] with y hy
  calc
    |operatorGraphEval (smulOperator a F) y| =
        |a| * |operatorGraphEval F y| := by
      simp [operatorGraphEval, smulOperator, abs_mul]
    _ <= |a| * |M| :=
      mul_le_mul_of_nonneg_left (hy.trans (le_abs_self M)) (abs_nonneg a)

end ViscositySolns
