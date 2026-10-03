/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Operators.Continuity

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Finite suprema and infima of operators

This file contains pointwise finite suprema and infima of second-order
operators. These constructions are the finite-index versions of the
Hamilton-Jacobi-Bellman and Isaacs operators appearing in viscosity theory.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The pointwise supremum of a nonempty finite family of operators.

For each `(x, r, p, X)`, this is the maximum of the finite set of real numbers
`F a x r p X`.
-/
def supOperator {α : Type*} [Fintype α] [Nonempty α] (F : α -> Operator n) :
    Operator n :=
  fun x r p X => Finset.univ.sup' Finset.univ_nonempty fun a => F a x r p X

/--
The pointwise infimum of a nonempty finite family of operators.

For each `(x, r, p, X)`, this is the minimum of the finite set of real numbers
`F a x r p X`.
-/
def infOperator {α : Type*} [Fintype α] [Nonempty α] (F : α -> Operator n) :
    Operator n :=
  fun x r p X => Finset.univ.inf' Finset.univ_nonempty fun a => F a x r p X

@[simp]
theorem supOperator_apply {α : Type*} [Fintype α] [Nonempty α]
    (F : α -> Operator n) (x : Point n) (r : Real) (p : Point n) (X : Hessian n) :
    supOperator F x r p X =
      Finset.univ.sup' Finset.univ_nonempty (fun a => F a x r p X) :=
  rfl

@[simp]
theorem infOperator_apply {α : Type*} [Fintype α] [Nonempty α]
    (F : α -> Operator n) (x : Point n) (r : Real) (p : Point n) (X : Hessian n) :
    infOperator F x r p X =
      Finset.univ.inf' Finset.univ_nonempty (fun a => F a x r p X) :=
  rfl

theorem DegenerateElliptic.supOperator {α : Type*} [Fintype α] [Nonempty α]
    {F : α -> Operator n} (hF : ∀ a : α, DegenerateElliptic (F a)) :
    DegenerateElliptic (supOperator F) := by
  intro x r p X Y hYX
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro a _ha
  exact (hF a x r p X Y hYX).trans
    (Finset.le_sup' (fun b : α => F b x r p Y) (Finset.mem_univ a))

theorem DegenerateElliptic.infOperator {α : Type*} [Fintype α] [Nonempty α]
    {F : α -> Operator n} (hF : ∀ a : α, DegenerateElliptic (F a)) :
    DegenerateElliptic (infOperator F) := by
  intro x r p X Y hYX
  refine Finset.le_inf' Finset.univ_nonempty _ ?_
  intro a _ha
  exact (Finset.inf'_le (fun b : α => F b x r p X) (Finset.mem_univ a)).trans
    (hF a x r p X Y hYX)

theorem Proper.supOperator {α : Type*} [Fintype α] [Nonempty α]
    {F : α -> Operator n} (hF : ∀ a : α, Proper (F a)) :
    Proper (supOperator F) := by
  constructor
  · intro x p X r s hrs
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro a _ha
    exact (hF a).mono_value x p X hrs |>.trans
      (Finset.le_sup' (fun b : α => F b x s p X) (Finset.mem_univ a))
  · exact DegenerateElliptic.supOperator fun a => (hF a).degenerateElliptic

theorem Proper.infOperator {α : Type*} [Fintype α] [Nonempty α]
    {F : α -> Operator n} (hF : ∀ a : α, Proper (F a)) :
    Proper (infOperator F) := by
  constructor
  · intro x p X r s hrs
    refine Finset.le_inf' Finset.univ_nonempty _ ?_
    intro a _ha
    exact (Finset.inf'_le (fun b : α => F b x r p X) (Finset.mem_univ a)).trans
      ((hF a).mono_value x p X hrs)
  · exact DegenerateElliptic.infOperator fun a => (hF a).degenerateElliptic

theorem OperatorContinuous.supOperator {α : Type*} [Fintype α] [Nonempty α]
    {F : α -> Operator n} (hF : ∀ a : α, OperatorContinuous (F a)) :
    OperatorContinuous (supOperator F) := by
  exact
    (Continuous.finset_sup'_apply
      (s := Finset.univ) (f := fun a z => operatorGraphEval (F a) z)
      Finset.univ_nonempty fun a _ha => (hF a).continuous)

theorem OperatorContinuous.infOperator {α : Type*} [Fintype α] [Nonempty α]
    {F : α -> Operator n} (hF : ∀ a : α, OperatorContinuous (F a)) :
    OperatorContinuous (infOperator F) := by
  exact
    (Continuous.finset_inf'_apply
      (s := Finset.univ) (f := fun a z => operatorGraphEval (F a) z)
      Finset.univ_nonempty fun a _ha => (hF a).continuous)

end ViscositySolns
