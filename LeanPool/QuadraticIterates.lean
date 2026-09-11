/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.QuadraticIterates.ArchMath1992
public import LeanPool.QuadraticIterates.ArchMath1992.DegreeCriterion
public import LeanPool.QuadraticIterates.ArchMath1992.Irreducibility
public import LeanPool.QuadraticIterates.ArchMath1992.Iterates
public import LeanPool.QuadraticIterates.ArchMath1992.Main
public import LeanPool.QuadraticIterates.ArchMath1992.Sequences
public import LeanPool.QuadraticIterates.Mathlib.Algebra.BigOperators
public import LeanPool.QuadraticIterates.Mathlib.Algebra.Polynomial.Eval
public import LeanPool.QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp
public import LeanPool.QuadraticIterates.Mathlib.Algebra.Polynomial.Roots
public import LeanPool.QuadraticIterates.Mathlib.Algebra.Squares
public import LeanPool.QuadraticIterates.Mathlib.Data.Int.DvdSequence
public import LeanPool.QuadraticIterates.Mathlib.Data.Multiset
public import LeanPool.QuadraticIterates.Mathlib.Data.Nat
public import LeanPool.QuadraticIterates.Mathlib.Data.ZMod
public import LeanPool.QuadraticIterates.Mathlib.FieldTheory.Multiquadratic
public import LeanPool.QuadraticIterates.Mathlib.GroupTheory.Card
public import LeanPool.QuadraticIterates.Mathlib.GroupTheory.PGroup
public import LeanPool.QuadraticIterates.Mathlib.GroupTheory.RegularWreathProduct
public import LeanPool.QuadraticIterates.Mathlib.NumberTheory.Moebius
public import LeanPool.QuadraticIterates.Mathlib.RingTheory.MoebiusFactor
public import LeanPool.QuadraticIterates.Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Power
import Mathlib.RingTheory.Radical.NatInt

/-!
# Galois groups of quadratic polynomial iterates

Source: doi:10.1007/BF01197321, url:https://github.com/MichaelStollBayreuth/QuadraticIterates
Authors: Michael Stoll
Status: verified
Main declarations: `QuadraticIterates.section3_main`
Tags: arithmetic-dynamics, galois-theory, iterated-polynomials
MSC: 11R32, 12F10, 37P05
-/

@[expose] public section
