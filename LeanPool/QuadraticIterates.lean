/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

import LeanPool.QuadraticIterates.ArchMath1992
import LeanPool.QuadraticIterates.ArchMath1992.DegreeCriterion
import LeanPool.QuadraticIterates.ArchMath1992.Irreducibility
import LeanPool.QuadraticIterates.ArchMath1992.Iterates
import LeanPool.QuadraticIterates.ArchMath1992.Main
import LeanPool.QuadraticIterates.ArchMath1992.Sequences
import LeanPool.QuadraticIterates.Mathlib.Algebra.BigOperators
import LeanPool.QuadraticIterates.Mathlib.Algebra.Polynomial.Eval
import LeanPool.QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp
import LeanPool.QuadraticIterates.Mathlib.Algebra.Polynomial.Roots
import LeanPool.QuadraticIterates.Mathlib.Algebra.Squares
import LeanPool.QuadraticIterates.Mathlib.Data.Int.DvdSequence
import LeanPool.QuadraticIterates.Mathlib.Data.Multiset
import LeanPool.QuadraticIterates.Mathlib.Data.Nat
import LeanPool.QuadraticIterates.Mathlib.Data.ZMod
import LeanPool.QuadraticIterates.Mathlib.FieldTheory.Multiquadratic
import LeanPool.QuadraticIterates.Mathlib.GroupTheory.Card
import LeanPool.QuadraticIterates.Mathlib.GroupTheory.PGroup
import LeanPool.QuadraticIterates.Mathlib.GroupTheory.RegularWreathProduct
import LeanPool.QuadraticIterates.Mathlib.NumberTheory.Moebius
import LeanPool.QuadraticIterates.Mathlib.RingTheory.MoebiusFactor
import LeanPool.QuadraticIterates.Mathlib.RingTheory.UniqueFactorizationDomain

/-!
# Galois groups of quadratic polynomial iterates

Source: doi:10.1007/BF01197321, url:https://github.com/MichaelStollBayreuth/QuadraticIterates
Authors: Michael Stoll
Status: verified
Main declarations: `QuadraticIterates.section3_main`
Tags: arithmetic-dynamics, galois-theory, iterated-polynomials
MSC: 11R32, 12F10, 37P05
-/
