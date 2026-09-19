/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import LeanPool.EcTateLean.Algebra.CharP.Basic
public import LeanPool.EcTateLean.Algebra.EllipticCurve.AuxRingLemmas
public import LeanPool.EcTateLean.Algebra.EllipticCurve.KodairaTypes
public import LeanPool.EcTateLean.Algebra.EllipticCurve.Kronecker
public import LeanPool.EcTateLean.Algebra.EllipticCurve.Model
public import LeanPool.EcTateLean.Algebra.Ring.Basic
public import LeanPool.EcTateLean.FieldTheory.PerfectClosure
public import LeanPool.EcTateLean.Init.Data.Int.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Weierstrass models and singular points for Tate's algorithm

Source: url:https://www.math.rug.nl/~top/ian.pdf
Authors: Sacha H., Sander R. Dahmen, Anne Baanen, Alex J. Best
Status: verified
Main declarations: `Model`, `Model.Field.isSingularPoint_singularPoint`
Tags: number-theory, elliptic-curves, algebraic-geometry
MSC: 11G05, 11G07, 14H52
-/

@[expose] public section

/-!
This is the foundational layer of the `ec-tate-lean` formalization of Tate's
algorithm. It defines Weierstrass `Model`s over a commutative ring, their
`b`/`c`-invariants and discriminant, the `rst`/`urst` change-of-coordinates
group action, and proves the classical invariant identities together with the
fact that the discriminant lies in the Jacobian ideal of the Weierstrass
polynomial. Over a perfect field it constructs the singular point of a singular
model (Connell, Proposition 1.5.4) and proves it is singular. The `Kodaira`
enumeration of reduction types is included as supporting data.
-/
