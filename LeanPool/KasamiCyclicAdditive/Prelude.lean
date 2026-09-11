/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.Exponent
public import Mathlib.NumberTheory.LegendreSymbol.Complex
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Polynomial.Dickson
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Ring.RingNF

/-!
# Explicit Mathlib dependencies for the Kasami development

The source project used `import Mathlib` for convenience.  Lean Pool keeps the
dependency surface explicit so that the entry point does not pull in the whole
Mathlib umbrella.
-/

@[expose] public section
