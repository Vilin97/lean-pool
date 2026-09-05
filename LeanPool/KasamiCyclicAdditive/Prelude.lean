/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.FunLike.Fintype
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.Exponent
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.Ring.RingNF

/-!
# Explicit Mathlib dependencies for the Kasami development

The source project used `import Mathlib` for convenience.  Lean Pool keeps the
dependency surface explicit so that the entry point does not pull in the whole
Mathlib umbrella.
-/
