/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/
module

public import LeanPool.PythagoreanPolynomialParametrization.Main
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset

/-!
# Polynomial parametrizations of Pythagorean triples

Source: arxiv:0706.0290, doi:10.1016/j.jpaa.2007.05.019
Authors: Lazar Milikic
Status: verified
Main declarations: `LeanPool.PythagoreanPolynomialParametrization.exists_int_valued_parametrization`
Tags: number-theory, pythagorean-triples, integer-valued-polynomials
MSC: 11D09, 11D85, 13F20
-/

@[expose] public section
