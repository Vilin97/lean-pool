/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/
module

public import LeanPool.PythagoreanPolynomialParametrization.Basic
public import LeanPool.PythagoreanPolynomialParametrization.SourceLemmas
public import LeanPool.PythagoreanPolynomialParametrization.Obstructions
public import LeanPool.PythagoreanPolynomialParametrization.IntegerValued
public import LeanPool.PythagoreanPolynomialParametrization.Positive
public import LeanPool.PythagoreanPolynomialParametrization.Explanatory

/-! # Parametrization of Pythagorean Triples by Polynomials

This directory sets up source-backed Lean statements for results from Frisch and
Vaserstein's paper "Parametrization of Pythagorean triples by a single triple of
polynomials". Externally cited or explanatory source claims are recorded separately
from the main parametrization proofs.

## File layout

- `Basic`: shared definitions of Pythagorean triples, integer-valued polynomials,
  and parametrization predicates.
- `SourceLemmas`: source-level proof handoff lemmas for the `T(a,b,c)` map, parity
  conditions, positive parameters, and four-square substitutions.
- `Obstructions`: no single integer-coefficient polynomial triple parametrizes all
  Pythagorean triples.
- `IntegerValued`: the explicit four-variable integer-valued parametrization of all
  Pythagorean triples.
- `Positive`: the positive-triple parametrization and the 16-parameter unrestricted
  variant.
- `Explanatory`: reusable finite-family parametrization statements, the cited
  finite-cover theorem, and the integer-valued factorization discussion.
-/

@[expose] public section

namespace LeanPool.PythagoreanPolynomialParametrization



end LeanPool.PythagoreanPolynomialParametrization
