/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/
module

public import LeanPool.PolynomialMethodRestrictedSums.ANRPolynomialMethod
public import LeanPool.PolynomialMethodRestrictedSums.CauchyDavenportTheorem
public import LeanPool.PolynomialMethodRestrictedSums.CompressedSizesRestrictedSum
public import LeanPool.PolynomialMethodRestrictedSums.DiasDaSilvaHamidoune
public import LeanPool.PolynomialMethodRestrictedSums.RestrictedSumDistinctSizes
public import LeanPool.PolynomialMethodRestrictedSums.VandermondeCoefficientFormula

/-!
# The polynomial method and restricted sums of congruence classes

Source: url:https://github.com/NickAdfor/The-polynomial-method-and-restricted-sums-of-congruence-classes
Authors: Nick Adfor
Status: verified
Main declarations: `ANR_polynomial_method`, `cauchy_davenport`, `dias_da_silva_hamidoune`
Tags: combinatorics, polynomial-method, alon-tarsi, restricted-sums, congruence-classes
MSC: 11B30, 11B75, 11P70
-/

@[expose] public section

/-!
## Mathematical overview

Formalizes the Alon–Nathanson–Ruzsa polynomial method for restricted sums in a
prime cyclic group `ZMod p`, and derives the Cauchy–Davenport theorem, the
Dias da Silva–Hamidoune bound, the distinct-sizes restricted-sum bound, and a
Vandermonde coefficient formula.

## References

N. Alon, M. B. Nathanson, and I. Z. Ruzsa, *The polynomial method and restricted
sums of congruence classes*, Journal of Number Theory 56 (1996), no. 2, 404-417
(doi:10.1006/jnth.1996.0029). The underlying tool is Alon's Combinatorial
Nullstellensatz, *Combinatorics, Probability and Computing* 8 (1999), 7-29.
-/
