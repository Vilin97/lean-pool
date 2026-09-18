/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.ComputableReal.ComputableRSeq
public import LeanPool.ComputableReal.ComputableReal
public import LeanPool.ComputableReal.IsComputable
public import LeanPool.ComputableReal.IsComputableC
public import LeanPool.ComputableReal.SpecialFunctions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.Positivity.Finset

/-!
# Verified interval-Cauchy real arithmetic

Source: arxiv:0805.2438, doi:10.1007/978-3-540-71067-7_21
Authors: Alex Meiburg
Status: verified
Main declarations: `ComputableℝSeq`, `Computableℝ`, `IsComputable`
Tags: interval-arithmetic, real-numbers, cauchy-sequences, special-functions
MSC: 65G40, 68V20
-/

@[expose] public section

/-!
A framework for verified interval-Cauchy real arithmetic, after Russell O'Connor,
*Certified exact transcendental real number computation in Coq*, TPHOLs 2008
(doi:10.1007/978-3-540-71067-7_21, arXiv:0805.2438), which carries out the same program:
real numbers presented by converging rational approximations, verified bounds for
elementary functions, and comparisons reduced to interval evaluation. The reference
anchors the overall construction (`ComputableℝSeq`, the quotient field `Computableℝ`)
and the special-function bound sequences for `Real.sqrt`, `Real.exp`, and `Real.pi`.

A `ComputableℝSeq` is an arbitrary function `ℕ → ℚInterval` with proofs that the rational
endpoints converge to a common real value, so it is interval data, not an algorithm in the
computable-analysis sense. Ring arithmetic on sequences (and on the quotient field
`Computableℝ`) is executable interval arithmetic, and the rational bound functions for
`sqrt`/`exp` (`Sqrt.sqrtq`, `Exp.expLb`, `Exp.expUb`) are likewise executable. Comparison,
inversion, and the packaged special-function sequences extract sign information classically
and are `noncomputable`; the `Decidable` instances on comparisons carry no algorithmic
content.
-/
