/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Hu Yongle, Zou Wenrong, Sun Tiantong, LeiBichang, Prowler99
-/

import LeanPool.Neukirch.AlgebraicIntegersPart1.GaussianIntegers
import LeanPool.Neukirch.AlgebraicIntegersPart2.CyclotomicFields
import LeanPool.Neukirch.AlgebraicIntegersPart2.ExtensionOfDedekindDomains
import LeanPool.Neukirch.AlgebraicIntegersPart2.HilbertRamificationTheory
import LeanPool.Neukirch.AlgebraicIntegersPart2.Localization
import LeanPool.Neukirch.Valuation.AddToMathlib
import LeanPool.Neukirch.ValuationTheory.Completions
import LeanPool.Neukirch.ValuationTheory.LocalField
import LeanPool.Neukirch.ValuationTheory.PAdic
import LeanPool.Neukirch.ValuationTheory.ThePadicNumbers
import LeanPool.Neukirch.ValuationTheory.Valuation
import LeanPool.Neukirch.ValuationTheory.Xadic
import LeanPool.Neukirch.ValuationTheory.power
import LeanPool.Neukirch.ValuationTheory.trivia

/-!
# Neukirch's Algebraic Number Theory — selected formalizations

Source: url:https://github.com/jjdishere/neukirch
Authors: Jiedong Jiang, Hu Yongle, Zou Wenrong, Sun Tiantong, LeiBichang, Prowler99
Status: vendor-only (proofs not ported; many `sorry`s remain upstream)
Main declarations: `DecompositionGroup`, `InertiaGroup`,
  `finrank_eq_ramificationIdx_mul_inertiaDeg`
Tags: number-theory, algebraic-number-theory, dedekind-domains, ramification,
  valuation-theory, p-adic
MSC: 11R04, 11R32, 11S15, 13F30
-/

/-!
## Provenance

Vendored from <https://github.com/jjdishere/neukirch>, a Lean formalization of
selected results from Neukirch's *Algebraic Number Theory*. Upstream uses Lean
v4.5.0-rc1 and is Apache-2.0 licensed (license added by the author at our
request on 2026-05-22). This vendor-only import does not port proofs; many
upstream files still contain `sorry`/`admit`.
-/
