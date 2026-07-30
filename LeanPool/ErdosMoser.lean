/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.ErdosMoser.Bounds

/-!
# Leo Moser's finite distinct-subset-sums inequality

Source: doi:10.1016/S0304-0208(08)73500-X, url:https://www.erdosproblems.com/1
Authors: Egor Lyfar
Status: verified
Main declarations: `LeanPool.ErdosMoser.leoMoserVarianceBound`
Tags: additive-combinatorics, number-theory, distinct-subset-sums, erdos-problems
MSC: 11B13, 11B75
-/

/-!
Guy's 1982 account states the exact finite sum-of-squares inequality as
Theorem 2 and attributes it to Leo Moser. This project formalizes that
inequality and derives two finite lower bounds for the largest element of a
set with distinct subset sums.

The stronger historical asymptotic bound attributed jointly to Erdős and
Moser is not claimed here, and Erdős Problem 1 remains open.
-/
