/-
Copyright (c) 2026 Bhavik Mehta, Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Arend Mellendijk
-/

import LeanPool.ABCExceptions.ForMathlib
import LeanPool.ABCExceptions.Section2
import LeanPool.ABCExceptions.Section4

/-!
# Exceptional Set in the abc Conjecture

Source: arxiv:2410.12234
Authors: Bhavik Mehta, Arend Mellendijk
Status: verified
Main declarations: `abcConjecture_iff_countTriples`, `thm_4_point_3`
Tags: number-theory, analytic-number-theory, abc-conjecture
MSC: 11D75, 11N37
-/

/-!
## Mathematical overview

This project formalizes parts of a proof strategy for bounding the exceptional
set in the abc conjecture, following Browning, Lichtman, and Teräväinen.

`Section2` develops the exceptional triples, dyadic decompositions, nice
factorizations, and the reduction to counting structured boxes.
`Section4` formalizes the linear-optimization step behind the exponent
calculation, including the determinant, Thue, geometry, and Fourier bound
interfaces that imply `thm_4_point_3`.
-/
