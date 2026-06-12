/-
Copyright (c) 2026 Stefan Barańczuk, Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Barańczuk, Aristotle
-/

import LeanPool.Fineqs.Main

/-!
# FinEqs - reducing equations defining a subset of n-space over a finite field

Source: arxiv:1906.11174, doi:10.5802/afst.1766
Authors: Stefan Barańczuk, Aristotle
Status: verified
Main declarations: `LeanPool.Fineqs.theorem_1`, `LeanPool.Fineqs.prop_1`
Tags: number-theory, finite-fields, algebraic-geometry
MSC: 14G15, 11T06
-/

/-!
## Mathematical overview

This project formalizes the main reduction theorem and sharpness examples from the paper
"Reducing the number of equations defining a subset of the n-space over a finite field"
by Stefan Barańczuk ([arXiv:1906.11174](https://arxiv.org/abs/1906.11174)). The
formalization was performed with the software Aristotle by Harmonic.

## Main result

- `LeanPool.Fineqs.theorem_1`: reduces a finite family of equations on a small finite
  set to at most `n` equations in the same span without changing the zero set.
- `LeanPool.Fineqs.prop_1`: shows the cardinality bound in `theorem_1` is sharp.
- `LeanPool.Fineqs.corollary_2` and `LeanPool.Fineqs.corollary_3`: apply the
  reduction theorem to affine and projective space.
- `LeanPool.Fineqs.remark_example`: formalizes the coordinate-function example from
  the paper's remark.
-/
