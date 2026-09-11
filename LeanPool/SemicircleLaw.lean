/-
Copyright (c) 2026 FredRaj3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FredRaj3
-/
module

public import LeanPool.SemicircleLaw.SemicircleDistribution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# Wigner Semicircle Distribution

Source: url:https://www.math.ucsd.edu/~tkemp/247A.Notes.pdf
Authors: FredRaj3
Status: verified
Main declarations: `LeanPool.SemicircleLaw.integral_semicirclePDFReal_eq_one`
Tags: probability, random-matrix-theory, distributions
MSC: 60B20, 60E05
-/

@[expose] public section

/-!
## Mathematical overview

The Wigner semicircle distribution is the limiting spectral distribution of a
Wigner random matrix, scaled by `1 / √n`. It is supported on `[-2√v, 2√v]`,
where `v` is the variance, with density

  `f(x) = 1 / (2 π v) · √(4 v - (x - μ) ^ 2)`

for `x ∈ [μ - 2√v, μ + 2√v]`. The semicircle law is Theorem 2.3 in Todd Kemp's
Random Matrix Theory notes.

## Main results

- `LeanPool.SemicircleLaw.semicirclePDFReal` — the real-valued probability
  density function of the semicircle distribution.
- `LeanPool.SemicircleLaw.semicirclePDF` — the `ℝ≥0∞`-valued pdf.
- `LeanPool.SemicircleLaw.integral_semicirclePDFReal_eq_one` — the density
  integrates to one for nonzero variance.
- `LeanPool.SemicircleLaw.semicircleReal` — the semicircle measure on `ℝ`,
  parametrized by mean `μ` and variance `v`.
- `LeanPool.SemicircleLaw.semicircleReal_map_add_const` — translating the
  measure translates the mean.
- `LeanPool.SemicircleLaw.semicircleReal_map_const_mul` — scaling the measure
  by a nonzero constant scales the mean and variance parameters.
- `LeanPool.SemicircleLaw.memLp_id_semicircleReal` — the identity has all
  finite `Lᵖ` moments under a semicircle distribution.
-/
