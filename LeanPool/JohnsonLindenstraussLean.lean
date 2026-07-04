/-
Copyright (c) 2026 claytomode. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: claytomode
-/

import LeanPool.JohnsonLindenstraussLean.ChiSquared
import LeanPool.JohnsonLindenstraussLean.EndToEnd
import LeanPool.JohnsonLindenstraussLean.GaussianTail
import LeanPool.JohnsonLindenstraussLean.InnerProduct
import LeanPool.JohnsonLindenstraussLean.Lemma
import LeanPool.JohnsonLindenstraussLean.NormPreservation
import LeanPool.JohnsonLindenstraussLean.Projection
import LeanPool.JohnsonLindenstraussLean.QJL
import LeanPool.JohnsonLindenstraussLean.QJLDistortion
import LeanPool.JohnsonLindenstraussLean.Rotation
import LeanPool.JohnsonLindenstraussLean.SquaredGaussian
import LeanPool.JohnsonLindenstraussLean.Verify

/-!
# The Johnson–Lindenstrauss Lemma and Quantized JL

Source: url:https://github.com/claytomode/johnson-lindenstrauss-lean
Authors: claytomode
Status: verified
Main declarations: `JL.johnson_lindenstrauss`, `JL.johnson_lindenstrauss_pointset`
Tags: dimensionality-reduction, random-projection, johnson-lindenstrauss, gaussian, quantization
MSC: 68W20, 60G15, 68P05
-/

/-!
## Mathematical overview

This project formalizes the Johnson–Lindenstrauss lemma end to end: a random
Gaussian projection into `k` dimensions preserves pairwise distances of a finite
point set up to a `(1 ± ε)` factor with positive probability, so a distortion-`ε`
embedding of any `m`-point set exists once `k` is logarithmic in `m`.

`Projection`, `Rotation`, and `NormPreservation` build the Gaussian random
projection and the per-vector norm-concentration bound from Gaussian rotation
invariance and the chi-squared law (`SquaredGaussian`, `ChiSquared`).
`Lemma` supplies the abstract probabilistic-method union bound
(`JL.johnson_lindenstrauss`), which `EndToEnd` instantiates to the pointset
statement `JL.johnson_lindenstrauss_pointset`.

`InnerProduct`, `QJL`, `GaussianTail`, and `QJLDistortion` develop the quantized
Johnson–Lindenstrauss (QJL) one-bit sign sketch: unbiasedness of the asymmetric
1-bit estimator and its sub-Gaussian distortion/concentration bound.
-/
