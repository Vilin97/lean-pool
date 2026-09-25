/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.Theorem

/-!
# Spectral-continuation implementation index

The original version of this module contained a second, speculative contour
API.  None of those declarations was referenced elsewhere, and the repository
subsequently completed the same mathematics with a stronger proof-carrying
interface:

* `PiecewiseC1ClosedContour` records the Mathlib path and its finite `C1`
  partition;
* `SpectralSeparatingContour` records self-adjointness, measurability, a
  positive contour-to-spectrum margin, and the two winding laws;
* `fixedContourRieszOperator` is the normalized operator-valued curve
  integral;
* the continuation transport modules prove quantitative Lipschitz control,
  finite subdivision into norm-close projections, composition of local direct
  rotations, spectral identification, and endpoint unitary transport;
* `SpectralContinuationWitness` packages the hypotheses of the final selected
  spectral-subspace theorem.

This import-only module preserves the old roadmap path while exposing the
completed implementation.  New developments should depend on the concrete
modules directly rather than introducing another contour representation.
-/

@[expose] public section
