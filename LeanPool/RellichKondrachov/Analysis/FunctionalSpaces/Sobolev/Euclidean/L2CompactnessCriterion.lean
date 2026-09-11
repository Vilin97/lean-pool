/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2CompactnessCriterion`

Aggregator module for the Euclidean `L²` precompactness (Fréchet–Kolmogorov / Riesz–Kolmogorov)
machinery used in the Euclidean Rellich–Kondrachov proof stack.

This is tracked under Beads `lean-103.5.2.26.5.3.2.2.*`.
-/

@[expose] public section
