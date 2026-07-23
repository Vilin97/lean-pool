/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsSpindle

/-!
# Known Bounds for the Hadwiger-Nelson Problem

Source: arxiv:2010.12661, url:https://www.erdosproblems.com/508
Authors: Egor Lyfar
Status: verified
Main declarations: `HadwigerNelsonBounds.hadwiger_nelson_known_bounds`
Tags: graph-theory, geometric-graph-theory, graph-coloring, hadwiger-nelson
MSC: 05C15, 52C10
-/

/-!
# Kernel-checked Hadwiger--Nelson bounds

This library proves the currently known bounds `5 ≤ χ(ℝ²) ≤ 7` for the
unit-distance graph of the Euclidean plane.  The upper bound is an explicit
Isbell-style coloring.  The lower bound checks Parts' 481-vertex certificate,
embeds a finite doubled triangular-lattice gadget, and closes the final
spindle.

The exact chromatic number remains open: this does not decide whether it is
five, six, or seven, and therefore does not solve Erdős Problem 508.
-/
