/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

import LeanPool.MooreBound.DegreeDiameter.PrimeIntervals
import LeanPool.MooreBound.DegreeDiameter.Construction
import LeanPool.MooreBound.DegreeDiameter.Theorem11FromProposition31
import LeanPool.MooreBound.DegreeDiameter.Corollary12FromProposition31

/-!
# Main results

The main exports use the concrete Proposition 3.1 family and its equation-(9)
limits. An independent big-cell proof is available under names ending in
`_via_big_cell`.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

namespace MooreBound

open Filter

namespace DegreeDiameter

/-- **Theorem 1.1.**  For every fixed positive `k`, the maximum order of a
finite simple graph of maximum degree at most `d` and extended diameter at
most `k`, divided by `d^k`, tends to one as `d` tends to infinity. -/
theorem theorem_1_1 {k : ℕ} (hk : 0 < k) :
    Tendsto (fun d : ℕ ↦ (nKD k d : ℝ) / (d : ℝ) ^ k) atTop (nhds 1) :=
  theorem_1_1_from_proposition_3_1 hk

/-- An independent proof of Theorem 1.1 through the big-cell lower bound. -/
theorem theorem_1_1_via_big_cell {k : ℕ} (hk : 0 < k) :
    Tendsto (fun d : ℕ ↦ (nKD k d : ℝ) / (d : ℝ) ^ k) atTop (nhds 1) :=
  theorem_1_1_of_asymptoticHalvedWitness asymptoticHalvedWitnessHypothesis hk

/-- **Corollary 1.2.**  For every fixed `ell ≥ 2`, the lower limit of the
edge extremum (with line-graph extended diameter at most `ell`), normalized
by `d^ell`, is at least one. -/
theorem corollary_1_2 {ell : ℕ} (hell : 2 ≤ ell) :
    1 ≤ liminf (fun d : ℕ ↦ (h ell d : ℝ) / (d : ℝ) ^ ell) atTop :=
  corollary_1_2_from_proposition_3_1 hell

/-- An independent proof of Corollary 1.2 through the big-cell lower bound. -/
theorem corollary_1_2_via_big_cell {ell : ℕ} (hell : 2 ≤ ell) :
    1 ≤ liminf (fun d : ℕ ↦ (h ell d : ℝ) / (d : ℝ) ^ ell) atTop :=
  corollary_1_2_of_asymptoticHalvedWitness asymptoticHalvedWitnessHypothesis hell

end DegreeDiameter

end MooreBound
