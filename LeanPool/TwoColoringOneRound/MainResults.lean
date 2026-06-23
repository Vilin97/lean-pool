/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.Definitions
import LeanPool.TwoColoringOneRound.Reduction

/-!
# Distributed2Coloring: Main results

This file collects the public-facing theorems connecting:
- the certified finite lower bound at `n = 1_000_000`, and
- one-round `ClassicalAlgorithm`s on the directed cycle.

We also package these bounds as statements about an infimum `p⋆` over all measurable local rules.
-/

namespace Distributed2Coloring

open scoped unitInterval

namespace ClassicalAlgorithm

/--
The optimal monochromatic-edge probability over all one-round `ClassicalAlgorithm`s.

This corresponds to the quantity `p⋆ := inf_f p(f)` in `theory/report/manuscript.tex`, where the
infimum ranges over all measurable local rules.
-/
noncomputable def pStar : ENNReal :=
  sInf (Set.range ClassicalAlgorithm.p)

/--
If `c` is a lower bound for `ClassicalAlgorithm.p` for *every* algorithm, then `c ≤ pStar`.
-/
theorem le_pStar_of_forall_le {c : ENNReal} (hc : ∀ alg : ClassicalAlgorithm, c ≤ alg.p) :
    c ≤ ClassicalAlgorithm.pStar := by
  -- `c ≤ sInf (range p)` since `c` is a lower bound for every element of the range.
  refine le_sInf ?_
  rintro _ ⟨alg, rfl⟩
  exact hc alg

/--
If there exists an algorithm achieving `p ≤ c`, then `pStar ≤ c`.

In particular, any explicit construction gives an upper bound on `pStar`.
-/
theorem pStar_le_of_exists_le {c : ENNReal} (hc : ∃ alg : ClassicalAlgorithm, alg.p ≤ c) :
    ClassicalAlgorithm.pStar ≤ c := by
  rcases hc with ⟨alg, halg⟩
  exact (sInf_le (Set.mem_range_self alg)).trans halg

end ClassicalAlgorithm

/-!
## Numerical bounds (as in the manuscript)

The bridge step is `Distributed2Coloring.p_ge_23879` from `Distributed2Coloring/Reduction.lean`.
-/

/-- Every one-round algorithm has monochromatic-edge probability at least `0.23879`. -/
theorem pStar_ge_23879 :
    ENNReal.ofReal (23879 / 100000 : ℝ) ≤ ClassicalAlgorithm.pStar :=
  ClassicalAlgorithm.le_pStar_of_forall_le (fun alg => Distributed2Coloring.p_ge_23879 alg)

/-- An explicit one-round algorithm achieves monochromatic-edge probability at most `0.24118`. -/
theorem pStar_le_24118 :
    ClassicalAlgorithm.pStar ≤ ENNReal.ofReal (24118 / 100000 : ℝ) :=
  ClassicalAlgorithm.pStar_le_of_exists_le Distributed2Coloring.exists_algorithm_p_le_24118

theorem pStar_lt_24118 :
    ClassicalAlgorithm.pStar < ENNReal.ofReal (24118 / 100000 : ℝ) := by
  rcases UpperBound.Recursive3Param.exists_algorithm_p_lt with ⟨alg, hlt⟩
  exact lt_of_le_of_lt (sInf_le (Set.mem_range_self alg)) hlt

end Distributed2Coloring
