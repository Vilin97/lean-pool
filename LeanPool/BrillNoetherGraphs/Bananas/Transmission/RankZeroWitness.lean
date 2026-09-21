/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionBasics

/-!
# Negative rank differences at rank zero

This is the rank-theoretic part of Lemma 3.1(2) in the paper.  The paper
phrases it using supports of a chosen effective representative; the intrinsic
form below avoids choosing representatives and is exactly what the later
reduced-divisor calculation consumes.
-/

namespace Bananas

open Utilities

/-- At rank zero, a negative marked second difference says precisely that
each one-chip deletion remains winnable while the two-chip deletion is not.
This formulation is invariant under changing the divisor within its linear
equivalence class. -/
theorem rankDelta_neg_iff_rank_zero_deletions
    (M : TwiceMarked) (D : CFDiv M.graph) (hD : rank M.graph D = 0) :
    rankDelta M D < 0 ↔
      rank M.graph (D - one_chip M.u) = 0 ∧
      rank M.graph (D - one_chip M.v) = 0 ∧
      rank M.graph (D - one_chip M.u - one_chip M.v) = -1 := by
  rw [rankDelta_neg_iff_rank_pattern]
  constructor
  · rintro ⟨hU, hV, hUV⟩
    refine ⟨hD ▸ hU.symm, hD ▸ hV.symm, ?_⟩
    omega
  · rintro ⟨hU, hV, hUV⟩
    refine ⟨?_, ?_, ?_⟩
    · omega
    · omega
    · omega

end Bananas
