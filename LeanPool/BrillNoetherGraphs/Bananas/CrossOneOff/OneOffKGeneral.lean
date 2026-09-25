/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.OneOffInversionLowerBound

/-!
# One-off general-transmission obstruction

This packages the corrected immediate inversion estimate following Lemma 4.23
with the defining inversion upper bound for `KGeneralTransmission`.  The
arithmetic hypothesis is deliberately explicit: it is exactly the condition
under which the paper's one-off row block is large enough to obstruct
generality.
-/

namespace Bananas

open Utilities

/-- The one-off marking cannot have `k`-general transmission once the
explicit inversion block from Lemma 4.24 is larger than the genus. -/
theorem oneOff_not_kGeneral_of_inversion_bound_gt_genus
    {g k : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (hg : 2 ≤ g) (hLength : 1 < B.length alpha)
    (hLarge : g < Nat.choose
      ((B.length alpha - 2) * (g / (B.length alpha - 1))) 2) :
    ¬ KGeneralTransmission
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k := by
  intro hK
  obtain ⟨tau, hTau, hAffine, hFinite, hUpper⟩ :=
    hK.2.2 (g • oneChip (rightEndpoint B))
  have hk : 0 < k := hK.1.1
  have hLower := oneOff_inversion_lower_bound
    B alpha tau hg hk hLength hTau hAffine hFinite
  have hGenus : Int.toNat (genus
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)).graph) = g := by
    change Int.toNat (genus B.graph) = g
    rw [B.genus_graph]
    omega
  rw [hGenus] at hUpper
  exact (not_lt_of_ge (hLower.trans hUpper)) hLarge

end Bananas
