/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.NSMFullClassification
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TorsionOrderExact
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralBNGeneral
import LeanPool.BrillNoetherGraphs.Bananas.Classification.CorrectedBananaTorsion

/-!
# The Section 6 large-period banana obstruction

The corrected Proposition 4.19 torsion dichotomy combines here with the
Section 6 Brill--Noether obstruction: a `k`-general transmission marking on a
high-genus banana cannot have `k ≥ g`, since Proposition 6.1 would make the
underlying banana Brill--Noether general.
-/

namespace Bananas

open Utilities

/-- Theorem 3.9 reduces every high-genus banana marking with general
transmission to one of its corrected endpoint-aware exceptional families. -/
theorem kGeneralTransmission_implies_nsmForBananaException
    {g k : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hK : KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k) :
    NSMForBananaException B (strandVertex B α i) (strandVertex B β j) := by
  rcases nsmForBanana_classification hg B α β i j with hException | hNeg
  · exact hException
  · exact False.elim
      (not_kGeneralTransmission_of_negative_rankDelta
        (mark B.graph (strandVertex B α i) (strandVertex B β j)) k hNeg hK)

/-- The Proposition 6.1 branch in Corollary 6.4 (`cor:bananasWithKGT`).

For a banana of genus at least three, any general-transmission period at
least the genus contradicts the degree-two endpoint pencil.  Thus the
unformalized Proposition 4.19 dichotomy only needs to rule out its remaining
order-two exceptional alternatives. -/
theorem banana_not_kGeneralTransmission_of_genus_le_period
    {g k : ℕ} (hg : 3 ≤ g) (B : Banana g) (u v : B.graph.V)
    (hkg : g ≤ k) :
    ¬ KGeneralTransmission (mark B.graph u v) k := by
  intro hK
  have hThreshold : g + 2 ≤ 2 * k := by
    nlinarith
  have hGenus : genus (mark B.graph u v).graph = g := by
    change genus B.graph = g
    rw [B.genus_graph]
    omega
  have hBN : BrillNoetherGeneral B.graph :=
    kGeneralTransmission_brillNoetherGeneral
      (banana_graph_connected B) hGenus hK hThreshold
  exact banana_not_brillNoetherGeneral hg B hBN

/-- The corrected Section 4 input required by Corollary 6.4.  This is
Proposition 4.19 with its published two-length-two exception replaced by the
larger `CorrectedMidpointException` family. -/
def CorrectedBananaTorsionDichotomy {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β) : Prop :=
  ∀ k : ℕ,
    IsTorsionOrder
        (mark B.graph (strandVertex B α i) (strandVertex B β j)) k →
    AllSubmodular
        (mark B.graph (strandVertex B α i) (strandVertex B β j)) →
      (CorrectedMidpointException B α β i j ∧ k = 2) ∨ g ≤ k

/-- Corrected Corollary 6.4, parameterized by its Proposition 4.19 input.
The following theorem supplies that input unconditionally. -/
theorem corrected_banana_kGeneral_iff_of_torsionDichotomy
    {g k : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hDichotomy : CorrectedBananaTorsionDichotomy B α β i j) :
    KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k ↔
      CorrectedMidpointException B α β i j ∧ k = 2 := by
  let u := strandVertex B α i
  let v := strandVertex B β j
  constructor
  · intro hK
    have huv : u ≠ v := by
      intro huvEq
      have hK' : KGeneralTransmission (mark B.graph u u) k := by
        simpa [u, v, huvEq] using hK
      have hNeg : ∃ D : CFDiv B.graph,
          rankDelta (mark B.graph u u) D < 0 :=
        ⟨oneChip u, rankDelta_one_chip_self_lt_zero (by omega) B u⟩
      exact (not_kGeneralTransmission_of_negative_rankDelta
        (mark B.graph u u) k hNeg) hK'
    have hTO : IsTorsionOrder (mark B.graph u v) k :=
      banana_kGeneral_isTorsionOrder B u v huv
        (by rw [B.genus_graph]; omega) hK
    rcases hDichotomy k (by simpa [u, v] using hTO)
      (by simpa [u, v] using hK.2.1) with hExceptional | hLarge
    · exact hExceptional
    · exact False.elim
        (banana_not_kGeneralTransmission_of_genus_le_period hg B u v hLarge hK)
  · rintro ⟨hExceptional, rfl⟩
    exact correctedMidpointException_twoGeneralTransmission hg B α β i j
      hExceptional

/-- Corrected Corollary 6.4: a high-genus banana has `k`-general transmission
exactly for the distinct-strand midpoint family with at least one length-two
strand, and then exactly at period two. -/
theorem corrected_banana_kGeneral_iff
    {g k : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β) :
    KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k ↔
      CorrectedMidpointException B α β i j ∧ k = 2 := by
  apply corrected_banana_kGeneral_iff_of_torsionDichotomy hg B α β i j
  intro period hTO hSub
  exact corrected_banana_torsion_dichotomy hg B α β i j hTO hSub

end Bananas
