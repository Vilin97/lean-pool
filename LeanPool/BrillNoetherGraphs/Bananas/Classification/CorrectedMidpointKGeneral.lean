/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralSwap
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.LengthTwoTorsion
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.LengthTwoCrossMonotonicity
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TorsionOrderTwoGeneral

/-!
# Corrected high-genus midpoint exceptions

The paper states the order-two exception in Proposition 4.19 and Corollary
6.4 with *both* supporting strands of length two.  The corrected
all-submodularity classification shows that this is too restrictive.  If one
mark is the midpoint of a length-two strand, it may be paired with any
interior point of a distinct strand.  When that second point is itself a
midpoint (so its strand merely has even length), both points double to the
endpoint pencil.  The marked graph therefore has exact torsion order two and
has `2`-general transmission.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- The corrected exceptional family in Proposition 4.19 and Corollary 6.4:
the marks lie at midpoints of distinct strands, and at least one of the two
strands has length two. -/
def CorrectedMidpointException {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β) : Prop :=
  α ≠ β ∧ 2 * i.val = B.length α ∧ 2 * j.val = B.length β ∧
    (B.length α = 2 ∨ B.length β = 2)

/-- Exact torsion order for the corrected exceptional family. -/
theorem correctedMidpointException_torsionOrder_two
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (h : CorrectedMidpointException B α β i j) :
    IsTorsionOrder
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) 2 := by
  exact distinct_strand_midpoints_torsionOrder_two B α β i j
    h.1 h.2.1 h.2.2.1

/-- Every divisor is submodular for the corrected exceptional family. -/
theorem correctedMidpointException_allSubmodular
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (h : CorrectedMidpointException B α β i j) :
    AllSubmodular
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) := by
  rcases h with ⟨hαβ, hiMid, hjMid, hαTwo | hβTwo⟩
  · have hiOne : i.val = 1 := by omega
    have hjInt : B.IsInteriorPosition β j := by
      change 0 < j.val ∧ j.val < B.length β
      have hlen := B.length_pos β
      omega
    exact NSMForBananaLengthTwoCrossException g B α β i j hg hαβ
      hαTwo hiOne hjInt
  · have hjOne : j.val = 1 := by omega
    have hiInt : B.IsInteriorPosition α i := by
      change 0 < i.val ∧ i.val < B.length α
      have hlen := B.length_pos α
      omega
    have hSwap := NSMForBananaLengthTwoCrossException g B β α j i hg
      hαβ.symm hβTwo hjOne hiInt
    exact (allSubmodular_swap_iff
      (strandVertex B α i) (strandVertex B β j)).mp hSwap

/-- Corrected positive half of Corollary 6.4: every exceptional midpoint
marking has `2`-general transmission. -/
theorem correctedMidpointException_twoGeneralTransmission
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (h : CorrectedMidpointException B α β i j) :
    KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) 2 := by
  exact torsionOrder_two_allSubmodular_isKGeneral
    (banana_graph_connected B)
    (correctedMidpointException_torsionOrder_two B α β i j h)
    (correctedMidpointException_allSubmodular hg B α β i j h)

end Bananas
