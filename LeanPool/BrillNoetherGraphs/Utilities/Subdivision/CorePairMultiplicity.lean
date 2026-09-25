/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CubicCore
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
public import Mathlib.Tactic

/-!
# Unordered pair multiplicities of an ordered core (light half)

`Core.pairMultiplicity` and the elementary symmetry, diagonal, row-sum, and
positivity facts about it that
the pseudocore marker layer consumes.  Rehomed from
`CoreOccurrenceMatching.lean` and `CubicMatrixReplay.lean` (which import this
file) so that consumers of these three declarations do not pull in the
occurrence-relabeling and replay machinery.
-/

@[expose] public section

namespace Utilities.Certificate

namespace ExplicitPotential.Core

variable {n p : ℕ}

/-- The number of ordered edge slots of `core` whose two endpoints are
exactly the unordered vertex pair `{i, j}`.  Both orientations are counted,
so the value is symmetric in `i` and `j`. -/
def pairMultiplicity (core : Core n p) (i j : Fin n) : ℕ :=
  (Finset.univ.filter fun edge : Fin p =>
      (core.tail edge = i ∧ core.head edge = j) ∨
        (core.tail edge = j ∧ core.head edge = i)).card

/-- Unordered multiplicity does not see the order of its two arguments. -/
theorem pairMultiplicity_comm (core : Core n p) (i j : Fin n) :
    core.pairMultiplicity i j = core.pairMultiplicity j i := by
  have hFilter :
      (Finset.univ.filter fun edge : Fin p =>
          (core.tail edge = i ∧ core.head edge = j) ∨
            (core.tail edge = j ∧ core.head edge = i))
        = Finset.univ.filter fun edge : Fin p =>
            (core.tail edge = j ∧ core.head edge = i) ∨
              (core.tail edge = i ∧ core.head edge = j) := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact or_comm
  rw [pairMultiplicity, hFilter]
  rfl

/-- A loopless core has zero diagonal in its multiplicity table. -/
theorem pairMultiplicity_self_eq_zero (core : Core n p)
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (i : Fin n) : core.pairMultiplicity i i = 0 := by
  rw [pairMultiplicity, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro edge _
  rintro (⟨hTail, hHead⟩ | ⟨hTail, hHead⟩) <;>
    exact hLoopless edge (hTail.trans hHead.symm)

end ExplicitPotential.Core

namespace CubicMatrixReplay

open ExplicitPotential

/-- On a loopless core the multiplicity row sums are exactly the occurrence
incidence degrees.  Looplessness is what makes the two endpoint conditions
mutually exclusive. -/
theorem sum_pairMultiplicity_eq_incidenceDegree {n p : ℕ} (core : Core n p)
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (i : Fin n) :
    ∑ j : Fin n, core.pairMultiplicity i j = core.incidenceDegree i := by
  classical
  have hCard : ∀ j : Fin n, core.pairMultiplicity i j
      = ∑ edge : Fin p, (if (core.tail edge = i ∧ core.head edge = j) ∨
          (core.tail edge = j ∧ core.head edge = i) then 1 else 0) := by
    intro j
    rw [Core.pairMultiplicity, Finset.card_filter]
  have hDegree : core.incidenceDegree i
      = ∑ edge : Fin p, ((if core.tail edge = i then 1 else 0) +
          (if core.head edge = i then 1 else 0)) := rfl
  simp only [hCard]
  rw [Finset.sum_comm, hDegree]
  refine Finset.sum_congr rfl fun edge _ => ?_
  by_cases hTail : core.tail edge = i
  · have hHead : ¬ core.head edge = i := fun hEq =>
      hLoopless edge (hTail.trans hEq.symm)
    simp [hTail, hHead, Finset.sum_ite_eq]
  · by_cases hHead : core.head edge = i
    · simp [hTail, hHead, Finset.sum_ite_eq]
    · simp [hTail, hHead]

/-- Each edge slot contributes to the multiplicity of its own endpoint
pair. -/
theorem pairMultiplicity_endpoints_pos {n p : ℕ} (core : Core n p)
    (edge : Fin p) :
    0 < core.pairMultiplicity (core.tail edge) (core.head edge) := by
  rw [Core.pairMultiplicity]
  exact Finset.card_pos.mpr ⟨edge, by simp⟩

end CubicMatrixReplay

end Utilities.Certificate
