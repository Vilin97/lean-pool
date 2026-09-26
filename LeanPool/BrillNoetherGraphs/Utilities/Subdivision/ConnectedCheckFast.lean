/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ContractionForestCensusGeneral
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity

/-!
# A union-find connectivity check for ordered cores

`ExplicitPotential.Core.connectedCheck`
(`Utilities/Subdivision/SubdivisionConnectivity.lean`) decides
`ExplicitPotential.Core.Connected` by enumerating **all `2ⁿ` vertex subsets**
and looking for a crossing slot in each.  That is the definition read
literally, and it is exact, but it makes every kernel-checked connectivity fact
cost exponentially in the number of core vertices.

This file gives the same information for the price of a union--find fold.  The
partition machinery is already present: `compFold core F` is the canonical
representative map obtained by contracting the slots of `F`, and
`compFold_iff` says `compFold`-equality *is* reachability
(`Utilities/Subdivision/ContractionForestCensusGeneral.lean`).  Taking
`F = Finset.univ`, a core is connected exactly when that map is constant.

## Measured

At `n = 8`, `p = 12` (the genus-five atlas), on the sixteen
Atanasov--Ranganathan rows, `by decide +kernel`:

| check | per core |
|---|---|
| `connectedCheck` (`2⁸ = 256` subsets × `8² + 12` tests) | **0.54 s** |
| `connectedCheckFast` (one fold, `8²` comparisons) | **0.01 s** |

a factor of about fifty, measured back-to-back in one batch and reproduced.
The genus-five library performed twenty-nine such checks, so this is
about fifteen seconds of kernel time, ten of it on the critical path
(`GenusFiveCoreAtlas` → `GenusFiveCubicAtlas`).  The saving grows with `n`:
genus six classifies sixty-six cores at `n = 10`, where the old checker
enumerates `1024` subsets.

## What is proved

`connectedCheckFast_eq_true_iff` is a genuine `iff`, so this is a drop-in
replacement for `connectedCheck_eq_true_iff` and not merely a sufficient
condition.  The forward direction is the one every call site uses; the
converse is here so that a reader does not have to wonder whether the cheap
check is also complete.  Neither checker is removed: `connectedCheck` remains
the literal reading of the definition and stays available as an independent
cross-check.
-/

@[expose] public section

namespace Utilities.Certificate

open Utilities.Certificate.ContractionForestCensusGeneral

namespace ExplicitPotential.Core

variable {n p : ℕ}

/-- Membership in a vertex cut is constant along reachability through `F`,
provided no slot of `F` crosses the cut.  This is the only graph-theoretic
content of the checker: a reach path that leaves `S` must cross it. -/
theorem mem_iff_of_reachIn {core : ExplicitPotential.Core n p}
    {F : Finset (Fin p)} {S : Finset (Fin n)}
    (hNoCrossing : ∀ e ∈ F, (core.tail e ∈ S ↔ core.head e ∈ S))
    {x y : Fin n} (hReach : ReachIn core F x y) : x ∈ S ↔ y ∈ S := by
  induction hReach with
  | refl => exact Iff.rfl
  | @tail b c _ hbc ih =>
      refine ih.trans ?_
      obtain ⟨e, heList, hEnds⟩ := hbc
      have hMem : e ∈ F := (mem_edgeList F e).mp heList
      have hIff := hNoCrossing e hMem
      rcases hEnds with ⟨hTail, hHead⟩ | ⟨hHead, hTail⟩
      · rw [← hTail, ← hHead]; exact hIff
      · rw [← hTail, ← hHead]; exact hIff.symm

/-- **The union--find connectivity checker.**  A core is connected exactly
when contracting every slot leaves one class. -/
def connectedCheckFast (core : ExplicitPotential.Core n p) : Bool :=
  decide (∀ v w : Fin n,
    compFold core Finset.univ v = compFold core Finset.univ w)

/-- The direction every call site uses. -/
theorem connected_of_connectedCheckFast {core : ExplicitPotential.Core n p}
    (hCheck : core.connectedCheckFast = true) : core.Connected := by
  have hConst : ∀ v w : Fin n,
      compFold core Finset.univ v = compFold core Finset.univ w :=
    of_decide_eq_true hCheck
  intro S hSplit
  obtain ⟨v, w, hv, hw⟩ := hSplit
  by_contra hNoCrossingSlot
  have hNoCrossing : ∀ e ∈ (Finset.univ : Finset (Fin p)),
      (core.tail e ∈ S ↔ core.head e ∈ S) := by
    intro e _
    by_cases hTail : core.tail e ∈ S <;> by_cases hHead : core.head e ∈ S
    · simp [hTail, hHead]
    · exact absurd ⟨e, Or.inl ⟨hTail, hHead⟩⟩ hNoCrossingSlot
    · exact absurd ⟨e, Or.inr ⟨hHead, hTail⟩⟩ hNoCrossingSlot
    · simp [hTail, hHead]
  exact hw ((mem_iff_of_reachIn hNoCrossing
    ((compFold_iff core Finset.univ v w).mp (hConst v w))).mp hv)

/-- The cheap checker is exact, not merely sufficient. -/
@[simp] theorem connectedCheckFast_eq_true_iff
    (core : ExplicitPotential.Core n p) :
    core.connectedCheckFast = true ↔ core.Connected := by
  refine ⟨connected_of_connectedCheckFast, fun hConnected => ?_⟩
  simp only [connectedCheckFast, decide_eq_true_eq]
  intro v w
  by_contra hNe
  classical
  set S : Finset (Fin n) :=
    Finset.univ.filter
      (fun x => compFold core Finset.univ x = compFold core Finset.univ v)
    with hS
  obtain ⟨e, hCross⟩ := hConnected S ⟨v, w, by simp [hS], by simp [hS, Ne.symm hNe]⟩
  have hEdge : compFold core Finset.univ (core.tail e)
      = compFold core Finset.univ (core.head e) :=
    compFold_tail_eq_head_of_mem core (Finset.mem_univ e)
  rcases hCross with ⟨hIn, hOut⟩ | ⟨hIn, hOut⟩ <;>
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hIn hOut
  · exact hOut (hEdge ▸ hIn)
  · exact hOut (hEdge.symm ▸ hIn)

end ExplicitPotential.Core

end Utilities.Certificate
