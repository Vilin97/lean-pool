/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ConnectedCheckFast
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionTwoEdgeCut

/-!
# A union-find two-edge-connectivity check for ordered cores

`ExplicitPotential.Core.twoEdgeConnectedCheck`
(`Utilities/Subdivision/SubdivisionTwoEdgeCut.lean:190`) decides
`ExplicitPotential.Core.TwoEdgeConnected` by enumerating **all `2ⁿ` vertex
subsets** and counting the slots that cross each one.  That is the definition
read literally, and it is exact, but it makes every kernel-checked
two-edge-connectivity fact cost exponentially in the number of core vertices.
It is the same shape `Utilities/Subdivision/ConnectedCheckFast.lean` was
written to replace for plain connectedness, and it was left behind there.

This file gives the same information for the price of `p + 1` union--find
folds.  The reading is the standard one: a core is two-edge connected exactly
when it is connected **and** deleting any single slot leaves it connected.
Deleting a slot needs no new datum, because `compFold core F` already takes an
arbitrary slot set: `compFold core (Finset.univ.erase e)` *is* the component
map of the core with slot `e` removed.

## Why the connectivity conjunct is not redundant

Dropping `connectedCheckFast` makes the checker wrong at `p = 0`: the
two-vertex edgeless core `Core 2 0` has `Finset.univ.erase e` vacuously
constant (there is no `e`), so the fold condition holds, while the core is not
even connected.  For `p ≥ 1` the fold condition alone does imply connectedness,
but the conjunction is the honest statement and costs one extra fold.

## Measured

At `n = 8`, `p = 12` (the genus-five atlas), on the sixteen
Atanasov--Ranganathan rows, `by decide +kernel`, measured back-to-back in one
batch and reproduced:

| check | sixteen cores |
|---|---|
| `twoEdgeConnectedCheck` (`2⁸ = 256` subsets × a `Fin 12` filter each) | **12.6 s** |
| `twoEdgeConnectedCheckFast` (`13` folds of `8²` comparisons) | **1.95 s** |

The saving grows with `n`: the old checker doubles per core vertex, the new one
grows linearly in `n · p`.

## What is proved

`twoEdgeConnectedCheckFast_eq_true_iff` is a genuine `iff`, so this is a
drop-in replacement for `twoEdgeConnectedCheck_eq_true_iff` and not merely a
sufficient condition.  The forward direction is the one every call site uses;
the converse is here so that a reader does not have to wonder whether the cheap
check is also complete.  Neither checker is removed: `twoEdgeConnectedCheck`
remains the literal reading of the definition and stays available as an
independent cross-check.
-/

namespace Utilities.Certificate

open Utilities.Certificate.ContractionForestCensusGeneral

namespace ExplicitPotential.Core

variable {n p : ℕ}

/-- The slot set that survives deleting `e`. -/
private abbrev without (e : Fin p) : Finset (Fin p) := Finset.univ.erase e

/-- A slot crosses `S` exactly when its two ends disagree about membership. -/
private theorem crosses_iff {core : ExplicitPotential.Core n p}
    {S : Finset (Fin n)} (e : Fin p) :
    ((core.tail e ∈ S ∧ core.head e ∉ S) ∨ (core.head e ∈ S ∧ core.tail e ∉ S))
      ↔ ¬ (core.tail e ∈ S ↔ core.head e ∈ S) := by
  by_cases hTail : core.tail e ∈ S <;> by_cases hHead : core.head e ∈ S <;>
    simp [hTail, hHead]

/-- **The union--find two-edge-connectivity checker.**  A core is two-edge
connected exactly when it is connected and every single-slot deletion still
leaves one class. -/
def twoEdgeConnectedCheckFast (core : ExplicitPotential.Core n p) : Bool :=
  core.connectedCheckFast &&
    decide (∀ e : Fin p, ∀ v w : Fin n,
      compFold core (without e) v = compFold core (without e) w)

/-- The direction every call site uses. -/
theorem twoEdgeConnected_of_twoEdgeConnectedCheckFast
    {core : ExplicitPotential.Core n p}
    (hCheck : core.twoEdgeConnectedCheckFast = true) : core.TwoEdgeConnected := by
  classical
  rw [twoEdgeConnectedCheckFast, Bool.and_eq_true, decide_eq_true_eq] at hCheck
  obtain ⟨hConnCheck, hFold⟩ := hCheck
  have hConnected : core.Connected := connected_of_connectedCheckFast hConnCheck
  intro S hNonempty hProper
  obtain ⟨v, hv⟩ := hNonempty
  obtain ⟨w, hw⟩ : ∃ w : Fin n, w ∉ S := by
    by_contra hAll
    push Not at hAll
    exact hProper (Finset.eq_univ_of_forall hAll)
  -- Connectedness supplies one crossing slot.
  obtain ⟨e₀, he₀⟩ := hConnected S ⟨v, w, hv, hw⟩
  -- Deleting it still joins `v` to `w`, so a *second*, different slot crosses.
  have hReach : ReachIn core (without e₀) v w :=
    (compFold_iff core (without e₀) v w).mp (hFold e₀ v w)
  obtain ⟨e₁, he₁mem, he₁cross⟩ :
      ∃ e₁ ∈ (Finset.univ.erase e₀ : Finset (Fin p)),
        ¬ (core.tail e₁ ∈ S ↔ core.head e₁ ∈ S) := by
    by_contra hNone
    push Not at hNone
    exact hw ((mem_iff_of_reachIn hNone hReach).mp hv)
  have hNe : e₀ ≠ e₁ := fun h => (Finset.mem_erase.mp he₁mem).1 h.symm
  -- Both slots sit in the crossing filter, and they are distinct.
  set T : Finset (Fin p) := (Finset.univ : Finset (Fin p)).filter fun edge =>
    (core.tail edge ∈ S ∧ core.head edge ∉ S) ∨
    (core.head edge ∈ S ∧ core.tail edge ∉ S) with hT
  have h0 : e₀ ∈ T := by simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]; exact he₀
  have h1 : e₁ ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (crosses_iff e₁).mpr he₁cross
  calc (2 : ℕ) = ({e₀, e₁} : Finset (Fin p)).card := by
        rw [Finset.card_insert_of_notMem (by simpa using hNe), Finset.card_singleton]
    _ ≤ T.card := Finset.card_le_card (by
        intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ h0
        · exact (Finset.mem_singleton.mp h) ▸ h1)

/-- The cheap checker is exact, not merely sufficient. -/
@[simp] theorem twoEdgeConnectedCheckFast_eq_true_iff
    (core : ExplicitPotential.Core n p) :
    core.twoEdgeConnectedCheckFast = true ↔ core.TwoEdgeConnected := by
  classical
  refine ⟨twoEdgeConnected_of_twoEdgeConnectedCheckFast, fun hTwo => ?_⟩
  rw [twoEdgeConnectedCheckFast, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨(connectedCheckFast_eq_true_iff core).mpr
    (connected_of_twoEdgeConnected hTwo), ?_⟩
  intro e v w
  by_contra hNe
  -- The `compFold`-class of `v` after deleting `e` is a cut crossed only by `e`.
  set S : Finset (Fin n) :=
    Finset.univ.filter fun x => compFold core (without e) x = compFold core (without e) v
    with hS
  have hv : v ∈ S := by simp [hS]
  have hw : w ∉ S := by simp [hS]; exact fun h => hNe h.symm
  have hProper : S ≠ Finset.univ := fun hUniv => hw (hUniv ▸ Finset.mem_univ w)
  have hCard := hTwo S ⟨v, hv⟩ hProper
  -- No surviving slot crosses `S`, so the crossing filter is inside `{e}`.
  have hSub : ((Finset.univ : Finset (Fin p)).filter fun edge =>
      (core.tail edge ∈ S ∧ core.head edge ∉ S) ∨
      (core.head edge ∈ S ∧ core.tail edge ∉ S)) ⊆ {e} := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    rw [Finset.mem_singleton]
    by_contra hfe
    have hmem : f ∈ (Finset.univ.erase e : Finset (Fin p)) :=
      Finset.mem_erase.mpr ⟨hfe, Finset.mem_univ f⟩
    have hEnds := compFold_tail_eq_head_of_mem core hmem
    refine ((crosses_iff f).mp hf) ?_
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hEnds ▸ h, fun h => hEnds.symm ▸ h⟩
  have hLe : ((Finset.univ : Finset (Fin p)).filter fun edge =>
      (core.tail edge ∈ S ∧ core.head edge ∉ S) ∨
      (core.head edge ∈ S ∧ core.tail edge ∉ S)).card ≤ 1 := by
    simpa using Finset.card_le_card hSub
  omega

end ExplicitPotential.Core

end Utilities.Certificate
