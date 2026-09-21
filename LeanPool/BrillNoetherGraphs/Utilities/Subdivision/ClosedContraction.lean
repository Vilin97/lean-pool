/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedFaceCensus

/-!
# A closed-orthant row proof implies every contraction of its row

the corresponding closed-row proof module moves a `(domain closed)` row proof down to the
*same* core's open-orthant obligation, by observing that a strictly positive
length vector has empty vanishing set.  This file makes the other, larger
move: the closed orthant of a core `C` also contains, as a **face**, the whole
closed orthant of every equal-genus contraction `C / F`.

Concretely, let `F` be a slot set of `C` which is a forest and whose
contraction leaves no loop, and let `C'` be the contracted core.  Send a
length vector `ℓ'` of `C'` to the length vector of `C` that is `ℓ'` on the
surviving slots and `0` on `F`.  Its vanishing set is exactly `F`, so a closed
row proof of `C` applies there, and
`Utilities.Certificate.DegenerateSpec.DegSpec.Contraction.laplacianEquiv` identifies the resulting
degenerate graph with the honest subdivision of `C'`.

So one closed-orthant row proof discharges the open-orthant obligation of its
core *and of every core below it in the contraction order*.

## What the data has to supply, and why orientation is a real constraint

`DegenerateSpec.Contraction` matches slots **with their orientation**: it asks
for `vtx (C'.tail e') = rep (C.tail (slot e'))`, not for the unordered pair.
Slot reversal is deliberately not part of that structure — it is supplied
separately by `SubdivisionGraph.Spec.Relabeling`.  `ContractionData` below
inherits that restriction, so it witnesses only orientation-exact
contractions.  A contraction that needs a slot flipped has to be composed with
a `Relabeling`; that composition is not built here.

## Where this does *not* reach

Contracting a slot of a **split loop** (a bivalent marker `w` carrying two
parallel slots to its base `v`) is never admissible: contracting one of the
pair identifies `v` with `w`, so the other becomes a loop and `IsLoopy` holds;
contracting both is not a forest.  The number of split loops is therefore
constant along every face reachable this way, and a loop-carrying row is never
a face of a loopless one.  See the corresponding closed-row proof module.
-/

namespace Utilities.Certificate.ClosedContraction

open Utilities

open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.ClosedFaceCensus

variable {n p n' p' : ℕ}

/-- A core is its two endpoint maps.  Used by the `RowNNNFromRowMMM` files to
check, rather than assume, that the core they write out by hand is the one the
catalog names. -/
theorem core_ext {m q : ℕ} {a b : ExplicitPotential.Core m q}
    (ht : a.tail = b.tail) (hh : a.head = b.head) : a = b := by
  cases a; cases b; cases ht; cases hh; rfl

/-- Data exhibiting `core'` as the contraction of `core` along the slot set
`F`, orientation included.  Every field is decidable on concrete cores, so an
instance is built by `decide`. -/
structure ContractionData (core : ExplicitPotential.Core n p)
    (core' : ExplicitPotential.Core n' p') where
  /-- The contracted slot set. -/
  F : Finset (Fin p)
  /-- Which vertex of `core` represents each vertex of `core'`. -/
  vtx : Fin n' → Fin n
  /-- Which slot of `core` each slot of `core'` is. -/
  slot : Fin p' → Fin p
  /-- Contracting `F` preserves the genus. -/
  isForest : IsForest core F
  /-- Contracting `F` leaves no loop. -/
  notLoopy : ¬ IsLoopy core F
  slot_inj : Function.Injective slot
  slot_notMem : ∀ e' : Fin p', slot e' ∉ F
  slot_surj : ∀ e : Fin p, e ∉ F → ∃ e' : Fin p', slot e' = e
  vtx_inj : Function.Injective vtx
  vtx_rep : ∀ v' : Fin n', compFold core F (vtx v') = vtx v'
  vtx_surj : ∀ v : Fin n, ∃ v' : Fin n', vtx v' = compFold core F v
  tail_eq : ∀ e' : Fin p',
    vtx (core'.tail e') = compFold core F (core.tail (slot e'))
  head_eq : ∀ e' : Fin p',
    vtx (core'.head e') = compFold core F (core.head (slot e'))

namespace ContractionData

variable {core : ExplicitPotential.Core n p} {core' : ExplicitPotential.Core n' p'}
  (c : ContractionData core core') (s : SubdivisionGraph.Spec n' p')

/-- The length vector of `core` which is `s.length` on the surviving slots and
`0` on `F`. -/
def lift (e : Fin p) : ℕ := ∑ e' : Fin p', if c.slot e' = e then s.length e' else 0

theorem lift_slot (e' : Fin p') : c.lift s (c.slot e') = s.length e' := by
  classical
  unfold lift
  rw [Finset.sum_eq_single e']
  · simp
  · intro b _ hb
    have : c.slot b ≠ c.slot e' := fun h => hb (c.slot_inj h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ e') h

theorem lift_of_mem {e : Fin p} (he : e ∈ c.F) : c.lift s e = 0 := by
  classical
  unfold lift
  refine Finset.sum_eq_zero ?_
  intro e' _
  have : c.slot e' ≠ e := fun h => c.slot_notMem e' (h ▸ he)
  simp [this]

theorem zeroSet_lift : zeroSet (c.lift s) = c.F := by
  classical
  ext e
  simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hF
    obtain ⟨e', rfl⟩ := c.slot_surj e hF
    rw [c.lift_slot s e'] at h
    exact (s.length_pos e').ne' h
  · exact fun h => c.lift_of_mem s h

theorem isForest_lift : IsForest core (zeroSet (c.lift s)) := by
  rw [c.zeroSet_lift s]; exact c.isForest

theorem notLoopy_lift : ¬ IsLoopy core (zeroSet (c.lift s)) := by
  rw [c.zeroSet_lift s]; exact c.notLoopy

theorem rep_censusSpec (hn : 0 < n) :
    (censusSpec core hn (c.lift s) (c.isForest_lift s) (c.notLoopy_lift s)).rep
      = compFold core c.F := by
  show compFold core (zeroSet (c.lift s)) = compFold core c.F
  rw [c.zeroSet_lift s]

/-- The face `{ℓ = 0 on F}` of the closed orthant of `core`, matched with the
honest subdivision of the contracted core `core'`. -/
def contraction (hn : 0 < n) (hcore : s.core = core') :
    Utilities.Certificate.DegenerateSpec.DegSpec.Contraction
      (censusSpec core hn (c.lift s) (c.isForest_lift s) (c.notLoopy_lift s)) s where
  vtx := c.vtx
  vtx_rep := fun v' => by rw [c.rep_censusSpec s hn]; exact c.vtx_rep v'
  vtx_inj := c.vtx_inj
  vtx_surj := fun v => by rw [c.rep_censusSpec s hn]; exact c.vtx_surj v
  slot := c.slot
  slot_inj := c.slot_inj
  slot_surj := fun e he => by
    refine c.slot_surj e ?_
    intro hF
    have he' : 0 < c.lift s e := he
    have := c.lift_of_mem s hF
    omega
  length_eq := fun e' => (c.lift_slot s e').symm
  tail_eq := fun e' => by
    rw [c.rep_censusSpec s hn, hcore]; exact c.tail_eq e'
  head_eq := fun e' => by
    rw [c.rep_censusSpec s hn, hcore]; exact c.head_eq e'

end ContractionData

/-- **The contraction bridge.**  A closed-orthant row proof for `core`
discharges the open-orthant row obligation of every orientation-exact
equal-genus contraction `core'` of `core`. -/
theorem bnExists_spec_of_closed_contraction
    (core : ExplicitPotential.Core n p) (hn : 0 < n) (degree : ℤ)
    (hclosed : ∀ (ℓ : Fin p → ℕ) (hForest : IsForest core (zeroSet ℓ))
      (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)),
        BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree)
    {core' : ExplicitPotential.Core n' p'} (c : ContractionData core core')
    (s : SubdivisionGraph.Spec n' p') (hcore : s.core = core') :
    BNExists s.graph 1 degree :=
  ((c.contraction s hn hcore).laplacianEquiv.bnExists_iff 1 degree).mpr
    (hclosed (c.lift s) (c.isForest_lift s) (c.notLoopy_lift s))

end Utilities.Certificate.ClosedContraction
