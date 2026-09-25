/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedContraction
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionIso

/-!
# Contraction up to slot reversal

`RowProof.ClosedContraction` derives a contracted row's open-orthant
obligation from a closed-orthant proof of the core it contracts from.  Its
`ContractionData` matches slots **with orientation**: `tail_eq` and `head_eq`
demand that the contracted slot's tail is the tail, not the head.

That is the binding constraint in practice.  Of the 94 non-trivalent
genus-four rows, only 27 admit an orientation-exact contraction from a proved
trivalent row; rows 010, 011, 031, 035 and 070 all sit under the proved row
099 yet need slots flipped.  Reversing a slot does not change the subdivided
graph at all — the path is the same, walked the other way — so this is pure
bookkeeping, and this file removes it.

The route is the one `Certificate/SubdivisionIso.lean` already supports:
reorient the target spec, contract there, and transport back along the
identity relabeling whose `reversed` field records the flips.
-/

@[expose] public section

namespace Utilities.Certificate.ReorientContraction

open Utilities

open Utilities.Certificate
open Utilities.Certificate.ClosedFaceCensus
open Utilities.Certificate.ClosedContraction
open Utilities.Certificate.ContractionForestCensusGeneral

variable {n p n' p' : ℕ}

/-- Reverse a chosen set of slots of a core. -/
def Core.reorient (core : ExplicitPotential.Core n p) (rev : Fin p → Bool) :
    ExplicitPotential.Core n p where
  tail := fun e => if rev e then core.head e else core.tail e
  head := fun e => if rev e then core.tail e else core.head e

@[simp] theorem Core.reorient_tail (core : ExplicitPotential.Core n p)
    (rev : Fin p → Bool) (e : Fin p) :
    (Core.reorient core rev).tail e =
      if rev e then core.head e else core.tail e := rfl

@[simp] theorem Core.reorient_head (core : ExplicitPotential.Core n p)
    (rev : Fin p → Bool) (e : Fin p) :
    (Core.reorient core rev).head e =
      if rev e then core.tail e else core.head e := rfl

/-- Reversing slots preserves looplessness. -/
theorem Core.reorient_loopless {core : ExplicitPotential.Core n p}
    {rev : Fin p → Bool} (h : ∀ e : Fin p, core.tail e ≠ core.head e)
    (e : Fin p) :
    (Core.reorient core rev).tail e ≠ (Core.reorient core rev).head e := by
  simp only [Core.reorient_tail, Core.reorient_head]
  by_cases hr : rev e
  · simp only [hr, if_pos]
    exact fun hEq => h e hEq.symm
  · simp only [hr, if_neg, Bool.false_eq_true, not_false_eq_true]
    exact h e

/-- The same subdivision, with a chosen set of slots read backwards. -/
def reorientSpec (s : SubdivisionGraph.Spec n p)
    (rev : Fin p → Bool) : SubdivisionGraph.Spec n p where
  core := Core.reorient s.core rev
  length := s.length
  core_nonempty := s.core_nonempty
  core_loopless := Core.reorient_loopless s.core_loopless
  length_pos := s.length_pos

/-- Reorientation is an identity relabeling: same vertices, same slots, same
lengths, with `reversed` recording which slots were flipped. -/
def reorientRelabeling (s : SubdivisionGraph.Spec n p) (rev : Fin p → Bool) :
    s.Relabeling (reorientSpec s rev) where
  coreEquiv := Equiv.refl _
  slotEquiv := Equiv.refl _
  reversed := rev
  length_eq := fun _ => rfl
  tail_eq := fun e => by
    simp only [reorientSpec, Equiv.refl_apply, Core.reorient_tail]
  head_eq := fun e => by
    simp only [reorientSpec, Equiv.refl_apply, Core.reorient_head]

/-- **Contraction up to slot reversal.**

A closed-orthant row proof for `core` yields the open-orthant obligation for
any `core'` that contracts from it *after reorienting some slots of `core'`*.
This is what takes the census reduction from the 27 orientation-exact rows to
all 94. -/
theorem bnExists_spec_of_closed_contraction_reorient
    (core : ExplicitPotential.Core n p) (hn : 0 < n) (degree : ℤ)
    (hclosed : ∀ (ℓ : Fin p → ℕ) (hForest : IsForest core (zeroSet ℓ))
      (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)),
        BNExists (censusSpec core hn ℓ hForest hNotLoopy).graph 1 degree)
    {core' : ExplicitPotential.Core n' p'} (rev : Fin p' → Bool)
    (c : ContractionData core (Core.reorient core' rev))
    (s : SubdivisionGraph.Spec n' p') (hcore : s.core = core') :
    BNExists s.graph 1 degree := by
  -- Contract on the reoriented spec, where the orientations do match.
  have hreor : (reorientSpec s rev).core = Core.reorient core' rev := by
    simp only [reorientSpec, hcore]
  have hbig : BNExists (reorientSpec s rev).graph 1 degree :=
    bnExists_spec_of_closed_contraction core hn degree hclosed c
      (reorientSpec s rev) hreor
  -- Reversing slots does not change the graph up to Laplacian equivalence.
  exact ((SubdivisionGraph.Spec.laplacianEquiv s (reorientSpec s rev)
    (reorientRelabeling s rev)).bnExists_iff 1 degree).mpr hbig

end Utilities.Certificate.ReorientContraction
