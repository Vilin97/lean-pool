/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffinePositionMultiBreak
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.StrongSeparator

/-!
# The multi-break interpolated script

`AffinePositionMultiBreak` names a passive multi-break slope script by a
list of affine-positioned breaks and computes its Laplacian exactly: the
endpoint sum at a core vertex, the jump of the break list at an interior
vertex, and in particular the *vanishing* of that jump away from every
named break. What it does **not** yet supply is the value *at* a named
break, or the small amount of vertex-by-vertex bookkeeping (`effective`,
`Reaches`) that every concrete instance of it would otherwise have to
restate. Both are entirely row-independent, so both are proved here once,
directly on top of `AffinePositionMultiBreak` (component 1).

* **Sorted break lists.** `SegmentReflection.value`/`slope` hard-code a
  three-piece step function (down, flat, up), and
  `GenusFourCore100.rampSlope`/`capSlope` hard-code two- and three-piece
  step functions via `min`/`max`. The multi-break format of component 1
  allows an arbitrary number of pieces, named by an arbitrary (unsorted)
  list; `BreakSorted` isolates the case that every script actually produces
  — start positions strictly increasing along the list — and
  `breakSlope_eq_of_breakSorted` gives, once, for any number of pieces, the
  same kind of closed form those files hard-code by hand: the value of a
  sorted break list at one of its own start positions is exactly that
  entry's slope. The supporting lemma `breakSlope_append_cons_eq` is more
  general still: it needs no global sortedness, only that nothing *after*
  the chosen entry in list order also starts at or before the query point.

* **March data.** `AffinePosition.SlopeScript.MarchData` bundles the closing
  balance condition of `AffinePosition.SlopeScript.Balanced` with sortedness
  on every slot — the affine-positioned analogue of
  `GenusFourCore100.RampData`, generalized from one window per slot to an
  arbitrary sorted sequence of them. `sortedBreaks_of_coordinate_lt` gives a
  convenient sufficient condition for sortedness (breaks listed in
  increasing coordinate order by script index), and
  `prin_firingScript_atBreak` computes the Laplacian of a march at one of
  its own named breaks in closed form, generalizing
  `GenusFourCore100.rampSlope_diff`/`capSlope_diff` to an arbitrary sorted
  sequence of breaks.

* **Effectiveness and reachability bookkeeping.** `effective_of_cases` and
  `reaches_of_script`, restated verbatim in every direct genus-four row
  (`GenusFourCore100.lean` etc.) for its own fixed `n, p`, are proved once
  here for an arbitrary `SubdivisionGraph.Spec n p`, so no row needs to
  restate them again.

Nothing here is row specific, and nothing here is decidable-by-`decide`: the
only Boolean checks anywhere in the stack are the fail-closed bound checks
already introduced by `AffinePosition`.
-/

@[expose] public section

namespace MarkedGraphs.Certificate
open Utilities.Certificate

open Utilities

open Finset
open ExplicitPotential
open SubdivisionGraph

/-! ## Generic effectiveness and reachability bookkeeping -/

end MarkedGraphs.Certificate

namespace Utilities.Certificate.SubdivisionGraph.Spec
open MarkedGraphs
open MarkedGraphs.Certificate

open Utilities.Certificate
open Utilities
open Finset
open ExplicitPotential
open SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- Effectivity is checked vertex by vertex: core vertices and interior
vertices separately. Row-independent generalization of the
`effective_of_cases` helper otherwise restated for each direct genus-four
row (e.g. `GenusFourCore100.effective_of_cases`). -/
theorem effective_of_cases {D : CFDiv spec.graph}
    (hcore : ∀ u : Fin n, 0 ≤ D (spec.coreVertex u))
    (hint : ∀ (edge : Fin p) (offset : Fin (spec.length edge - 1)),
      0 ≤ D (spec.interiorVertex edge offset)) :
    effective D := by
  intro v
  rcases v with u | ⟨edge, offset⟩
  · exact hcore u
  · exact hint edge offset

/-- An explicit firing script realizing an effective representative with a
chip at `q` proves that `D` reaches `q`. Row-independent generalization of
the `reaches_of_script` helper otherwise restated for each direct
genus-four row (e.g. `GenusFourCore100.reaches_of_script`). -/
theorem reaches_of_script (D : CFDiv spec.graph)
    (script : firingScript spec.graph) (q : spec.graph.V)
    (hEffective : effective (D + prin spec.graph script))
    (hChip : 1 ≤ (D + prin spec.graph script) q) :
    Certificate.StrongSeparator.Reaches spec.graph D q := by
  refine Certificate.StrongSeparator.reaches_of_effective_representative
    ?_ hEffective hChip
  unfold linearEquiv
  rw [principal_iff_eq_prin]
  exact ⟨script, by abel⟩

end Utilities.Certificate.SubdivisionGraph.Spec

namespace MarkedGraphs.Certificate
open Utilities.Certificate
open Utilities
open Finset
open ExplicitPotential
open SubdivisionGraph

/-! ## Sorted break lists

Pure list combinatorics on `List (ℕ × ℤ)`: none of it mentions a
`SubdivisionGraph.Spec`, but it is housed in the same namespace as
`breakSlope`/`breakSlopeFrom` (`AffinePositionMultiBreak.lean`) for
discoverability. -/

end MarkedGraphs.Certificate

namespace Utilities.Certificate.SubdivisionGraph.Spec
open MarkedGraphs
open MarkedGraphs.Certificate

open Utilities.Certificate
open Utilities
open Finset
open ExplicitPotential
open SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- A break list is sorted when its start positions strictly increase along
the list, in list order. Every break list actually produced by a script
whose entries are supplied in increasing-coordinate order has this shape
(`AffinePosition.SlopeScript.sortedBreaks_of_coordinate_lt`). -/
def BreakSorted (breaks : List (ℕ × ℤ)) : Prop :=
  breaks.Pairwise (fun a b => a.1 < b.1)

@[simp] theorem breakSorted_nil : BreakSorted ([] : List (ℕ × ℤ)) :=
  List.Pairwise.nil

/-- The scan never fires, and the initial value survives, once every
remaining entry starts strictly after the query point. -/
theorem breakSlopeFrom_eq_initial_of_forall_lt (breaks : List (ℕ × ℤ)) (k : ℕ)
    (hAfter : ∀ entry ∈ breaks, k < entry.1) (initial : ℤ) :
    breakSlopeFrom initial breaks k = initial := by
  induction breaks generalizing initial with
  | nil => rfl
  | cons entry rest ih =>
      rw [breakSlopeFrom_cons,
        if_neg (by have := hAfter entry (by simp); omega)]
      exact ih (fun e he => hAfter e (List.mem_cons_of_mem _ he)) initial

/-- A break list evaluates to `0` strictly before its first entry: the `k`
below every start behaves as if the list were empty. -/
theorem breakSlope_eq_zero_of_forall_lt (breaks : List (ℕ × ℤ)) (k : ℕ)
    (hAfter : ∀ entry ∈ breaks, k < entry.1) :
    breakSlope breaks k = 0 :=
  breakSlopeFrom_eq_initial_of_forall_lt breaks k hAfter 0

/-- The scan distributes over list append: it can be run on the first part
and resumed on the rest with the resulting value as the new initial
value. -/
theorem breakSlopeFrom_append (initial : ℤ) (pre rest : List (ℕ × ℤ)) (k : ℕ) :
    breakSlopeFrom initial (pre ++ rest) k =
      breakSlopeFrom (breakSlopeFrom initial pre k) rest k := by
  induction pre generalizing initial with
  | nil => rfl
  | cons entry pre' ih =>
      rw [List.cons_append, breakSlopeFrom_cons, breakSlopeFrom_cons, ih]

/-- The value of the scan at a chosen entry's own start position: whatever
precedes the entry is irrelevant (the entry itself applies once reached,
since `entry.1 ≤ k` for `k = entry.1`), and nothing after it in the list can
override it once everything after it starts strictly later than `k`. This
is the closed form `SegmentReflection.value`/`GenusFourCore100.rampSlope`/
`capSlope` hard-code for two or three pieces, given here once for any
number of pieces and needing no global sortedness hypothesis. -/
theorem breakSlope_append_cons_eq (pre : List (ℕ × ℤ)) (entry : ℕ × ℤ)
    (post : List (ℕ × ℤ)) (k : ℕ) (hEntry : entry.1 ≤ k)
    (hPost : ∀ e ∈ post, k < e.1) :
    breakSlope (pre ++ entry :: post) k = entry.2 := by
  unfold breakSlope
  rw [breakSlopeFrom_append, breakSlopeFrom_cons, if_pos hEntry]
  exact breakSlopeFrom_eq_initial_of_forall_lt post k hPost entry.2

/-- The value of a sorted break list at any point `k` at or after a member
`entry`, as long as no *other* member of the list starts strictly between
`entry` and `k`, is exactly `entry`'s slope: sortedness places every other
member either at or before `entry` (irrelevant, `entry` overrides it) or
strictly after `k` (irrelevant, it is never reached). This is the general
"current regime" reading of a sorted break list; evaluating it at `k =
entry.1` recovers `breakSlope_eq_of_breakSorted` below. -/
theorem breakSlope_eq_of_breakSorted_le {breaks : List (ℕ × ℤ)}
    (hSorted : BreakSorted breaks) {entry : ℕ × ℤ} (hMem : entry ∈ breaks)
    {k : ℕ} (hLe : entry.1 ≤ k)
    (hNoOther : ∀ other ∈ breaks, entry.1 < other.1 → k < other.1) :
    breakSlope breaks k = entry.2 := by
  obtain ⟨pre, post, hSplit⟩ := List.append_of_mem hMem
  rw [hSplit] at hSorted ⊢
  unfold BreakSorted at hSorted
  rw [List.pairwise_append, List.pairwise_cons] at hSorted
  refine breakSlope_append_cons_eq pre entry post k hLe (fun e he => ?_)
  refine hNoOther e ?_ (hSorted.2.1.1 e he)
  rw [hSplit]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ he)

/-- The value of a sorted break list at one of its own start positions is
exactly that entry's slope. Special case of `breakSlope_eq_of_breakSorted_le`
at `k = entry.1`. -/
theorem breakSlope_eq_of_breakSorted {breaks : List (ℕ × ℤ)}
    (hSorted : BreakSorted breaks) {entry : ℕ × ℤ} (hMem : entry ∈ breaks) :
    breakSlope breaks entry.1 = entry.2 :=
  breakSlope_eq_of_breakSorted_le hSorted hMem le_rfl (fun _ _ h => h)

end Utilities.Certificate.SubdivisionGraph.Spec

namespace MarkedGraphs.Certificate
open Utilities.Certificate
open Utilities
open Finset
open ExplicitPotential
open SubdivisionGraph

/-! ## Affine-positioned marches -/

namespace AffinePosition

namespace SlopeScript

variable {m n p b : ℕ}

/-- If a script entry names `edge`, its decoded `(coordinate, slope)` pair is
a member of the decoded break list for `edge`. Converse of
`exists_of_mem_breaks`. -/
theorem mem_breaks_of_edge_eq
    (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (point : Fin m → ℤ) (edge : Fin p)
    (index : Fin b) (hEdge : (script.entry index).position.edge = edge) :
    ((script.entry index).position.coordinate certificate point,
        (script.entry index).slope) ∈ script.breaks certificate point edge := by
  rw [breaks, List.mem_filterMap]
  exact ⟨script.entry index, List.mem_ofFn.mpr ⟨index, rfl⟩, by rw [if_pos hEdge]⟩

/-- Every slot's decoded break list is sorted. -/
def SortedBreaks (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (point : Fin m → ℤ) : Prop :=
  ∀ edge : Fin p,
    SubdivisionGraph.Spec.BreakSorted (script.breaks certificate point edge)

/-- Sufficient condition for `SortedBreaks`: on every slot, breaks named by
an earlier script index have a strictly smaller decoded coordinate than
breaks named by a later one. This is the condition a script author actually
establishes (breaks are written down in the order the chip should pass
through them), and it is enough to make every slot's decoded break list
sorted, without ever materializing that list. -/
theorem sortedBreaks_of_coordinate_lt
    (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (point : Fin m → ℤ)
    (hOrder : ∀ edge : Fin p, ∀ i j : Fin b, i < j →
      (script.entry i).position.edge = edge →
      (script.entry j).position.edge = edge →
      (script.entry i).position.coordinate certificate point <
        (script.entry j).position.coordinate certificate point) :
    script.SortedBreaks certificate point := by
  intro edge
  show (script.breaks certificate point edge).Pairwise (fun a c => a.1 < c.1)
  rw [breaks, List.pairwise_filterMap, List.pairwise_ofFn]
  intro i j hij pairA hA pairB hB
  by_cases hiEdge : (script.entry i).position.edge = edge
  · by_cases hjEdge : (script.entry j).position.edge = edge
    · rw [if_pos hiEdge] at hA
      rw [if_pos hjEdge] at hB
      cases hA
      cases hB
      exact hOrder edge i j hij hiEdge hjEdge
    · rw [if_neg hjEdge] at hB
      simp at hB
  · rw [if_neg hiEdge] at hA
    simp at hA

/-- Consistency data for a multi-break script that marches through its
breaks in coordinate order on every slot: the closing balance condition of
`Balanced`, together with sortedness of every slot's decoded break list.
The affine-positioned analogue of `GenusFourCore100.RampData`, generalized
from one window per slot to an arbitrary sorted sequence of them. -/
structure MarchData (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (potential : Fin n → ℤ) (point : Fin m → ℤ)
    (core_nonempty : 0 < n) {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) : Prop where
  balanced :
    script.Balanced certificate potential point core_nonempty hValid hCone
  sorted : script.SortedBreaks certificate point

/-- The Laplacian of a march at one of its own named breaks: the entry's
slope minus the running value just before it. Generalizes
`GenusFourCore100.rampSlope_diff`/`capSlope_diff` to an arbitrary sorted
sequence of affine-positioned breaks. -/
theorem prin_firingScript_atBreak
    (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (potential : Fin n → ℤ) (point : Fin m → ℤ)
    (core_nonempty : 0 < n) {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hMarch :
      script.MarchData certificate potential point core_nonempty hValid hCone)
    (edge : Fin p)
    (offset : Fin ((certificate.subdivisionSpec point core_nonempty hValid hCone).length
      edge - 1))
    (index : Fin b) (hEdge : (script.entry index).position.edge = edge)
    (hCoordinate :
      (script.entry index).position.coordinate certificate point =
        offset.val + 1) :
    prin (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
        (script.firingScript certificate potential point core_nonempty hValid hCone)
        ((certificate.subdivisionSpec point core_nonempty hValid hCone).interiorVertex
          edge offset) =
      (script.entry index).slope -
        SubdivisionGraph.Spec.breakSlope (script.breaks certificate point edge)
          offset.val := by
  rw [script.prin_firingScript_interiorVertex certificate potential point
      core_nonempty hValid hCone hMarch.balanced edge offset, ← hCoordinate,
    SubdivisionGraph.Spec.breakSlope_eq_of_breakSorted (hMarch.sorted edge)
      (script.mem_breaks_of_edge_eq certificate point edge index hEdge)]

end SlopeScript

end AffinePosition

end MarkedGraphs.Certificate
