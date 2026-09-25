/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionIso

/-!
# Orbit reduction at the bare core: the generic transport

The repository certifies "only a fundamental domain of the core's
automorphism group" at several different packagings of the same core data.
This module states the transport once at the common denominator, which is a
bare `ExplicitPotential.Core n p` together with a positive length vector.  No
row structure, no catalog metadata and no marked data enter the statement.  A
`CoreSymmetry` is an occurrence-sensitive automorphism of the ordered core: it
permutes core vertices and edge *slots*, and may independently reverse the
reading direction of each slot.  Given any two positive length vectors matched
along the slot permutation, such a symmetry produces a
`SubdivisionGraph.Spec.Relabeling`, hence a `LaplacianEquiv` and a
`CFGraphIso`, and therefore transports `BNExists` in both directions.

The declarations use the established `Utilities.Certificate.CoreOrbitReduction`
namespace for API compatibility.
-/

@[expose] public section

namespace Utilities.Certificate.CoreOrbitReduction
open Utilities.Certificate

open Utilities

open ExplicitPotential
open SubdivisionGraph

universe u v w

variable {n p : ℕ}

/-! ### The general symmetry datum -/

/-- An occurrence-sensitive automorphism of a bare ordered core.

`slotPerm` acts on edge *occurrences*, so parallel core edges are never
identified.  `reversed edge = true` records that the image slot is read from
the image of the head to the image of the tail; the two endpoint equations
certify exactly that reading. -/
structure CoreSymmetry (core : ExplicitPotential.Core n p) where
  /-- Permutation of core vertices. -/
  vertexPerm : Equiv.Perm (Fin n)
  /-- Permutation of edge slots (occurrences, not endpoint pairs). -/
  slotPerm : Equiv.Perm (Fin p)
  /-- Per-slot orientation reversal flag. -/
  reversed : Fin p → Bool
  tail_eq : ∀ edge : Fin p,
    core.tail (slotPerm edge) =
      if reversed edge then vertexPerm (core.head edge)
      else vertexPerm (core.tail edge)
  head_eq : ∀ edge : Fin p,
    core.head (slotPerm edge) =
      if reversed edge then vertexPerm (core.tail edge)
      else vertexPerm (core.head edge)

namespace CoreSymmetry

variable {core : ExplicitPotential.Core n p}

/-- The identity symmetry. -/
def refl (core : ExplicitPotential.Core n p) : CoreSymmetry core where
  vertexPerm := Equiv.refl _
  slotPerm := Equiv.refl _
  reversed := fun _ => false
  tail_eq := fun _ => rfl
  head_eq := fun _ => rfl

/-- A pure slot permutation of a core, i.e. a permutation of edge occurrences
fixing every endpoint.  This is the shape used by the genus-four catalog rows
to sort parallel slot pairs. -/
def ofSlotPerm (core : ExplicitPotential.Core n p) (σ : Equiv.Perm (Fin p))
    (hTail : ∀ edge, core.tail (σ edge) = core.tail edge)
    (hHead : ∀ edge, core.head (σ edge) = core.head edge) :
    CoreSymmetry core where
  vertexPerm := Equiv.refl _
  slotPerm := σ
  reversed := fun _ => false
  tail_eq := hTail
  head_eq := hHead

/-- **The smart constructor for hand-written or generated automorphisms.**
Build a `CoreSymmetry` from raw vertex- and slot-permutation *functions*
together with a reversal flag, checking bijectivity by injectivity (a finite
endofunction is bijective iff it is injective) rather than carrying an
inverse function by hand.  At a concrete core all four hypotheses are
`by decide`.

This is the public successor of the retired
`Certificate/CoreAutomorphismOrbit.lean`'s `mkCoreSymmetry`, which was
specialized to eight-vertex, twelve-slot cores. -/
noncomputable def ofMaps (core : ExplicitPotential.Core n p)
    (vertexMap : Fin n → Fin n) (slotMap : Fin p → Fin p) (reversed : Fin p → Bool)
    (hVertex : ∀ i j : Fin n, vertexMap i = vertexMap j → i = j)
    (hSlot : ∀ i j : Fin p, slotMap i = slotMap j → i = j)
    (hTail : ∀ edge : Fin p, core.tail (slotMap edge) =
      if reversed edge then vertexMap (core.head edge) else vertexMap (core.tail edge))
    (hHead : ∀ edge : Fin p, core.head (slotMap edge) =
      if reversed edge then vertexMap (core.tail edge) else vertexMap (core.head edge)) :
    CoreSymmetry core where
  vertexPerm := Equiv.ofBijective vertexMap
    (Finite.injective_iff_bijective.mp (fun i j hij => hVertex i j hij))
  slotPerm := Equiv.ofBijective slotMap
    (Finite.injective_iff_bijective.mp (fun i j hij => hSlot i j hij))
  reversed := reversed
  tail_eq := hTail
  head_eq := hHead

@[simp] theorem ofMaps_slotPerm (core : ExplicitPotential.Core n p)
    (vertexMap : Fin n → Fin n) (slotMap : Fin p → Fin p) (reversed : Fin p → Bool)
    (hVertex hSlot hTail hHead) (edge : Fin p) :
    (ofMaps core vertexMap slotMap reversed hVertex hSlot hTail hHead).slotPerm edge =
      slotMap edge := rfl

@[simp] theorem ofMaps_vertexPerm (core : ExplicitPotential.Core n p)
    (vertexMap : Fin n → Fin n) (slotMap : Fin p → Fin p) (reversed : Fin p → Bool)
    (hVertex hSlot hTail hHead) (vertex : Fin n) :
    (ofMaps core vertexMap slotMap reversed hVertex hSlot hTail hHead).vertexPerm vertex =
      vertexMap vertex := rfl

/-- **The kernel-transparent constructor.**

`ofMaps` is the convenient one — it checks bijectivity by injectivity — but it
builds its permutations with `Equiv.ofBijective`, and `Equiv.symm` of such a
permutation does **not** reduce in the kernel.  Forward application still
reduces (`ofMaps_vertexPerm` and `ofMaps_slotPerm` above are both `rfl`), so a
`decide` about `vertexPerm` cannot tell the two constructions apart.  What
breaks is `reindexLength`, which is `fun edge => length (slotPerm.symm edge)`,
and with it every consumer of it — `ClosedCoreSymmetry.targetLength` and the
closed-orthant orbit and chamber arguments.

`ofInverses` takes the two inverse functions explicitly, so every projection,
forward and backward, reduces.  **Use it whenever the symmetry will be fed to
`reindexLength`**; `reindexLength_ofInverses` below is the one-line regression
test that the reduction is really there. -/
def ofInverses (core : ExplicitPotential.Core n p)
    (vertexMap vertexInv : Fin n → Fin n) (slotMap slotInv : Fin p → Fin p)
    (reversed : Fin p → Bool)
    (hVertexLeft : ∀ x, vertexInv (vertexMap x) = x)
    (hVertexRight : ∀ x, vertexMap (vertexInv x) = x)
    (hSlotLeft : ∀ e, slotInv (slotMap e) = e)
    (hSlotRight : ∀ e, slotMap (slotInv e) = e)
    (hTail : ∀ edge : Fin p, core.tail (slotMap edge) =
      if reversed edge then vertexMap (core.head edge) else vertexMap (core.tail edge))
    (hHead : ∀ edge : Fin p, core.head (slotMap edge) =
      if reversed edge then vertexMap (core.tail edge) else vertexMap (core.head edge)) :
    CoreSymmetry core where
  vertexPerm := ⟨vertexMap, vertexInv, hVertexLeft, hVertexRight⟩
  slotPerm := ⟨slotMap, slotInv, hSlotLeft, hSlotRight⟩
  reversed := reversed
  tail_eq := hTail
  head_eq := hHead

@[simp] theorem ofInverses_vertexPerm (core : ExplicitPotential.Core n p)
    (vertexMap vertexInv : Fin n → Fin n) (slotMap slotInv : Fin p → Fin p)
    (reversed : Fin p → Bool)
    (hVL hVR hSL hSR hTail hHead) (vertex : Fin n) :
    (ofInverses core vertexMap vertexInv slotMap slotInv reversed
      hVL hVR hSL hSR hTail hHead).vertexPerm vertex = vertexMap vertex := rfl

@[simp] theorem ofInverses_slotPerm (core : ExplicitPotential.Core n p)
    (vertexMap vertexInv : Fin n → Fin n) (slotMap slotInv : Fin p → Fin p)
    (reversed : Fin p → Bool)
    (hVL hVR hSL hSR hTail hHead) (edge : Fin p) :
    (ofInverses core vertexMap vertexInv slotMap slotInv reversed
      hVL hVR hSL hSR hTail hHead).slotPerm edge = slotMap edge := rfl

@[simp] theorem ofInverses_slotPerm_symm (core : ExplicitPotential.Core n p)
    (vertexMap vertexInv : Fin n → Fin n) (slotMap slotInv : Fin p → Fin p)
    (reversed : Fin p → Bool)
    (hVL hVR hSL hSR hTail hHead) (edge : Fin p) :
    (ofInverses core vertexMap vertexInv slotMap slotInv reversed
      hVL hVR hSL hSR hTail hHead).slotPerm.symm edge = slotInv edge := rfl

/-- The composite of two core symmetries: apply `first`, then `second`. -/
def trans (first second : CoreSymmetry core) : CoreSymmetry core where
  vertexPerm := first.vertexPerm.trans second.vertexPerm
  slotPerm := first.slotPerm.trans second.slotPerm
  reversed := fun edge => xor (first.reversed edge) (second.reversed (first.slotPerm edge))
  tail_eq := fun edge => by
    have h1t := first.tail_eq edge
    have h1h := first.head_eq edge
    have h2t := second.tail_eq (first.slotPerm edge)
    have h2h := second.head_eq (first.slotPerm edge)
    by_cases hr1 : first.reversed edge <;> by_cases hr2 : second.reversed (first.slotPerm edge) <;>
      simp_all [Equiv.trans_apply]
  head_eq := fun edge => by
    have h1t := first.tail_eq edge
    have h1h := first.head_eq edge
    have h2t := second.tail_eq (first.slotPerm edge)
    have h2h := second.head_eq (first.slotPerm edge)
    by_cases hr1 : first.reversed edge <;> by_cases hr2 : second.reversed (first.slotPerm edge) <;>
      simp_all [Equiv.trans_apply]

/-! ### Reindexing a length vector -/

/-- Transport a length vector along the slot permutation. -/
def reindexLength (symmetry : CoreSymmetry core) (length : Fin p → ℕ) :
    Fin p → ℕ :=
  fun edge => length (symmetry.slotPerm.symm edge)

/-- **The regression test for the kernel-reduction hazard.**  For a symmetry
built by `ofInverses`, reindexing a length vector is definitionally the
composite with the supplied slot inverse — the `rfl` is the whole point.  The
same statement for `ofMaps` is **not** provable by `rfl`, because
`Equiv.ofBijective`'s inverse is opaque; that is the difference the two
constructors exist to record. -/
@[simp] theorem reindexLength_ofInverses (core : ExplicitPotential.Core n p)
    (vertexMap vertexInv : Fin n → Fin n) (slotMap slotInv : Fin p → Fin p)
    (reversed : Fin p → Bool)
    (hVL hVR hSL hSR hTail hHead) (length : Fin p → ℕ) (edge : Fin p) :
    (ofInverses core vertexMap vertexInv slotMap slotInv reversed
        hVL hVR hSL hSR hTail hHead).reindexLength length edge =
      length (slotInv edge) := rfl

theorem reindexLength_pos (symmetry : CoreSymmetry core) (length : Fin p → ℕ)
    (hLength : ∀ edge, 0 < length edge) :
    ∀ edge, 0 < symmetry.reindexLength length edge :=
  fun edge => hLength (symmetry.slotPerm.symm edge)

@[simp] theorem reindexLength_slotPerm (symmetry : CoreSymmetry core)
    (length : Fin p → ℕ) (edge : Fin p) :
    symmetry.reindexLength length (symmetry.slotPerm edge) = length edge := by
  simp [reindexLength]

/-- The compatibility hypothesis required by `relabeling`, in the canonical
`reindexLength` case. -/
theorem reindexLength_compat (symmetry : CoreSymmetry core)
    (length : Fin p → ℕ) (edge : Fin p) :
    length edge = symmetry.reindexLength length (symmetry.slotPerm edge) :=
  (symmetry.reindexLength_slotPerm length edge).symm

@[simp] theorem reindexLength_refl (length : Fin p → ℕ) :
    (CoreSymmetry.refl core).reindexLength length = length := rfl

theorem reindexLength_trans (first second : CoreSymmetry core)
    (length : Fin p → ℕ) :
    (first.trans second).reindexLength length =
      second.reindexLength (first.reindexLength length) := rfl

/-! ### The general relabeling -/

section Relabeling

variable (core_nonempty : 0 < n)
  (core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)

/-- The subdivision of `core` at a positive length vector. -/
abbrev spec (core : ExplicitPotential.Core n p) (core_nonempty : 0 < n)
    (core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (length : Fin p → ℕ) (hLength : ∀ edge, 0 < length edge) :
    SubdivisionGraph.Spec n p :=
  SubdivisionGraph.Spec.ofCore core core_nonempty core_loopless length hLength

/-- **The general transport datum.**  A core symmetry, together with any two
positive length vectors matched along its slot permutation, is a checked
slotwise relabeling from the subdivision at `length` to the subdivision at
`length'`.

Stating the two length vectors independently (rather than forcing
`length' = reindexLength length`) is what lets the same lemma serve both the
row packaging, which reindexes, and the catalog rows, which sort a chosen
pair of parallel slots. -/
def relabeling (symmetry : CoreSymmetry core)
    (length length' : Fin p → ℕ)
    (hLength : ∀ edge, 0 < length edge) (hLength' : ∀ edge, 0 < length' edge)
    (hCompat : ∀ edge, length edge = length' (symmetry.slotPerm edge)) :
    (spec core core_nonempty core_loopless length hLength).Relabeling
      (spec core core_nonempty core_loopless length' hLength') where
  coreEquiv := symmetry.vertexPerm
  slotEquiv := symmetry.slotPerm
  reversed := symmetry.reversed
  length_eq := hCompat
  tail_eq := symmetry.tail_eq
  head_eq := symmetry.head_eq

/-- The Laplacian equivalence carried by a core symmetry. -/
def laplacianEquiv (symmetry : CoreSymmetry core)
    (length length' : Fin p → ℕ)
    (hLength : ∀ edge, 0 < length edge) (hLength' : ∀ edge, 0 < length' edge)
    (hCompat : ∀ edge, length edge = length' (symmetry.slotPerm edge)) :
    LaplacianEquiv (spec core core_nonempty core_loopless length hLength).graph
      (spec core core_nonempty core_loopless length' hLength').graph :=
  SubdivisionGraph.Spec.laplacianEquiv _ _
    (symmetry.relabeling core_nonempty core_loopless length length'
      hLength hLength' hCompat)

/-- The graph isomorphism carried by a core symmetry. -/
def graphIso (symmetry : CoreSymmetry core)
    (length length' : Fin p → ℕ)
    (hLength : ∀ edge, 0 < length edge) (hLength' : ∀ edge, 0 < length' edge)
    (hCompat : ∀ edge, length edge = length' (symmetry.slotPerm edge)) :
    CFGraphIso (spec core core_nonempty core_loopless length hLength).graph
      (spec core core_nonempty core_loopless length' hLength').graph :=
  SubdivisionGraph.Spec.graphIso _ _
    (symmetry.relabeling core_nonempty core_loopless length length'
      hLength hLength' hCompat)

/-- The vertex bijection carried by a core symmetry. -/
def vertexEquiv (symmetry : CoreSymmetry core)
    (length length' : Fin p → ℕ)
    (hLength : ∀ edge, 0 < length edge) (hLength' : ∀ edge, 0 < length' edge)
    (hCompat : ∀ edge, length edge = length' (symmetry.slotPerm edge)) :
    (spec core core_nonempty core_loopless length hLength).Vertex ≃
      (spec core core_nonempty core_loopless length' hLength').Vertex :=
  SubdivisionGraph.Spec.vertexEquiv _ _
    (symmetry.relabeling core_nonempty core_loopless length length'
      hLength hLength' hCompat)

@[simp] theorem vertexEquiv_coreVertex (symmetry : CoreSymmetry core)
    (length length' : Fin p → ℕ)
    (hLength : ∀ edge, 0 < length edge) (hLength' : ∀ edge, 0 < length' edge)
    (hCompat : ∀ edge, length edge = length' (symmetry.slotPerm edge))
    (vertex : Fin n) :
    symmetry.vertexEquiv core_nonempty core_loopless length length'
        hLength hLength' hCompat
        ((spec core core_nonempty core_loopless length hLength).coreVertex vertex) =
      (spec core core_nonempty core_loopless length' hLength').coreVertex
        (symmetry.vertexPerm vertex) := rfl

/-! ### The transport corollary -/

/-- **Transport of Brill--Noether existence, in both directions.**  A core
symmetry makes the subdivisions at two matched length vectors carry exactly
the same existence statements. -/
theorem bnExists_iff (symmetry : CoreSymmetry core)
    (length length' : Fin p → ℕ)
    (hLength : ∀ edge, 0 < length edge) (hLength' : ∀ edge, 0 < length' edge)
    (hCompat : ∀ edge, length edge = length' (symmetry.slotPerm edge))
    (r d : ℤ) :
    BNExists (spec core core_nonempty core_loopless length' hLength').graph r d ↔
      BNExists (spec core core_nonempty core_loopless length hLength).graph r d :=
  (symmetry.graphIso core_nonempty core_loopless length length'
    hLength hLength' hCompat).BNExists_iff r d

/-- Forward direction of `bnExists_iff`, spelled out. -/
theorem bnExists_of_bnExists (symmetry : CoreSymmetry core)
    (length length' : Fin p → ℕ)
    (hLength : ∀ edge, 0 < length edge) (hLength' : ∀ edge, 0 < length' edge)
    (hCompat : ∀ edge, length edge = length' (symmetry.slotPerm edge))
    (r d : ℤ)
    (hBN : BNExists
      (spec core core_nonempty core_loopless length hLength).graph r d) :
    BNExists (spec core core_nonempty core_loopless length' hLength').graph r d :=
  (symmetry.bnExists_iff core_nonempty core_loopless length length'
    hLength hLength' hCompat r d).mpr hBN

/-- Backward direction of `bnExists_iff`, spelled out.  This is the direction
the catalog rows use: solve the sorted chamber, conclude at arbitrary
lengths. -/
theorem bnExists_of_bnExists' (symmetry : CoreSymmetry core)
    (length length' : Fin p → ℕ)
    (hLength : ∀ edge, 0 < length edge) (hLength' : ∀ edge, 0 < length' edge)
    (hCompat : ∀ edge, length edge = length' (symmetry.slotPerm edge))
    (r d : ℤ)
    (hBN : BNExists
      (spec core core_nonempty core_loopless length' hLength').graph r d) :
    BNExists (spec core core_nonempty core_loopless length hLength).graph r d :=
  (symmetry.bnExists_iff core_nonempty core_loopless length length'
    hLength hLength' hCompat r d).mp hBN

/-- The reindexing shape used by the genus-four catalog rows that sort a
parallel slot pair by permuting the length vector (`GenusFourCore034`):
solve at the reindexed lengths, conclude at the original lengths.  Here the
compatibility hypothesis is discharged automatically. -/
theorem bnExists_of_reindexed (symmetry : CoreSymmetry core)
    (length : Fin p → ℕ) (hLength : ∀ edge, 0 < length edge) (r d : ℤ)
    (hBN : BNExists (spec core core_nonempty core_loopless
      (symmetry.reindexLength length)
      (symmetry.reindexLength_pos length hLength)).graph r d) :
    BNExists (spec core core_nonempty core_loopless length hLength).graph r d :=
  symmetry.bnExists_of_bnExists' core_nonempty core_loopless length
    (symmetry.reindexLength length) hLength
    (symmetry.reindexLength_pos length hLength)
    (symmetry.reindexLength_compat length) r d hBN

end Relabeling

end CoreSymmetry

/-! ### The genus-four slot-permutation transport, re-derived

The statement below was `MarkedGraphs.Certificate.GenusFourCore066.bnExists_of_slotPerm`,
copied verbatim (only the name is primed); that row's cover has since been
retired, and this is now the only copy.  It is proved as a corollary of
`CoreSymmetry.bnExists_iff` rather than by building a `Spec.Relabeling` by
hand, which is the evidence that the abstraction of this file really does
subsume that instance. -/

/-- Existence transports along a tail- and head-preserving permutation of the
edge slots of a fixed core: the subdivision at lengths `length ∘ σ` is
isomorphic to the subdivision at `length`.  This is the special case of
`SubdivisionIso` with the identity vertex relabeling and no reversed slots; it
is what discharges a parallel-slot ordering row. -/
theorem bnExists_of_slotPerm' {n p : ℕ} (core : ExplicitPotential.Core n p)
    (core_nonempty : 0 < n)
    (core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (σ : Equiv.Perm (Fin p))
    (hTail : ∀ edge, core.tail (σ edge) = core.tail edge)
    (hHead : ∀ edge, core.head (σ edge) = core.head edge)
    (length : Fin p → ℕ) (hLength : ∀ edge, 0 < length edge)
    (hLength' : ∀ edge, 0 < length (σ edge))
    (hBN : BNExists (SubdivisionGraph.Spec.ofCore core core_nonempty core_loopless
      (fun edge => length (σ edge)) hLength').graph 1 3) :
    BNExists (SubdivisionGraph.Spec.ofCore core core_nonempty core_loopless
      length hLength).graph 1 3 :=
  (CoreSymmetry.ofSlotPerm core σ hTail hHead).bnExists_of_bnExists
    core_nonempty core_loopless (fun edge => length (σ edge)) length
    hLength' hLength (fun _ => rfl) 1 3 hBN

/-- **One sorting step.**  If existence is known on the half-space
`L a ≤ L b` under a side condition `C` that the transposition of the parallel
slot pair `{a, b}` preserves, then it holds everywhere `C` does: an unsorted
length vector is sorted by the transposition, and existence transports back
along it by `bnExists_of_slotPerm'`.

This is what discharges the parallel-slot ordering rows a mixed cover's
advertised base chamber may retain, one pair at a time, instead of by a
`2 ^ (number of pairs)` case split.  It came from `GenusFourCore066.lean`,
whose cover was retired on 2026-08-18 in favour of
the corresponding closed-row proof module; the lemma is general and outlives that row. -/
theorem bnExists_of_pairSort {n p : ℕ} (core : ExplicitPotential.Core n p)
    (core_nonempty : 0 < n)
    (core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (a b : Fin p)
    (hTail : ∀ edge, core.tail (Equiv.swap a b edge) = core.tail edge)
    (hHead : ∀ edge, core.head (Equiv.swap a b edge) = core.head edge)
    (C : (Fin p → ℕ) → Prop)
    (hCswap : ∀ length : Fin p → ℕ, C length →
      C (fun edge => length (Equiv.swap a b edge)))
    (H : ∀ (length : Fin p → ℕ) (hLength : ∀ edge, 0 < length edge),
      C length → length a ≤ length b →
      BNExists (SubdivisionGraph.Spec.ofCore core core_nonempty core_loopless
        length hLength).graph 1 3)
    (length : Fin p → ℕ) (hLength : ∀ edge, 0 < length edge) (hC : C length) :
    BNExists (SubdivisionGraph.Spec.ofCore core core_nonempty core_loopless
      length hLength).graph 1 3 := by
  by_cases hab : length a ≤ length b
  · exact H length hLength hC hab
  · refine bnExists_of_slotPerm' core core_nonempty core_loopless
      (Equiv.swap a b) hTail hHead length hLength (fun edge => hLength _) ?_
    refine H _ (fun edge => hLength _) (hCswap length hC) ?_
    show length (Equiv.swap a b a) ≤ length (Equiv.swap a b b)
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
    omega

end Utilities.Certificate.CoreOrbitReduction
