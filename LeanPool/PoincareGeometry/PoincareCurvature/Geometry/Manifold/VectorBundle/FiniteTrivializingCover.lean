/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Finite compact covers subordinate to bundle trivializations

On a compact Hausdorff base, the preferred trivialization at each point gives
an open cover.  Compactness extracts a finite subcover, and the finite compact
shrinking lemma replaces it by compact pieces subordinate to the same
trivializations.  This file packages that construction in the exact shape
used by the repository's Banach space of continuous bundle sections.
-/

@[expose] public noncomputable section
open Bundle Set
open scoped Topology

namespace PoincareCurvature
namespace Bundle.Trivialization

variable
  {F M : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)]
  [FiberBundle F V]

/-- The compact overlap of two pieces in a finite compact cover. -/
def compactOverlap {s : Finset M}
    (Kc : s → TopologicalSpace.Compacts M) (i j : s) :
    TopologicalSpace.Compacts M :=
  ⟨(Kc i : Set M) ∩ (Kc j : Set M), (Kc i).isCompact.inter (Kc j).isCompact⟩

@[simp]
theorem coe_compactOverlap {s : Finset M}
    (Kc : s → TopologicalSpace.Compacts M) (i j : s) :
    (compactOverlap Kc i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M) :=
  rfl

theorem compactOverlap_subset {s : Finset M}
    (Kc : s → TopologicalSpace.Compacts M) (i j : s) :
    (compactOverlap Kc i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M) :=
  subset_rfl

/-- Every compact Hausdorff base admits a finite compact cover subordinate to
the preferred bundle trivializations.  The finite index type is the subtype
of a concrete `Finset M`, so all later finite-product and completeness
instances are available without any additional choice of atlas. -/
theorem exists_finite_compact_preferred_trivializingCover
    [CompactSpace M] :
    ∃ (s : Finset M) (Kc : s → TopologicalSpace.Compacts M),
      (∀ i : s,
        (Kc i : Set M) ⊆ (trivializationAt F V (i : M)).baseSet) ∧
      (⋃ i : s, (Kc i : Set M)) = Set.univ := by
  classical
  let U : M → Set M := fun x => (trivializationAt F V x).baseSet
  have hUopen : ∀ x : M, IsOpen (U x) := fun x =>
    (trivializationAt F V x).open_baseSet
  have hUcover : Set.univ ⊆ ⋃ x : M, U x := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨x, mem_baseSet_trivializationAt F V x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen hUcover
  obtain ⟨K, hKcompact, hKsub, hKcover⟩ :=
    isCompact_univ.finite_compact_cover s U
      (fun i hi => hUopen i) (by simpa using hs)
  let Kc : s → TopologicalSpace.Compacts M := fun i =>
    ⟨K (i : M), hKcompact (i : M)⟩
  refine ⟨s, Kc, ?_, ?_⟩
  · intro i
    exact hKsub (i : M)
  · calc
      (⋃ i : s, (Kc i : Set M)) = ⋃ i ∈ s, K i := by
        ext x
        simp [Kc]
      _ = Set.univ := hKcover.symm

/-- The preceding cover, together with the canonical compact overlaps, has
all of the subset and exact-overlap fields expected by
`ContinuousSectionSpace`. -/
theorem exists_finite_compact_preferred_trivializingCover_with_overlaps
    [CompactSpace M] :
    ∃ (s : Finset M) (Kc : s → TopologicalSpace.Compacts M),
      (∀ i : s,
        (Kc i : Set M) ⊆ (trivializationAt F V (i : M)).baseSet) ∧
      (⋃ i : s, (Kc i : Set M)) = Set.univ ∧
      (∀ i j : s,
        (compactOverlap Kc i j : Set M) ⊆
          (Kc i : Set M) ∩ (Kc j : Set M)) ∧
      (∀ i j : s,
        (compactOverlap Kc i j : Set M) =
          (Kc i : Set M) ∩ (Kc j : Set M)) := by
  obtain ⟨s, Kc, hsub, hcover⟩ :=
    exists_finite_compact_preferred_trivializingCover (F := F) (V := V)
  exact ⟨s, Kc, hsub, hcover,
    fun i j => compactOverlap_subset Kc i j,
    fun i j => coe_compactOverlap Kc i j⟩

/-- A chosen finite compact cover subordinate to the preferred
trivializations of a bundle.  Pairwise compact overlaps are canonical and
therefore are not stored as additional data. -/
structure FiniteCompactPreferredTrivializingCover where
  centers : Finset M
  pieces : centers → TopologicalSpace.Compacts M
  pieces_subset_baseSet : ∀ i : centers,
    (pieces i : Set M) ⊆ (trivializationAt F V (i : M)).baseSet
  iUnion_pieces : (⋃ i : centers, (pieces i : Set M)) = Set.univ

namespace FiniteCompactPreferredTrivializingCover

/-- The finite type indexing a chosen cover. -/
abbrev Index (C : FiniteCompactPreferredTrivializingCover (F := F) (V := V)) :=
  C.centers

/-- The preferred trivialization associated to an index of the cover. -/
def trivialization
    (C : FiniteCompactPreferredTrivializingCover (F := F) (V := V))
    (i : C.Index) :
    Trivialization F (TotalSpace.proj : TotalSpace F V → M) :=
  trivializationAt F V (i : M)

instance memTrivializationAtlas_trivialization
    (C : FiniteCompactPreferredTrivializingCover (F := F) (V := V))
    (i : C.Index) : MemTrivializationAtlas (C.trivialization i) := by
  unfold trivialization
  infer_instance

/-- Canonical compact overlap pieces. -/
def overlaps
    (C : FiniteCompactPreferredTrivializingCover (F := F) (V := V))
    (i j : C.Index) : TopologicalSpace.Compacts M :=
  compactOverlap C.pieces i j

theorem overlaps_subset
    (C : FiniteCompactPreferredTrivializingCover (F := F) (V := V))
    (i j : C.Index) :
    (C.overlaps i j : Set M) ⊆
      (C.pieces i : Set M) ∩ (C.pieces j : Set M) :=
  compactOverlap_subset C.pieces i j

@[simp]
theorem coe_overlaps
    (C : FiniteCompactPreferredTrivializingCover (F := F) (V := V))
    (i j : C.Index) :
    (C.overlaps i j : Set M) =
      (C.pieces i : Set M) ∩ (C.pieces j : Set M) :=
  coe_compactOverlap C.pieces i j

/-- Choose finite compact preferred trivializing-cover data from compactness.
This is noncomputable only because it chooses a finite subcover and a compact
shrinking; its specifications are the proved fields of the structure. -/
noncomputable def chosen [CompactSpace M] :
    FiniteCompactPreferredTrivializingCover (F := F) (V := V) := by
  classical
  let h := exists_finite_compact_preferred_trivializingCover
    (F := F) (V := V)
  let s : Finset M := h.choose
  let hKc := h.choose_spec
  let Kc : s → TopologicalSpace.Compacts M := hKc.choose
  have hspec := hKc.choose_spec
  exact
    { centers := s
      pieces := Kc
      pieces_subset_baseSet := hspec.1
      iUnion_pieces := hspec.2 }

end FiniteCompactPreferredTrivializingCover

end Bundle.Trivialization
end PoincareCurvature
