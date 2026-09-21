/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.FiniteTrivializingCover

/-!
# Finite smooth partitions subordinate to preferred bundle trivializations

For a vector bundle over a compact finite-dimensional manifold, this file
extracts a finite preferred trivializing cover and equips it with a smooth
partition of unity.  The topological supports of the partition functions are
compact, lie in their corresponding trivialization domains, and cover the
whole manifold.  These are the geometric data needed for an honest
local-to-global parabolic parametrix.
-/

@[expose] public noncomputable section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace PoincareCurvature
namespace Bundle.Trivialization

variable
  {E H M F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [SigmaCompactSpace M]
  [NormedAddCommGroup F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)]
  [FiberBundle F V]

/-- The joint coordinate-and-bundle domain used by the tensor-heat local
parametrix at a center. -/
def preferredAnalysisDomain (p : M) : Set M :=
  (extChartAt I p).source ∩ (trivializationAt F V p).baseSet

theorem isOpen_preferredAnalysisDomain (p : M) :
    IsOpen (preferredAnalysisDomain I (F := F) (V := V) p) :=
  (isOpen_extChartAt_source p).inter (trivializationAt F V p).open_baseSet

theorem mem_preferredAnalysisDomain (p : M) :
    p ∈ preferredAnalysisDomain I (F := F) (V := V) p :=
  ⟨mem_extChartAt_source p, mem_baseSet_trivializationAt F V p⟩

/-- A finite smooth partition of unity subordinate to an arbitrary
point-indexed family of domains.  Keeping the family as a type parameter
lets later analytic constructions choose a radius separately at every point
before compactness extracts the finite subcover. -/
structure FiniteSmoothPointwiseSubordinateCover (domains : M → Set M) where
  centers : Finset M
  partition : SmoothPartitionOfUnity centers I M Set.univ
  subordinate : partition.IsSubordinate
    (fun i : centers => domains (i : M))

namespace FiniteSmoothPointwiseSubordinateCover

variable {I} {domains : M → Set M}

abbrev Index
    (C : FiniteSmoothPointwiseSubordinateCover I domains) :=
  C.centers

/-- Compact support of one member of the subordinate partition. -/
def pieces (C : FiniteSmoothPointwiseSubordinateCover I domains)
    (i : C.Index) : TopologicalSpace.Compacts M :=
  ⟨tsupport (C.partition i), isClosed_closure.isCompact⟩

@[simp]
theorem coe_pieces (C : FiniteSmoothPointwiseSubordinateCover I domains)
    (i : C.Index) :
    (C.pieces i : Set M) = tsupport (C.partition i) :=
  rfl

theorem pieces_subset_domain
    (C : FiniteSmoothPointwiseSubordinateCover I domains) (i : C.Index) :
    (C.pieces i : Set M) ⊆ domains (i : M) :=
  C.subordinate i

theorem iUnion_pieces
    (C : FiniteSmoothPointwiseSubordinateCover I domains) :
    (⋃ i : C.Index, (C.pieces i : Set M)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := C.partition.exists_pos_of_mem (Set.mem_univ x)
  exact Set.mem_iUnion.2
    ⟨i, subset_closure (Function.mem_support.2 (ne_of_gt hi))⟩

/-- Compactness and smooth partitions of unity turn any point-indexed open
family with `p ∈ domains p` into a finite subordinate smooth cover. -/
theorem exists_of_isOpen_mem
    (domains : M → Set M)
    (hopen : ∀ p : M, IsOpen (domains p))
    (hmem : ∀ p : M, p ∈ domains p) :
    Nonempty (FiniteSmoothPointwiseSubordinateCover I domains) := by
  classical
  have hcover : Set.univ ⊆ ⋃ p : M, domains p := by
    intro p _
    exact Set.mem_iUnion.2 ⟨p, hmem p⟩
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover domains hopen hcover
  let U : s → Set M := fun i => domains (i : M)
  have hUopen : ∀ i : s, IsOpen (U i) := fun i => hopen (i : M)
  have hUcover : Set.univ ⊆ ⋃ i : s, U i := by
    intro x hx
    have hx' : x ∈ ⋃ p ∈ s, domains p := hs hx
    simpa [U] using hx'
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    I isClosed_univ U hUopen hUcover
  exact ⟨{ centers := s, partition := ρ, subordinate := hρ }⟩

end FiniteSmoothPointwiseSubordinateCover

/-- A finite smooth partition of unity subordinate simultaneously to the
preferred manifold chart and preferred bundle trivialization at every
center. -/
structure FiniteSmoothPreferredTrivializingCover where
  centers : Finset M
  partition : SmoothPartitionOfUnity centers I M Set.univ
  subordinate : partition.IsSubordinate
    (fun i : centers =>
      preferredAnalysisDomain I (F := F) (V := V) (i : M))

namespace FiniteSmoothPreferredTrivializingCover

variable {I}

/-- The finite type indexing the cover. -/
abbrev Index
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V)) :=
  C.centers

/-- Preferred bundle trivialization at a cover center. -/
def trivialization
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    Trivialization F (TotalSpace.proj : TotalSpace F V → M) :=
  trivializationAt F V (i : M)

instance memTrivializationAtlas_trivialization
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) : MemTrivializationAtlas (C.trivialization i) := by
  unfold trivialization
  infer_instance

/-- Compact support piece belonging to one partition function. -/
def pieces
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) : TopologicalSpace.Compacts M :=
  ⟨tsupport (C.partition i), isClosed_closure.isCompact⟩

@[simp]
theorem coe_pieces
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.pieces i : Set M) = tsupport (C.partition i) :=
  rfl

theorem pieces_subset_baseSet
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.pieces i : Set M) ⊆ (C.trivialization i).baseSet := by
  change tsupport (C.partition i) ⊆
    (trivializationAt F V (i : M)).baseSet
  exact (C.subordinate i).trans inter_subset_right

/-- Each compact support piece lies in its preferred manifold chart. -/
theorem pieces_subset_chartSource
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.pieces i : Set M) ⊆ (extChartAt I (i : M)).source := by
  exact (C.subordinate i).trans inter_subset_left

/-- Each compact support piece lies in the exact joint local-analysis
domain used by the coordinate tensor-heat operator. -/
theorem pieces_subset_preferredAnalysisDomain
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.pieces i : Set M) ⊆
      preferredAnalysisDomain I (F := F) (V := V) (i : M) :=
  C.subordinate i

/-- The joint analysis domain transported to the model space by the
preferred extended chart. -/
def preferredCoordinateAnalysisDomain (p : M) : Set E :=
  (extChartAt I p).target ∩
    (extChartAt I p).symm ⁻¹' (trivializationAt F V p).baseSet

theorem isOpen_preferredCoordinateAnalysisDomain [I.Boundaryless] (p : M) :
    IsOpen (preferredCoordinateAnalysisDomain (I := I) (F := F) (V := V) p) :=
  (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
    (isOpen_extChartAt_target p) (trivializationAt F V p).open_baseSet

theorem chart_self_mem_preferredCoordinateAnalysisDomain (p : M) :
    (extChartAt I p) p ∈
      preferredCoordinateAnalysisDomain (I := I) (F := F) (V := V) p := by
  have hpSource : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  constructor
  · exact (extChartAt I p).map_source hpSource
  · change (extChartAt I p).symm ((extChartAt I p) p) ∈
      (trivializationAt F V p).baseSet
    rw [(extChartAt I p).left_inv hpSource]
    exact mem_baseSet_trivializationAt F V p

/-- Image of one compact support piece in its preferred model chart. -/
def coordinatePieces
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) : TopologicalSpace.Compacts E :=
  ⟨extChartAt I (i : M) '' (C.pieces i : Set M),
    (C.pieces i).isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (I := I) (i : M)).mono
        (C.pieces_subset_chartSource i))⟩

@[simp]
theorem coe_coordinatePieces
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.coordinatePieces i : Set E) =
      extChartAt I (i : M) '' (C.pieces i : Set M) :=
  rfl

/-- Every transported support piece lies in the coordinate domain on which
both the inverse chart and bundle coordinates are valid. -/
theorem coordinatePieces_subset_preferredCoordinateAnalysisDomain
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.coordinatePieces i : Set E) ⊆
      preferredCoordinateAnalysisDomain (I := I) (F := F) (V := V) (i : M) := by
  rintro y ⟨x, hx, rfl⟩
  have hxSource : x ∈ (extChartAt I (i : M)).source :=
    C.pieces_subset_chartSource i hx
  constructor
  · exact (extChartAt I (i : M)).map_source hxSource
  · change (extChartAt I (i : M)).symm ((extChartAt I (i : M)) x) ∈
      (trivializationAt F V (i : M)).baseSet
    rw [(extChartAt I (i : M)).left_inv hxSource]
    exact C.pieces_subset_baseSet i hx

/-- The compact coordinate core used for coefficient localization.  The
chart center is adjoined because a subordinate partition function may have
support disjoint from its indexing center (or even be identically zero). -/
def coordinateCore
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) : TopologicalSpace.Compacts E :=
  ⟨(C.coordinatePieces i : Set E) ∪ {(extChartAt I (i : M)) (i : M)},
    (C.coordinatePieces i).isCompact.union isCompact_singleton⟩

@[simp]
theorem coe_coordinateCore
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.coordinateCore i : Set E) =
      (C.coordinatePieces i : Set E) ∪
        {(extChartAt I (i : M)) (i : M)} :=
  rfl

theorem coordinatePieces_subset_coordinateCore
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.coordinatePieces i : Set E) ⊆ (C.coordinateCore i : Set E) :=
  subset_union_left

theorem chart_self_mem_coordinateCore
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (extChartAt I (i : M)) (i : M) ∈ (C.coordinateCore i : Set E) :=
  Set.mem_union_right _ (Set.mem_singleton _)

theorem coordinateCore_subset_preferredCoordinateAnalysisDomain
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.coordinateCore i : Set E) ⊆
      preferredCoordinateAnalysisDomain (I := I) (F := F) (V := V) (i : M) := by
  rw [coe_coordinateCore]
  exact union_subset (C.coordinatePieces_subset_preferredCoordinateAnalysisDomain i)
    (Set.singleton_subset_iff.2
      (chart_self_mem_preferredCoordinateAnalysisDomain
        (I := I) (F := F) (V := V) (i : M)))

/-- The compact supports of the finite partition cover the manifold. -/
theorem iUnion_pieces
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V)) :
    (⋃ i : C.Index, (C.pieces i : Set M)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := C.partition.exists_pos_of_mem (Set.mem_univ x)
  exact Set.mem_iUnion.2 ⟨i, subset_closure (Function.mem_support.2 (ne_of_gt hi))⟩

/-- Canonical compact pairwise overlaps. -/
def overlaps
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i j : C.Index) : TopologicalSpace.Compacts M :=
  compactOverlap C.pieces i j

theorem overlaps_subset
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i j : C.Index) :
    (C.overlaps i j : Set M) ⊆
      (C.pieces i : Set M) ∩ (C.pieces j : Set M) :=
  compactOverlap_subset C.pieces i j

@[simp]
theorem coe_overlaps
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i j : C.Index) :
    (C.overlaps i j : Set M) =
      (C.pieces i : Set M) ∩ (C.pieces j : Set M) :=
  coe_compactOverlap C.pieces i j

/-- Construct a finite smooth preferred trivializing cover from compactness
and the smooth-partition-of-unity theorem for manifolds. -/
theorem exists_finiteSmoothPreferredTrivializingCover :
    Nonempty (FiniteSmoothPreferredTrivializingCover I (F := F) (V := V)) := by
  classical
  let U₀ : M → Set M := fun x =>
    preferredAnalysisDomain I (F := F) (V := V) x
  have hU₀open : ∀ x : M, IsOpen (U₀ x) := fun x =>
    isOpen_preferredAnalysisDomain I (F := F) (V := V) x
  have hU₀cover : Set.univ ⊆ ⋃ x : M, U₀ x := by
    intro x hx
    exact Set.mem_iUnion.2
      ⟨x, mem_preferredAnalysisDomain I (F := F) (V := V) x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U₀ hU₀open hU₀cover
  let U : s → Set M := fun i => U₀ (i : M)
  have hUopen : ∀ i : s, IsOpen (U i) := fun i => hU₀open (i : M)
  have hUcover : Set.univ ⊆ ⋃ i : s, U i := by
    intro x hx
    have hx' : x ∈ ⋃ i ∈ s, U₀ i := hs hx
    simpa [U] using hx'
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    I isClosed_univ U hUopen hUcover
  exact ⟨{ centers := s, partition := ρ, subordinate := hρ }⟩

/-- A canonical noncomputable choice of finite smooth preferred cover. -/
noncomputable def chosen :
    FiniteSmoothPreferredTrivializingCover I (F := F) (V := V) :=
  Classical.choice
    (exists_finiteSmoothPreferredTrivializingCover (I := I) (F := F) (V := V))

end FiniteSmoothPreferredTrivializingCover
end Bundle.Trivialization
end PoincareCurvature
