/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Foundation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Compact neighborhoods for local stability

This file packages compact neighborhood hypotheses used by stability arguments.

There are two levels. `CompactRelativeNeighborhood` records the compact
relative neighborhoods used directly in the paper: compact subsets `K ⊆ C`
which are neighborhoods of `x` inside `C`. `CompactLocalization` is stronger:
it adds the convexity and differentiability hypotheses consumed by the smooth
selection lemmas.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
A compact relative neighborhood of `x` inside `C`.

This means that `K` is a compact subset of `C`, `x ∈ K`, and
`K ∈ nhdsWithin x C`. Equivalently, `K` contains the intersection of `C` with
some neighborhood of `x`. No convexity or ambient-interior assumption is
included.
-/
structure CompactRelativeNeighborhood (C : Set (Point n)) (x : Point n)
    (K : Set (Point n)) : Prop where
  subset : K ⊆ C
  mem_nhdsWithin : K ∈ nhdsWithin x C
  point_mem : x ∈ K
  nonempty : K.Nonempty
  isCompact : IsCompact K

namespace CompactRelativeNeighborhood

theorem eventually_mem_nhdsWithin {C K : Set (Point n)} {x : Point n}
    (hK : CompactRelativeNeighborhood C x K)
    {ι : Type*} {xᵢ : ι -> Point n} {l : Filter ι}
    (hx : Tendsto xᵢ l (nhds x)) (hmem : ∀ᶠ i in l, xᵢ i ∈ C) :
    ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C :=
  eventually_mem_nhdsWithin_of_mem_nhdsWithin_of_tendsto
    hK.mem_nhdsWithin hx hmem

theorem nhdsWithin_eq {C K : Set (Point n)} {x : Point n}
    (hK : CompactRelativeNeighborhood C x K) :
    nhdsWithin x K = nhdsWithin x C :=
  nhdsWithin_eq_of_subset_of_mem_nhdsWithin hK.subset hK.mem_nhdsWithin

end CompactRelativeNeighborhood

/--
If `K` is a relative neighborhood of `x` in `C`, then every point of `C` in
some ordinary neighborhood of `x` also has `K` as a relative neighborhood in
`C`.
-/
theorem exists_nhds_forall_mem_nhdsWithin {C K : Set (Point n)} {x : Point n}
    (hK : K ∈ nhdsWithin x C) :
    ∃ U ∈ nhds x, ∀ z : Point n, z ∈ U -> z ∈ C -> K ∈ nhdsWithin z C := by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hK with ⟨U, hU, hUC⟩
  refine ⟨interior U, interior_mem_nhds.2 hU, ?_⟩
  intro z hzU hzC
  have hUnhds : interior U ∈ nhds z := isOpen_interior.mem_nhds hzU
  exact mem_of_superset (inter_mem_nhdsWithin C hUnhds) fun y hy =>
    hUC ⟨interior_subset hy.2, hy.1⟩

/--
Compact localizing data for a point `x` in a domain `C`.

The smooth selected-contact stability lemmas consume exactly these shape
hypotheses for the compact set `K`: compactness, convexity, unique
differentiability, and the condition that all points of `K` lie in the closure
of its interior.
-/
structure CompactLocalization (C : Set (Point n)) (x : Point n)
    (K : Set (Point n)) : Prop where
  subset : K ⊆ C
  mem_nhdsWithin : K ∈ nhdsWithin x C
  point_mem : x ∈ K
  nonempty : K.Nonempty
  isCompact : IsCompact K
  convex : Convex Real K
  uniqueDiffOn : UniqueDiffOn Real K
  subset_closure_interior : K ⊆ closure (interior K)

namespace CompactLocalization

theorem toCompactRelativeNeighborhood {C K : Set (Point n)} {x : Point n}
    (hK : CompactLocalization C x K) :
    CompactRelativeNeighborhood C x K where
  subset := hK.subset
  mem_nhdsWithin := hK.mem_nhdsWithin
  point_mem := hK.point_mem
  nonempty := hK.nonempty
  isCompact := hK.isCompact

theorem eventually_mem_nhdsWithin {C K : Set (Point n)} {x : Point n}
    (hK : CompactLocalization C x K)
    {ι : Type*} {xᵢ : ι -> Point n} {l : Filter ι}
    (hx : Tendsto xᵢ l (nhds x)) (hmem : ∀ᶠ i in l, xᵢ i ∈ C) :
    ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C :=
  eventually_mem_nhdsWithin_of_mem_nhdsWithin_of_tendsto
    hK.mem_nhdsWithin hx hmem

end CompactLocalization

/--
The compact relative neighborhood used in the CIL proof: intersect the domain
with a positive-radius closed ball around the point. Compactness is kept as an
explicit hypothesis, as it is supplied by local compactness in the paper.
-/
theorem compactRelativeNeighborhood_inter_closedBall {C : Set (Point n)}
    {x : Point n} {r : Real} (hxC : x ∈ C) (hr : 0 < r)
    (hcompact : IsCompact (C ∩ Metric.closedBall x r)) :
    CompactRelativeNeighborhood C x (C ∩ Metric.closedBall x r) where
  subset := Set.inter_subset_left
  mem_nhdsWithin := by
    exact Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x hr))
  point_mem := ⟨hxC, Metric.mem_closedBall_self hr.le⟩
  nonempty := ⟨x, ⟨hxC, Metric.mem_closedBall_self hr.le⟩⟩
  isCompact := hcompact

/--
If `C` is locally compact in its relative topology, then around each point of
`C` there is a positive-radius closed ball whose intersection with `C` is
compact.
-/
theorem exists_isCompact_inter_closedBall_of_locallyCompactSpace
    {C : Set (Point n)} [LocallyCompactSpace C] {x : Point n} (hxC : x ∈ C) :
    ∃ r > 0, IsCompact (C ∩ Metric.closedBall x r) := by
  let xC : C := ⟨x, hxC⟩
  rcases LocallyCompactSpace.local_compact_nhds xC Set.univ univ_mem with
    ⟨S, hSnhds, _hSuniv, hScompact⟩
  rcases Metric.mem_nhds_iff.1 hSnhds with ⟨ε, hε, hεS⟩
  let r : Real := ε / 2
  let T : Set C := {y | (y : Point n) ∈ Metric.closedBall x r}
  have hr : 0 < r := half_pos hε
  have hrε : r < ε := half_lt_self hε
  have hTS : T ⊆ S := by
    intro y hy
    apply hεS
    have hydist : dist (y : Point n) x < ε := lt_of_le_of_lt hy hrε
    exact hydist
  have hTclosed : IsClosed T := by
    exact Metric.isClosed_closedBall.preimage continuous_subtype_val
  have hTcompact : IsCompact T := by
    have hST : S ∩ T = T := by
      ext y
      constructor
      · intro hy
        exact hy.2
      · intro hy
        exact ⟨hTS hy, hy⟩
    simpa [hST] using hScompact.inter_right hTclosed
  have himage : IsCompact ((fun y : C => (y : Point n)) '' T) :=
    hTcompact.image continuous_subtype_val
  have himage_eq : ((fun y : C => (y : Point n)) '' T) =
      C ∩ Metric.closedBall x r := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hyC, hyball⟩
      exact ⟨⟨y, hyC⟩, hyball, rfl⟩
  exact ⟨r, hr, by simpa [himage_eq] using himage⟩

/--
If a positive radius gives a compact intersection with a closed ball, then it
gives a compact relative neighborhood.
-/
theorem exists_inter_closedBall_compactRelativeNeighborhood {C : Set (Point n)}
    {x : Point n} (hxC : x ∈ C)
    (h : ∃ r > 0, IsCompact (C ∩ Metric.closedBall x r)) :
    ∃ r > 0, CompactRelativeNeighborhood C x (C ∩ Metric.closedBall x r) := by
  rcases h with ⟨r, hr, hcompact⟩
  exact ⟨r, hr, compactRelativeNeighborhood_inter_closedBall hxC hr hcompact⟩

/--
Local compactness of the relative topology on `C` supplies the compact
relative closed-ball neighborhoods used in the paper.
-/
theorem exists_inter_closedBall_compactRelativeNeighborhood_of_locallyCompactSpace
    {C : Set (Point n)} [LocallyCompactSpace C] {x : Point n} (hxC : x ∈ C) :
    ∃ r > 0, CompactRelativeNeighborhood C x (C ∩ Metric.closedBall x r) :=
  exists_inter_closedBall_compactRelativeNeighborhood hxC
    (exists_isCompact_inter_closedBall_of_locallyCompactSpace hxC)

/--
Given any relative neighborhood `P` of `x` in `C`, local compactness lets us
choose a positive-radius closed-ball relative neighborhood contained in `P`.

The conclusion gives `r > 0`, `K = C ∩ closedBall x r`,
`CompactRelativeNeighborhood C x K`, and `K ⊆ P`. The compactness of `K` is
obtained from local compactness of the relative topology on `C` at `x`.
-/
theorem exists_inter_closedBall_compactRelativeNeighborhood_subset_of_mem_nhdsWithin
    {C P : Set (Point n)} [LocallyCompactSpace C] {x : Point n}
    (hxC : x ∈ C) (hP : P ∈ nhdsWithin x C) :
    ∃ r > 0,
      CompactRelativeNeighborhood C x (C ∩ Metric.closedBall x r) ∧
        C ∩ Metric.closedBall x r ⊆ P := by
  rcases mem_nhdsWithin.1 hP with ⟨U, hUopen, hxU, hUP⟩
  rcases Metric.mem_nhds_iff.1 (hUopen.mem_nhds hxU) with ⟨ε, hε, hεU⟩
  rcases exists_isCompact_inter_closedBall_of_locallyCompactSpace (C := C) hxC with
    ⟨R, hR, hcompactR⟩
  let r : Real := min (R / 2) (ε / 2)
  have hr : 0 < r := lt_min (half_pos hR) (half_pos hε)
  have hrR : r <= R := by
    calc
      r <= R / 2 := min_le_left _ _
      _ <= R := by linarith
  have hrε : r < ε := by
    calc
      r <= ε / 2 := min_le_right _ _
      _ < ε := half_lt_self hε
  have hcompact : IsCompact (C ∩ Metric.closedBall x r) := by
    have hcompact' : IsCompact ((C ∩ Metric.closedBall x R) ∩ Metric.closedBall x r) :=
      hcompactR.inter_right Metric.isClosed_closedBall
    have heq : (C ∩ Metric.closedBall x R) ∩ Metric.closedBall x r =
        C ∩ Metric.closedBall x r := by
      ext y
      constructor
      · rintro ⟨⟨hyC, _hyR⟩, hyr⟩
        exact ⟨hyC, hyr⟩
      · rintro ⟨hyC, hyr⟩
        exact ⟨⟨hyC, Metric.closedBall_subset_closedBall hrR hyr⟩, hyr⟩
    simpa [heq] using hcompact'
  have hrel : CompactRelativeNeighborhood C x (C ∩ Metric.closedBall x r) :=
    compactRelativeNeighborhood_inter_closedBall hxC hr hcompact
  refine ⟨r, hr, hrel, ?_⟩
  intro y hy
  apply hUP
  exact ⟨hεU (Metric.closedBall_subset_ball hrε hy.2), hy.1⟩

theorem compactLocalization_closedBall {C : Set (Point n)} {x : Point n} {r : Real}
    (hr : 0 < r) (hball : Metric.closedBall x r ⊆ C) :
    CompactLocalization C x (Metric.closedBall x r) where
  subset := hball
  mem_nhdsWithin := mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x hr)
  point_mem := Metric.mem_closedBall_self hr.le
  nonempty := ⟨x, Metric.mem_closedBall_self hr.le⟩
  isCompact := ProperSpace.isCompact_closedBall x r
  convex := convex_closedBall x r
  uniqueDiffOn := by
    refine uniqueDiffOn_convex (convex_closedBall x r) ?_
    rw [interior_closedBall x hr.ne']
    exact ⟨x, Metric.mem_ball_self hr⟩
  subset_closure_interior := by
    intro y hy
    simpa [interior_closedBall x hr.ne', closure_ball x hr.ne'] using hy

/--
At an interior point of a domain, a sufficiently small closed ball supplies all
compact localizing hypotheses used by the smooth stability selection lemmas.
-/
theorem exists_closedBall_compactLocalization {C : Set (Point n)} {x : Point n}
    (hC : C ∈ nhds x) :
    ∃ r > 0, CompactLocalization C x (Metric.closedBall x r) := by
  rcases Metric.mem_nhds_iff.1 hC with ⟨ε, hε, hεC⟩
  refine ⟨ε / 2, half_pos hε, compactLocalization_closedBall (half_pos hε) ?_⟩
  exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεC

end ViscositySolns
