/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonReconstruction

/-!
# Local geometry of separated piece families

A family of pieces, each carried by an open member of a pairwise ordered disjoint family of open
sets and bounded above by a center inside its own open carrier, is locally a single piece: at a
point of some carrier, that carrier isolates its piece; away from all carriers and from the
closure of the centers, an order interval avoiding the centers meets at most one piece, because a
piece meeting it forces its center inside. This replaces the half-open interval bookkeeping of
ordered interval families and applies to cosets of convex open subgroups at arbitrary
cofinality.
-/

open Set Filter Topology TopologicalSpace

universe u v

public noncomputable section

variable {X : Type u} {ι : Type v}
  [LinearOrder X] [TopologicalSpace X] [OrderTopology X] [NoMinOrder X] [NoMaxOrder X]
  [LinearOrder ι]

omit [TopologicalSpace X] [OrderTopology X] [NoMinOrder X] [NoMaxOrder X] in
/-- An order interval avoiding the centers meets at most one piece of a separated family. -/
theorem subsingleton_pieces_of_Ioo_of_notMem_centers
    (P : ι → Set X) (C : ι → Set X) (x : ι → X)
    (hPC : ∀ i, P i ⊆ C i) (hPx : ∀ i, ∀ p ∈ P i, p ≤ x i) (hxC : ∀ i, x i ∈ C i)
    (hord : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C j, a < b)
    {a b : X} (hab : ∀ y ∈ Ioo a b, y ∉ Set.range x) :
    {i | (P i ∩ Ioo a b).Nonempty}.Subsingleton := by
  intro i hi j hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · obtain ⟨p, hpP, hpa, hpb⟩ := hi
    obtain ⟨q, hqP, hqa, hqb⟩ := hj
    have hpx : p ≤ x i := hPx i p hpP
    have hxq : x i < q := hord i j hij (x i) (hxC i) q (hPC j hqP)
    exact hab (x i) ⟨hpa.trans_le hpx, hxq.trans hqb⟩ ⟨i, rfl⟩
  · obtain ⟨p, hpP, hpa, hpb⟩ := hi
    obtain ⟨q, hqP, hqa, hqb⟩ := hj
    have hqx : q ≤ x j := hPx j q hqP
    have hxp : x j < p := hord j i hji (x j) (hxC j) p (hPC i hpP)
    exact hab (x j) ⟨hqa.trans_le hqx, hxp.trans hpb⟩ ⟨j, rfl⟩

/-- Away from the closure of the centers, the closure of a separated piece union agrees locally
with the closure of a single piece. -/
theorem exists_local_closure_eq_separated_pieces
    (P : ι → Set X) (C : ι → Set X) (x : ι → X)
    (hPC : ∀ i, P i ⊆ C i) (hPx : ∀ i, ∀ p ∈ P i, p ≤ x i) (hxC : ∀ i, x i ∈ C i)
    (hCopen : ∀ i, IsOpen (C i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hord : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C j, a < b)
    {z : X} (hzcenter : z ∉ closure (Set.range x))
    (hz : z ∈ closure (⋃ i, P i)) :
    ∃ i t, IsOpen t ∧ z ∈ t ∧
      closure (⋃ i, P i) ∩ t = closure (P i) ∩ t := by
  classical
  by_cases hzC : ∃ i, z ∈ C i
  · obtain ⟨i, hzi⟩ := hzC
    refine ⟨i, C i, hCopen i, hzi, (hCopen i).closure_congr ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hyC⟩
      rw [Set.mem_iUnion] at hy
      obtain ⟨j, hyj⟩ := hy
      rcases eq_or_ne j i with rfl | hji
      · exact ⟨hyj, hyC⟩
      · exact absurd hyC (Set.disjoint_left.mp (hdisj j i hji) (hPC j hyj))
    · rintro ⟨hyi, hyC⟩
      exact ⟨Set.mem_iUnion_of_mem i hyi, hyC⟩
  · rw [not_exists] at hzC
    have hcompl : (closure (Set.range x))ᶜ ∈ 𝓝 z :=
      isClosed_closure.isOpen_compl.mem_nhds hzcenter
    obtain ⟨a, b, ⟨haz, hzb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hcompl
    have habx : ∀ y ∈ Ioo a b, y ∉ Set.range x := fun y hy hyx ↦
      hab hy (subset_closure hyx)
    have hsub := subsingleton_pieces_of_Ioo_of_notMem_centers P C x hPC hPx hxC hord habx
    obtain ⟨p, hpu, hp⟩ := mem_closure_iff.mp hz (Ioo a b) isOpen_Ioo ⟨haz, hzb⟩
    rw [Set.mem_iUnion] at hp
    obtain ⟨i, hpi⟩ := hp
    have hi : i ∈ {j | (P j ∩ Ioo a b).Nonempty} := ⟨p, hpi, hpu⟩
    refine ⟨i, Ioo a b, isOpen_Ioo, ⟨haz, hzb⟩, isOpen_Ioo.closure_congr ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hyu⟩
      rw [Set.mem_iUnion] at hy
      obtain ⟨j, hyj⟩ := hy
      have hj : j ∈ {k | (P k ∩ Ioo a b).Nonempty} := ⟨y, hyj, hyu⟩
      exact ⟨hsub hj hi ▸ hyj, hyu⟩
    · rintro ⟨hyi, hyu⟩
      exact ⟨Set.mem_iUnion_of_mem i hyi, hyu⟩

/-- When every piece closure stays inside its open carrier, the closure of the union is carried
by the carriers together with the closure of the centers. -/
theorem closure_iUnion_subset_of_closure_piece_subset
    (P : ι → Set X) (C : ι → Set X) (x : ι → X)
    (hPC : ∀ i, P i ⊆ C i) (hPx : ∀ i, ∀ p ∈ P i, p ≤ x i) (hxC : ∀ i, x i ∈ C i)
    (hCopen : ∀ i, IsOpen (C i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hord : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C j, a < b)
    (hclP : ∀ i, closure (P i) ⊆ C i) :
    closure (⋃ i, P i) ⊆ (⋃ i, C i) ∪ closure (Set.range x) := by
  intro z hz
  by_cases hzc : z ∈ closure (Set.range x)
  · exact Or.inr hzc
  · obtain ⟨i, t, -, hzt, heq⟩ :=
      exists_local_closure_eq_separated_pieces P C x hPC hPx hxC hCopen hdisj hord hzc hz
    have hzi : z ∈ closure (P i) := ((Set.ext_iff.mp heq z).mp ⟨hz, hzt⟩).1
    exact Or.inl (Set.mem_iUnion_of_mem i (hclP i hzi))

/-- If a derivative stage of every piece is supported at its center, the same stage of the
separated union is supported on the closure of the centers. -/
theorem cantorBendixson_separated_iUnion_subset_closure_range
    (P : ι → Set X) (C : ι → Set X) (x : ι → X)
    (hPC : ∀ i, P i ⊆ C i) (hPx : ∀ i, ∀ p ∈ P i, p ≤ x i) (hxC : ∀ i, x i ∈ C i)
    (hCopen : ∀ i, IsOpen (C i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hord : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C j, a < b)
    (o : Ordinal.{u})
    (hstage : ∀ i, ((⟨closure (P i), isClosed_closure⟩ : Closeds X).cantorBendixson o :
      Set X) ⊆ {x i}) :
    ((⟨closure (⋃ i, P i), isClosed_closure⟩ : Closeds X).cantorBendixson o : Set X) ⊆
      closure (Set.range x) := by
  intro z hz
  by_contra hzcenter
  have hzunion : z ∈ closure (⋃ i, P i) :=
    (⟨closure (⋃ i, P i), isClosed_closure⟩ : Closeds X).cantorBendixson_le o hz
  obtain ⟨i, t, htopen, hzt, heq⟩ :=
    exists_local_closure_eq_separated_pieces P C x hPC hPx hxC hCopen hdisj hord hzcenter hzunion
  let s : Closeds X := ⟨closure (⋃ i, P i), isClosed_closure⟩
  let q : Closeds X := ⟨closure (P i), isClosed_closure⟩
  have hcongr := TopologicalSpace.Closeds.cantorBendixson_congr_on_open s q htopen heq o
  have hm := (Set.ext_iff.mp hcongr z).mp ⟨hz, hzt⟩
  have hzc : z = x i := Set.mem_singleton_iff.mp (hstage i hm.1)
  exact hzcenter (subset_closure ⟨i, hzc.symm⟩)

omit [NoMinOrder X] [NoMaxOrder X] [LinearOrder ι] in
/-- On its own open carrier, a derivative stage of the separated union agrees with that stage of
the single piece carried there. -/
theorem cantorBendixson_inter_piece_eq
    (P : ι → Set X) (C : ι → Set X)
    (hPC : ∀ i, P i ⊆ C i)
    (hCopen : ∀ i, IsOpen (C i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (i : ι) (o : Ordinal.{u}) :
    ((⟨closure (⋃ j, P j), isClosed_closure⟩ : Closeds X).cantorBendixson o : Set X) ∩ C i =
      ((⟨closure (P i), isClosed_closure⟩ : Closeds X).cantorBendixson o : Set X) ∩ C i := by
  have hinter : (⋃ j, P j) ∩ C i = P i ∩ C i := by
    ext y
    constructor
    · rintro ⟨hy, hyC⟩
      rw [Set.mem_iUnion] at hy
      obtain ⟨j, hyj⟩ := hy
      rcases eq_or_ne j i with rfl | hji
      · exact ⟨hyj, hyC⟩
      · exact absurd hyC (Set.disjoint_left.mp (hdisj j i hji) (hPC j hyj))
    · rintro ⟨hyi, hyC⟩
      exact ⟨Set.mem_iUnion_of_mem i hyi, hyC⟩
  exact TopologicalSpace.Closeds.cantorBendixson_congr_on_open _ _ (hCopen i)
    ((hCopen i).closure_congr hinter) o

/-- If every piece of a separated family has an empty stage, that stage of the union is carried
by the closure of the centers with the centers themselves removed. -/
theorem cantorBendixson_separated_iUnion_subset_of_stage_empty
    (P : ι → Set X) (C : ι → Set X) (x : ι → X)
    (hPC : ∀ i, P i ⊆ C i) (hPx : ∀ i, ∀ p ∈ P i, p ≤ x i) (hxC : ∀ i, x i ∈ C i)
    (hCopen : ∀ i, IsOpen (C i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hord : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C j, a < b)
    (o : Ordinal.{u})
    (hstage : ∀ i, ((⟨closure (P i), isClosed_closure⟩ : Closeds X).cantorBendixson o :
      Set X) = ∅) :
    ((⟨closure (⋃ i, P i), isClosed_closure⟩ : Closeds X).cantorBendixson o : Set X) ⊆
      closure (Set.range x) \ Set.range x := by
  intro z hz
  refine ⟨cantorBendixson_separated_iUnion_subset_closure_range P C x hPC hPx hxC hCopen hdisj
    hord o (fun i ↦ by rw [hstage i]; exact Set.empty_subset _) hz, ?_⟩
  rintro ⟨i, rfl⟩
  have hmem : x i ∈ ((⟨closure (P i), isClosed_closure⟩ : Closeds X).cantorBendixson o :
      Set X) ∩ C i := by
    rw [← cantorBendixson_inter_piece_eq P C hPC hCopen hdisj i o]
    exact ⟨hz, hxC i⟩
  rw [hstage i] at hmem
  exact absurd hmem.1 (Set.notMem_empty _)
