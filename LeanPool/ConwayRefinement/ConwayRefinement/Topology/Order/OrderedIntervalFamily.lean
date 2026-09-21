/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonReconstruction

/-!
# Local geometry of ordered interval families

A family carried by ordered disjoint half-open intervals is locally a single member away from
the closure of its interval centers.  This remains true for index orders of arbitrary cofinality.
-/

open Set Filter Topology TopologicalSpace

universe u v

public noncomputable section

variable {X : Type u} {ι : Type v}
  [LinearOrder X] [TopologicalSpace X] [OrderTopology X] [NoMinOrder X] [NoMaxOrder X]
  [LinearOrder ι]

/-- Away from the closure of their centers, ordered half-open intervals meet some neighborhood in
at most one member of the family. -/
theorem exists_nhds_subsingleton_ordered_Ioc
    (cut center : ι → X) (hord : ∀ i j, i < j → center i ≤ cut j)
    {x : X} (hx : x ∉ closure (Set.range center)) :
    ∃ t ∈ 𝓝 x, {i | (Ioc (cut i) (center i) ∩ t).Nonempty}.Subsingleton := by
  have hcompl : (closure (Set.range center))ᶜ ∈ 𝓝 x :=
    isClosed_closure.isOpen_compl.mem_nhds hx
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hcompl
  refine ⟨Ioo a b, Ioo_mem_nhds hax hxb, ?_⟩
  intro i hi j hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · obtain ⟨p, ⟨_, hpcenter⟩, ⟨hap, _⟩⟩ := hi
    obtain ⟨q, ⟨hcutq, _⟩, ⟨_, hqb⟩⟩ := hj
    have hc : center i ∈ Ioo a b :=
      ⟨hap.trans_le hpcenter, (hord i j hij).trans_lt hcutq |>.trans hqb⟩
    exact (hab hc) (subset_closure ⟨i, rfl⟩)
  · obtain ⟨p, ⟨hcutp, _⟩, ⟨_, hpb⟩⟩ := hi
    obtain ⟨q, ⟨_, hqcenter⟩, ⟨haq, _⟩⟩ := hj
    have hc : center j ∈ Ioo a b :=
      ⟨haq.trans_le hqcenter, (hord j i hji).trans_lt hcutp |>.trans hpb⟩
    exact (hab hc) (subset_closure ⟨j, rfl⟩)

/-- Away from the closure of the interval centers, the closure of an ordered union agrees locally
with the closure of one member. -/
theorem exists_local_closure_eq_ordered_iUnion
    (f : ι → Set X) (cut center : ι → X)
    (hsupp : ∀ i, f i ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j)
    {x : X} (hxcenter : x ∉ closure (Set.range center))
    (hx : x ∈ closure (⋃ i, f i)) :
    ∃ i t, IsOpen t ∧ x ∈ t ∧
      closure (⋃ i, f i) ∩ t = closure (f i) ∩ t := by
  obtain ⟨t, htx, hsub⟩ := exists_nhds_subsingleton_ordered_Ioc cut center hord hxcenter
  let u := interior t
  have hxu : x ∈ u := mem_interior_iff_mem_nhds.mpr htx
  have huopen : IsOpen u := isOpen_interior
  obtain ⟨p, hpu, hp⟩ := mem_closure_iff.mp hx u huopen hxu
  rw [Set.mem_iUnion] at hp
  obtain ⟨i, hpi⟩ := hp
  have hi : i ∈ {j | (Ioc (cut j) (center j) ∩ t).Nonempty} :=
    ⟨p, hsupp i hpi, interior_subset hpu⟩
  refine ⟨i, u, huopen, hxu, huopen.closure_congr ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyu⟩
    rw [Set.mem_iUnion] at hy
    obtain ⟨j, hyj⟩ := hy
    have hj : j ∈ {k | (Ioc (cut k) (center k) ∩ t).Nonempty} :=
      ⟨y, hsupp j hyj, interior_subset hyu⟩
    exact ⟨hsub hj hi ▸ hyj, hyu⟩
  · rintro ⟨hyi, hyu⟩
    exact ⟨Set.mem_iUnion_of_mem i hyi, hyu⟩

/-- If a derivative stage of every component is supported at its interval center, the
corresponding stage of the ordered union is supported on the closure of those centers. -/
theorem cantorBendixson_ordered_iUnion_subset_closure_range
    (f : ι → Set X) (cut center : ι → X)
    (hsupp : ∀ i, f i ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j) (o : Ordinal.{u})
    (hstage : ∀ i, ((⟨closure (f i), isClosed_closure⟩ : Closeds X).cantorBendixson o :
      Set X) ⊆ {center i}) :
    ((⟨closure (⋃ i, f i), isClosed_closure⟩ : Closeds X).cantorBendixson o : Set X) ⊆
      closure (Set.range center) := by
  intro x hx
  by_contra hxcenter
  have hxunion : x ∈ closure (⋃ i, f i) :=
    (⟨closure (⋃ i, f i), isClosed_closure⟩ : Closeds X).cantorBendixson_le o hx
  obtain ⟨i, t, htopen, hxt, heq⟩ :=
    exists_local_closure_eq_ordered_iUnion f cut center hsupp hord hxcenter hxunion
  let s : Closeds X := ⟨closure (⋃ i, f i), isClosed_closure⟩
  let q : Closeds X := ⟨closure (f i), isClosed_closure⟩
  have hcongr := TopologicalSpace.Closeds.cantorBendixson_congr_on_open
    s q htopen heq o
  have hm := (Set.ext_iff.mp hcongr x).mp ⟨hx, hxt⟩
  have hxc : x = center i := Set.mem_singleton_iff.mp (hstage i hm.1)
  exact hxcenter (subset_closure ⟨i, hxc.symm⟩)
