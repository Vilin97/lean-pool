/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Order.WellFoundedSet
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Addition on well-ordered supports

In a complete linearly ordered uniform additive group, addition restricted to two closed
well-ordered subsets is proper and has finite fibers. Closure therefore commutes with their
pointwise sum. Well-ordering here refers to the increasing order on the exponent group.

The proof uses the finite set of minimal elements in a partially well-ordered set: an ultrafilter
containing that set concentrates above one of its minimal elements. If the sums are Cauchy,
nonnegative increments in either coordinate are bounded by increments of the sum. Completeness
then supplies a limit in the closed product. No Archimedean or countable cofinality hypothesis
is used, and no order completion is substituted for the given ambient group.
-/

public section

open Set Filter Topology
open scoped Pointwise

/-- An ultrafilter containing a partially well-ordered set concentrates above one of its points. -/
theorem Set.IsPWO.exists_eventually_le {α : Type*} [PartialOrder α]
    {s : Set α} (hs : s.IsPWO) (𝒰 : Ultrafilter α) (hmem : s ∈ 𝒰) :
    ∃ a ∈ s, ∀ᶠ b in 𝒰, a ≤ b := by
  have hfin : {a | Minimal (· ∈ s) a}.Finite :=
    (setOf_minimal_antichain _).finite_of_partiallyWellOrderedOn
      (hs.mono (setOf_minimal_subset _))
  have he : ∀ᶠ b in 𝒰, ∃ a ∈ {a | Minimal (· ∈ s) a}, a ≤ b := by
    filter_upwards [hmem] with b hb
    obtain ⟨a, hab, ha⟩ := hs.exists_le_minimal hb
    exact ⟨a, ha, hab⟩
  obtain ⟨a, ha, hab⟩ := (Ultrafilter.eventually_exists_mem_iff hfin).mp he
  exact ⟨a, ha.1, hab⟩

private theorem Set.IsPWO.exists_mem_Ioc_of_mem_closure {α : Type*}
    [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hs : s.IsPWO) {x y : α} (hx : x ∈ closure s) (hy : y < x) :
    ∃ b ∈ s, y < b ∧ b ≤ x := by
  by_contra! hn
  have habove : ∀ b ∈ s, y < b → x < b := fun b hb hyb ↦ hn b hb hyb
  let v := s ∩ Ioi x
  have hv : v.IsWF := hs.isWF.mono inter_subset_left
  have hne : v.Nonempty := by
    obtain ⟨b, hby, hbs⟩ := mem_closure_iff_nhds.mp hx (Ioi y) (Ioi_mem_nhds hy)
    exact ⟨b, hbs, habove b hbs hby⟩
  let m := hv.min hne
  have hm : m ∈ v := hv.min_mem hne
  obtain ⟨b, hb, hbs⟩ := mem_closure_iff_nhds.mp hx (Ioo y m) (Ioo_mem_nhds hy hm.2)
  exact (not_lt_of_ge (hv.min_le hne ⟨hbs, habove b hbs hb.1⟩)) hb.2

/-- The ambient closure of a well-ordered subset of a linearly ordered space is well ordered. -/
theorem Set.IsPWO.closure {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] {s : Set α} (hs : s.IsPWO) : (closure s).IsPWO := by
  rw [Set.isPWO_iff_isWF, Set.isWF_iff_no_descending_seq]
  intro f hf hmem
  choose b hbs hb using fun n ↦
    hs.exists_mem_Ioc_of_mem_closure (hmem n) (hf (Nat.lt_succ_self n))
  have hAnti : StrictAnti b := strictAnti_nat_of_succ_lt fun n ↦
    lt_of_le_of_lt (hb (n + 1)).2 (hb n).1
  exact (Set.isWF_iff_no_descending_seq.mp hs.isWF) b hAnti hbs

section OrderedGroup

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] in
/-- A line of fixed sum meets a product of well-ordered sets in finitely many points. -/
theorem Set.IsPWO.finite_add_fiber {s t : Set G} (hs : s.IsPWO) (ht : t.IsPWO) (z : G) :
    {p : G × G | p ∈ s ×ˢ t ∧ p.1 + p.2 = z}.Finite := by
  apply IsAntichain.finite_of_partiallyWellOrderedOn _
    ((hs.prod ht).mono fun _ h ↦ h.1)
  intro p hp q hq hne hpq
  apply hne
  have hfst : p.1 = q.1 := le_antisymm hpq.1 <|
    (add_le_add_iff_right p.2).mp <| calc
      q.1 + p.2 ≤ q.1 + q.2 := add_le_add_right hpq.2 _
      _ = p.1 + p.2 := hq.2.trans hp.2.symm
  exact Prod.ext hfst (add_left_cancel (hfst ▸ hp.2.trans hq.2.symm))

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] in
private theorem abs_sub_lt_of_lower_bound {a x y : G × G} {ε : G}
    (hx : a ≤ x) (hy : a ≤ y)
    (hxs : |(x.1 + x.2) - (a.1 + a.2)| < ε)
    (hys : |(y.1 + y.2) - (a.1 + a.2)| < ε) : |x.1 - y.1| < ε := by
  have hb (z : G × G) (hz : a ≤ z) :
      z.1 - a.1 ≤ (z.1 + z.2) - (a.1 + a.2) := by
    rw [← sub_add_sub_comm]
    exact le_add_of_nonneg_right (sub_nonneg.mpr hz.2)
  apply abs_lt.mpr
  constructor
  · have h : y.1 - x.1 < ε :=
      (sub_le_sub_left hx.1 _).trans_lt ((hb y hy).trans_lt (abs_lt.mp hys).2)
    simpa only [neg_sub] using neg_lt_neg h
  · exact (sub_le_sub_left hy.1 _).trans_lt ((hb x hx).trans_lt (abs_lt.mp hxs).2)

private theorem Ultrafilter.exists_mem_small_coordinates {s t : Set G}
    (hs : s.IsPWO) (ht : t.IsPWO) (𝒰 : Ultrafilter (G × G))
    (hmem : s ×ˢ t ∈ 𝒰)
    (hc : Cauchy (Filter.map (fun p : G × G ↦ p.1 + p.2) (𝒰 : Filter (G × G))))
    {ε : G} (hε : 0 < ε) :
    ∃ v ∈ 𝒰, ∀ x ∈ v, ∀ y ∈ v, |x.1 - y.1| < ε ∧ |x.2 - y.2| < ε := by
  obtain ⟨v, hv, hdiam⟩ :=
    ((nhds_basis_zero_abs_lt G).uniformity_of_nhds_zero_swapped.cauchy_iff.mp hc).2 ε hε
  let w : Set (G × G) := (s ×ˢ t) ∩ {p | p.1 + p.2 ∈ v}
  have hw : w ∈ 𝒰 := inter_mem hmem hv
  obtain ⟨a, ha, hle⟩ := ((hs.prod ht).mono inter_subset_left).exists_eventually_le 𝒰 hw
  refine ⟨w ∩ Ici a, inter_mem hw hle, ?_⟩
  intro x hx y hy
  have hxa : |(x.1 + x.2) - (a.1 + a.2)| < ε := hdiam _ hx.1.2 _ ha.2
  have hya : |(y.1 + y.2) - (a.1 + a.2)| < ε := hdiam _ hy.1.2 _ ha.2
  refine ⟨abs_sub_lt_of_lower_bound hx.2 hy.2 hxa hya, ?_⟩
  exact abs_sub_lt_of_lower_bound (a := a.swap) (x := x.swap) (y := y.swap)
    ⟨hx.2.2, hx.2.1⟩ ⟨hy.2.2, hy.2.1⟩
    (by simpa only [Prod.swap, add_comm] using hxa)
    (by simpa only [Prod.swap, add_comm] using hya)

/-- A Cauchy sum makes an ultrafilter on two well-ordered supports itself Cauchy. -/
theorem Ultrafilter.cauchy_of_add {s t : Set G}
    (hs : s.IsPWO) (ht : t.IsPWO) (𝒰 : Ultrafilter (G × G))
    (hmem : s ×ˢ t ∈ 𝒰)
    (hc : Cauchy (Filter.map (fun p : G × G ↦ p.1 + p.2) (𝒰 : Filter (G × G)))) :
    Cauchy (𝒰 : Filter (G × G)) := by
  rw [cauchy_prod_iff]
  constructor
  · rw [IsUniformAddGroup.cauchy_map_iff_tendsto]
    refine ⟨inferInstance, (nhds_basis_zero_abs_lt G).tendsto_right_iff.mpr ?_⟩
    intro ε hε
    obtain ⟨v, hv, hd⟩ := 𝒰.exists_mem_small_coordinates hs ht hmem hc hε
    exact mem_of_superset (prod_mem_prod hv hv) fun p hp ↦ (hd _ hp.1 _ hp.2).1
  · rw [IsUniformAddGroup.cauchy_map_iff_tendsto]
    refine ⟨inferInstance, (nhds_basis_zero_abs_lt G).tendsto_right_iff.mpr ?_⟩
    intro ε hε
    obtain ⟨v, hv, hd⟩ := 𝒰.exists_mem_small_coordinates hs ht hmem hc hε
    exact mem_of_superset (prod_mem_prod hv hv) fun p hp ↦ (hd _ hp.1 _ hp.2).2

/-- Addition on two closed well-ordered supports is proper in an ordered uniform group that is
Cauchy complete. -/
theorem Set.IsPWO.isProperMap_add [CompleteSpace G] {s t : Set G}
    (hs : s.IsPWO) (ht : t.IsPWO) (hsc : IsClosed s) (htc : IsClosed t) :
    IsProperMap (fun p : s ×ˢ t ↦ p.1.1 + p.1.2) := by
  letI : CompleteSpace (s ×ˢ t) := (hsc.prod htc).isComplete.completeSpace_coe
  refine isProperMap_iff_ultrafilter_of_t2.mpr ⟨by fun_prop, ?_⟩
  intro 𝒰 y hy
  have hc : Cauchy (Filter.map (fun p : G × G ↦ p.1 + p.2)
      (𝒰.map Subtype.val : Filter (G × G))) := by
    simpa only [Ultrafilter.coe_map, Filter.map_map, Function.comp_def] using hy.cauchy_map
  have hm : s ×ˢ t ∈ 𝒰.map Subtype.val := by
    change {p : s ×ˢ t | p.1 ∈ s ×ˢ t} ∈ (𝒰 : Filter (s ×ˢ t))
    exact Filter.Eventually.of_forall fun p ↦ p.2
  have hu := (𝒰.map Subtype.val).cauchy_of_add hs ht hm hc
  have hcU : Cauchy (𝒰 : Filter (s ×ˢ t)) :=
    isUniformEmbedding_subtype_val.isUniformInducing.cauchy_map_iff.mp hu
  exact cauchy_iff_exists_le_nhds.mp hcU

/-- Addition on two closed well-ordered supports is a closed map. -/
theorem Set.IsPWO.isClosedMap_add [CompleteSpace G] {s t : Set G}
    (hs : s.IsPWO) (ht : t.IsPWO) (hsc : IsClosed s) (htc : IsClosed t) :
    IsClosedMap (fun p : s ×ˢ t ↦ p.1.1 + p.1.2) :=
  (hs.isProperMap_add ht hsc htc).isClosedMap

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] in
/-- Every fiber of addition on the subtype of two well-ordered supports is finite. -/
theorem Set.IsPWO.finite_subtype_add_fiber {s t : Set G}
    (hs : s.IsPWO) (ht : t.IsPWO) (z : G) :
    ((fun p : s ×ˢ t ↦ p.1.1 + p.1.2) ⁻¹' {z}).Finite := by
  have hf := (hs.finite_add_fiber ht z).preimage
    (f := (Subtype.val : s ×ˢ t → G × G)) Subtype.val_injective.injOn
  change {p : s ×ˢ t | p.1.1 + p.1.2 = z}.Finite
  simpa only [preimage_setOf_eq, Subtype.coe_prop, true_and] using hf

/-- The sum of two closed well-ordered supports is closed. -/
theorem Set.IsPWO.isClosed_add [CompleteSpace G] {s t : Set G}
    (hs : s.IsPWO) (ht : t.IsPWO) (hsc : IsClosed s) (htc : IsClosed t) :
    IsClosed (s + t) := by
  have he : Set.range (fun p : s ×ˢ t ↦ p.1.1 + p.1.2) = s + t := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact Set.add_mem_add p.2.1 p.2.2
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨⟨(x, y), hx, hy⟩, rfl⟩
  rw [← he]
  exact (hs.isClosedMap_add ht hsc htc).isClosed_range

/-- Closure commutes with addition of well-ordered supports when the ambient ordered uniform group
is Cauchy complete. -/
theorem Set.IsPWO.closure_add_eq [CompleteSpace G] {s t : Set G}
    (hs : s.IsPWO) (ht : t.IsPWO) :
    _root_.closure (s + t) = _root_.closure s + _root_.closure t := by
  apply Subset.antisymm
  · exact closure_minimal (Set.add_subset_add subset_closure subset_closure)
      (hs.closure.isClosed_add ht.closure isClosed_closure isClosed_closure)
  · rw [← Set.image2_add, ← Set.image2_add, ← Set.image_prod, ← Set.image_prod,
      ← closure_prod_eq]
    exact image_closure_subset_closure_image (by fun_prop)

end OrderedGroup
