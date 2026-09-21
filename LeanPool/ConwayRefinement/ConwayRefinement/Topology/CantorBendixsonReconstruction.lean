/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonRank
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.DiscreteSubset

import Mathlib.Topology.Maps.Basic

/-!
# Local reconstruction of Cantor–Bendixson stages

Transfinite derivatives compose by ordinary ordinal addition and agree locally whenever the
original closed sets agree on an open set. For a closed well-ordered support, the points of
exact rank `a` are dense in its `a`-th derivative. These facts give the reconstruction inequality:
if its rank-`a` points locally belong to another set's `b`-th derivative, then its `(a + c)`-th
stage locally belongs to that set's `(b + c)`-th stage, for every ordinal `c`.

The statements use the given ambient topology and hold at arbitrary ordinal cofinalities.
-/

public noncomputable section

open Set Filter Topology TopologicalSpace

universe u v w

/-- Homeomorphisms preserve every transfinite derivative stage of a closed set. -/
theorem Homeomorph.mem_cantorBendixson_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [T1Space Y]
    (e : X ≃ₜ Y) (s : Closeds X) (t : Closeds Y) (he : e '' (s : Set X) = (t : Set Y))
    (x : X) (o : Ordinal.{v}) :
    e x ∈ (t.cantorBendixson o : Set Y) ↔ x ∈ (s.cantorBendixson o : Set X) := by
  have hf (y : Y) : (e ⁻¹' {y}).Finite := (finite_singleton y).preimage e.injective.injOn
  have hg (x : X) : (e.symm ⁻¹' {x}).Finite :=
    (finite_singleton x).preimage e.symm.injective.injOn
  have ht' : (⟨e '' (s : Set X), e.isClosedMap _ s.isClosed⟩ : Closeds Y) = t :=
    SetLike.coe_injective he
  have he' : e.symm '' (t : Set Y) = (s : Set X) := by
    rw [← he, ← Set.image_comp]
    simp
  have hs' : (⟨e.symm '' (t : Set Y), e.symm.isClosedMap _ t.isClosed⟩ : Closeds X) = s :=
    SetLike.coe_injective he'
  have hst := e.isClosedMap.cantorBendixson_image_subset hf s o
  have hts := e.symm.isClosedMap.cantorBendixson_image_subset hg t o
  rw [ht'] at hst
  rw [hs'] at hts
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hst hx
    exact e.injective hyx ▸ hy
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hts hx
    have hxy : y = e x := by simpa using congrArg e hyx
    exact hxy ▸ hy

namespace TopologicalSpace.Closeds

variable {X : Type u} [TopologicalSpace X] [T1Space X]

/-- Iteration of derivative stages corresponds to ordinary ordinal addition. -/
theorem cantorBendixson_add (s : Closeds X) (a b : Ordinal.{v}) :
    s.cantorBendixson (a + b) = (s.cantorBendixson a).cantorBendixson b := by
  induction b using Ordinal.limitRecOn with
  | zero => simp
  | add_one b ih =>
    rw [← add_assoc, cantorBendixson_add_one, cantorBendixson_add_one, ih]
  | limit b hb ih =>
    rw [cantorBendixson_limit _ _ (Ordinal.isSuccLimit_add a hb),
      cantorBendixson_limit _ _ hb]
    apply le_antisymm
    · apply le_iInf
      intro i
      rw [← ih i.1 i.2]
      exact iInf_le (fun j : Iio (a + b) ↦ s.cantorBendixson j.1)
        ⟨a + i.1, (add_lt_add_iff_left a).mpr i.2⟩
    · apply le_iInf
      intro i
      obtain ⟨j, hj, hij⟩ := (Ordinal.lt_add_iff hb.ne_bot).mp i.2
      exact (iInf_le (fun k : Iio b ↦ (s.cantorBendixson a).cantorBendixson k.1)
        ⟨j, hj⟩).trans
        ((ih j hj) ▸ s.cantorBendixson_antitone hij)

end TopologicalSpace.Closeds

/-- Restricting a set to an open set preserves its derived set inside that open set. -/
theorem IsOpen.derivedSet_inter_eq {X : Type*} [TopologicalSpace X] {U s : Set X}
    (hU : IsOpen U) : derivedSet (s ∩ U) ∩ U = derivedSet s ∩ U := by
  ext x
  constructor
  · rintro ⟨hx, hxU⟩
    exact ⟨derivedSet_mono _ _ inter_subset_left hx, hxU⟩
  · rintro ⟨hx, hxU⟩
    refine ⟨mem_derivedSet.mpr (accPt_iff_frequently.mpr ?_), hxU⟩
    exact ((accPt_iff_frequently.mp (mem_derivedSet.mp hx)).and_eventually
      (hU.mem_nhds hxU)).mono fun y hy ↦ ⟨hy.1.1, hy.1.2, hy.2⟩

/-- Sets agreeing on an open set have closures agreeing there. -/
theorem IsOpen.closure_congr {X : Type*} [TopologicalSpace X] {U s t : Set X}
    (hU : IsOpen U) (hst : s ∩ U = t ∩ U) : closure s ∩ U = closure t ∩ U := by
  ext x
  constructor
  · intro hx
    have hm := hU.closure_inter hx
    rw [hst] at hm
    exact ⟨closure_mono inter_subset_left hm, hx.2⟩
  · intro hx
    have hm := hU.closure_inter hx
    rw [← hst] at hm
    exact ⟨closure_mono inter_subset_left hm, hx.2⟩

/-- Sets agreeing on an open set have derived sets agreeing there. -/
theorem IsOpen.derivedSet_congr {X : Type*} [TopologicalSpace X] {U s t : Set X}
    (hU : IsOpen U) (hst : s ∩ U = t ∩ U) : derivedSet s ∩ U = derivedSet t ∩ U := by
  rw [← hU.derivedSet_inter_eq (s := s), hst, hU.derivedSet_inter_eq]

namespace TopologicalSpace.Closeds

variable {X : Type u} [TopologicalSpace X] [T1Space X]

/-- Closed sets agreeing on an open set have every derivative stage agreeing there. -/
theorem cantorBendixson_congr_on_open (s t : Closeds X) {U : Set X} (hU : IsOpen U)
    (hst : (s : Set X) ∩ U = (t : Set X) ∩ U) (o : Ordinal.{v}) :
    (s.cantorBendixson o : Set X) ∩ U = (t.cantorBendixson o : Set X) ∩ U := by
  induction o using Ordinal.limitRecOn with
  | zero => simpa using hst
  | add_one o ih =>
    simpa only [cantorBendixson_add_one, coe_derived] using hU.derivedSet_congr ih
  | limit o ho ih =>
    rw [cantorBendixson_limit _ _ ho, cantorBendixson_limit _ _ ho]
    ext x
    constructor
    · rintro ⟨hx, hxU⟩
      refine ⟨Closeds.mem_iInf.mpr (fun i ↦ ?_), hxU⟩
      exact ((Set.ext_iff.mp (ih i.1 i.2) x).mp
        ⟨Closeds.mem_iInf.mp hx i, hxU⟩).1
    · rintro ⟨hx, hxU⟩
      refine ⟨Closeds.mem_iInf.mpr (fun i ↦ ?_), hxU⟩
      exact ((Set.ext_iff.mp (ih i.1 i.2) x).mpr
        ⟨Closeds.mem_iInf.mp hx i, hxU⟩).1

/-- Local inclusion of closed sets implies local inclusion at every derivative stage. -/
theorem cantorBendixson_mono_on_open (s t : Closeds X) {U : Set X} (hU : IsOpen U)
    (hst : (s : Set X) ∩ U ⊆ (t : Set X)) (o : Ordinal.{v}) :
    (s.cantorBendixson o : Set X) ∩ U ⊆ (t.cantorBendixson o : Set X) := by
  have he : (s : Set X) ∩ U = ((s ⊓ t : Closeds X) : Set X) ∩ U := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨hx.1, hst hx⟩, hx.2⟩
    · rintro ⟨⟨hx, _⟩, hxU⟩
      exact ⟨hx, hxU⟩
  intro x hx
  have hx' := (Set.ext_iff.mp (s.cantorBendixson_congr_on_open (s ⊓ t) hU he o) x).mp hx
  exact cantorBendixson_mono inf_le_right o hx'.1

variable [LinearOrder X] [OrderTopology X]

/-- Point rank depends only on the closed set in a neighborhood of the point. -/
theorem cantorBendixsonRank_congr_on_open (s t : Closeds X)
    (hs : (s : Set X).IsPWO) (ht : (t : Set X).IsPWO)
    {U : Set X} (hU : IsOpen U) (hst : (s : Set X) ∩ U = (t : Set X) ∩ U)
    {x : X} (hx : x ∈ U) : s.cantorBendixsonRank hs x = t.cantorBendixsonRank ht x := by
  apply le_antisymm
  · apply s.cantorBendixsonRank_le_of_notMem hs x
    intro hm
    have he := s.cantorBendixson_congr_on_open t hU hst (t.cantorBendixsonRank ht x + 1)
    exact t.notMem_cantorBendixson_rank_add_one ht x ((Set.ext_iff.mp he x).mp ⟨hm, hx⟩).1
  · apply t.cantorBendixsonRank_le_of_notMem ht x
    intro hm
    have he := s.cantorBendixson_congr_on_open t hU hst (s.cantorBendixsonRank hs x + 1)
    exact s.notMem_cantorBendixson_rank_add_one hs x ((Set.ext_iff.mp he x).mpr ⟨hm, hx⟩).1

omit [T1Space X] in
/-- The isolated points of a closed well-ordered support are dense in that support. -/
theorem closure_isolated_eq (s : Closeds X) (hs : (s : Set X).IsPWO) :
    closure {x | x ∈ s ∧ x ∉ derivedSet (s : Set X)} = (s : Set X) := by
  apply Subset.antisymm (closure_minimal (fun _ h ↦ h.1) s.isClosed)
  intro x hx
  apply mem_closure_iff.mpr
  intro U hU hxU
  let v : Set X := (s : Set X) ∩ U
  have hv : v.IsWF := hs.isWF.mono inter_subset_left
  have hn : v.Nonempty := ⟨x, hx, hxU⟩
  let m := hv.min hn
  have hm : m ∈ v := hv.min_mem hn
  refine ⟨m, hm.2, hm.1, ?_⟩
  rw [mem_derivedSet, accPt_iff_frequently, Filter.not_frequently]
  filter_upwards [hs.eventually_le m, hU.mem_nhds hm.2] with y hy hyU hn
  exact hn.1 ((hy hn.2).antisymm (hv.min_le ‹v.Nonempty› ⟨hn.2, hyU⟩))

/-- The exact rank-`o` points are dense in the `o`-th derivative of a well-ordered support. -/
theorem closure_rank_level_eq (s : Closeds X) (hs : (s : Set X).IsPWO) (o : Ordinal.{u}) :
    closure {x | x ∈ s ∧ s.cantorBendixsonRank hs x = o} =
      (s.cantorBendixson o : Set X) := by
  have hd := (s.cantorBendixson o).closure_isolated_eq (hs.mono (s.cantorBendixson_le o))
  have he : {x | x ∈ s ∧ s.cantorBendixsonRank hs x = o} =
      {x | x ∈ (s.cantorBendixson o : Set X) ∧
        x ∉ derivedSet (s.cantorBendixson o : Set X)} := by
    ext x
    constructor
    · rintro ⟨hx, hr⟩
      have hh := (s.cantorBendixsonRank_eq_iff hs hx o).mp hr
      simpa only [cantorBendixson_add_one, coe_derived, mem_setOf_eq] using hh
    · intro hh
      have hx := s.cantorBendixson_le o hh.1
      refine ⟨hx, (s.cantorBendixsonRank_eq_iff hs hx o).mpr ?_⟩
      simpa only [cantorBendixson_add_one, coe_derived, mem_setOf_eq] using hh
  rw [he]
  exact hd

/-- Local inclusion of exact-rank points lifts to all further derivative stages. -/
theorem cantorBendixson_reconstruction (s t : Closeds X) (hs : (s : Set X).IsPWO)
    {U : Set X} (hU : IsOpen U) (a b c : Ordinal.{u})
    (hlevel : ∀ y ∈ U, y ∈ s → s.cantorBendixsonRank hs y = a →
      y ∈ (t.cantorBendixson b : Set X)) :
    (s.cantorBendixson (a + c) : Set X) ∩ U ⊆
      (t.cantorBendixson (b + c) : Set X) := by
  have hlocal : (s.cantorBendixson a : Set X) ∩ U ⊆ (t.cantorBendixson b : Set X) := by
    intro x hx
    have hl : x ∈ closure {y | y ∈ s ∧ s.cantorBendixsonRank hs y = a} := by
      rw [s.closure_rank_level_eq hs a]
      exact hx.1
    have hf := (mem_closure_iff_frequently.mp hl).and_eventually (hU.mem_nhds hx.2)
    exact (t.cantorBendixson b).isClosed.closure_subset
      (mem_closure_iff_frequently.mpr (hf.mono fun y hy ↦ hlevel y hy.2 hy.1.1 hy.1.2))
  simpa only [cantorBendixson_add] using
    (s.cantorBendixson a).cantorBendixson_mono_on_open (t.cantorBendixson b) hU hlocal c

/-- If every local exact-rank point of `s` survives to the same stage of `t`, then absence from
the next two stages of `t` bounds the rank in `s` by one successor. -/
theorem cantorBendixsonRank_le_add_one_of_rankLevel_mapsTo_stage
    (s t : Closeds X) (hs : (s : Set X).IsPWO) {U : Set X} (hU : IsOpen U)
    {x : X} (hxU : x ∈ U) (a b : Ordinal.{u})
    (hlevel : ∀ y ∈ U, y ∈ s → s.cantorBendixsonRank hs y = a →
      y ∈ (t.cantorBendixson b : Set X))
    (ht : x ∉ (t.cantorBendixson ((b + 1) + 1) : Set X)) :
    s.cantorBendixsonRank hs x ≤ a + 1 := by
  apply s.cantorBendixsonRank_le_of_notMem hs x
  intro hx
  have hrec := s.cantorBendixson_reconstruction t hs hU a b (1 + 1) hlevel
  apply ht
  have hm := hrec ⟨by simpa only [add_assoc] using hx, hxU⟩
  simpa only [add_assoc] using hm

/-- If every local exact-rank point of `s` survives to the same stage of `t`, then absence from
the next two stages of `t` bounds the rank in `s` by one successor. -/
theorem cantorBendixsonRank_le_add_one_of_rankLevel_mapsTo
    (s t : Closeds X) (hs : (s : Set X).IsPWO) {U : Set X} (hU : IsOpen U)
    {x : X} (hxU : x ∈ U) (a : Ordinal.{u})
    (hlevel : ∀ y ∈ U, y ∈ s → s.cantorBendixsonRank hs y = a →
      y ∈ (t.cantorBendixson a : Set X))
    (ht : x ∉ (t.cantorBendixson ((a + 1) + 1) : Set X)) :
    s.cantorBendixsonRank hs x ≤ a + 1 := by
  exact s.cantorBendixsonRank_le_add_one_of_rankLevel_mapsTo_stage
    t hs hU hxU a a hlevel ht

/-- The points of one exact Cantor--Bendixson rank in a closed partially well-ordered set form a
discrete subset. -/
theorem rankLevel_isDiscrete (s : Closeds X) (hs : (s : Set X).IsPWO) (o : Ordinal.{u}) :
    IsDiscrete {x | x ∈ s ∧ s.cantorBendixsonRank hs x = o} := by
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  have hr := (s.cantorBendixsonRank_eq_iff hs hx.1 o).mp hx.2
  have hn : ¬AccPt x (𝓟 (s.cantorBendixson o : Set X)) := by
    simpa only [cantorBendixson_add_one, coe_derived, mem_derivedSet] using hr.2
  rw [AccPt, not_neBot] at hn
  apply le_antisymm
  · calc
      𝓝[≠] x ⊓ 𝓟 {y | y ∈ s ∧ s.cantorBendixsonRank hs y = o} ≤
          𝓝[≠] x ⊓ 𝓟 (s.cantorBendixson o : Set X) :=
        inf_le_inf_left _ (Filter.principal_mono.mpr fun y hy ↦
          (s.mem_cantorBendixson_iff hs y o).mpr ⟨hy.1, hy.2.ge⟩)
      _ = ⊥ := hn
  · exact bot_le

omit [T1Space X] in
/-- The subtype of one exact rank level inherits partial well-ordering from the closed support. -/
theorem rankLevel_univ_isPWO (s : Closeds X) (hs : (s : Set X).IsPWO)
    (o : Ordinal.{u}) :
    (Set.univ : Set {x // x ∈ s ∧ s.cantorBendixsonRank hs x = o}).IsPWO := by
  rw [Set.isPWO_iff_exists_monotone_subseq]
  intro f _
  obtain ⟨g, hg⟩ := hs.exists_monotone_subseq fun n ↦ (f n).property.1
  refine ⟨g, fun a b hab ↦ ?_⟩
  exact Subtype.coe_le_coe.mp (hg hab)

variable [NoMinOrder X]

omit [LinearOrder X] [OrderTopology X] [NoMinOrder X] [T1Space X] in
/-- **A union of two discrete sets is discrete when neither accumulates at the other.** At a point
of one of them, that set's own witness handles it; the other either contains the point, and
supplies its own witness, or stays away from it, leaving room to shrink into.

Staying away is the hypothesis, in the form each application actually has: it holds when the sets
are closed, and equally when they are only relatively closed on an open set containing both. -/
theorem isDiscrete_union {L M : Set X} (hL : IsDiscrete L) (hM : IsDiscrete M)
    (hLM : ∀ x ∈ M, x ∉ L → Lᶜ ∈ 𝓝 x) (hML : ∀ x ∈ L, x ∉ M → Mᶜ ∈ 𝓝 x) :
    IsDiscrete (L ∪ M) := by
  rw [isDiscrete_iff_nhdsNE] at hL hM ⊢
  have haway : ∀ {S : Set X} {y : X}, Sᶜ ∈ 𝓝 y → 𝓝[≠] y ⊓ 𝓟 S = ⊥ := by
    intro S y hy
    refine le_bot_iff.mp (le_trans (inf_le_inf_right _ nhdsWithin_le_nhds) ?_)
    rw [le_bot_iff, Filter.inf_principal_eq_bot]
    exact hy
  intro x hx
  rw [← Filter.sup_principal, inf_sup_left]
  rcases hx with hx | hx
  · rw [hL x hx, bot_sup_eq]
    by_cases hxM : x ∈ M
    · exact hM x hxM
    · exact haway (hML x hx hxM)
  · rw [hM x hx, sup_bot_eq]
    by_cases hxL : x ∈ L
    · exact hL x hxL
    · exact haway (hLM x hx hxL)

omit [LinearOrder X] [OrderTopology X] [NoMinOrder X] [T1Space X] in
/-- **A finite union of discrete sets is discrete when none accumulates at another's points.** -/
theorem isDiscrete_biUnion {ι' : Type*} (s : Finset ι') (L : ι' → Set X)
    (hL : ∀ i ∈ s, IsDiscrete (L i))
    (haway : ∀ i ∈ s, ∀ j ∈ s, ∀ x ∈ L j, x ∉ L i → (L i)ᶜ ∈ 𝓝 x) :
    IsDiscrete (⋃ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    rw [isDiscrete_iff_nhdsNE]
    simp
  | insert c s hc ih =>
    have hLs : ∀ i ∈ s, IsDiscrete (L i) := fun i hi ↦ hL i (Finset.mem_insert_of_mem hi)
    have hawayS : ∀ i ∈ s, ∀ j ∈ s, ∀ x ∈ L j, x ∉ L i → (L i)ᶜ ∈ 𝓝 x :=
      fun i hi j hj ↦ haway i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hrest := ih hLs hawayS
    rw [Finset.set_biUnion_insert]
    refine isDiscrete_union (hL c (Finset.mem_insert_self c s)) hrest ?_ ?_
    · intro x hx hxc
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨j, hj, hxj⟩ := hx
      exact haway c (Finset.mem_insert_self c s) j (Finset.mem_insert_of_mem hj) x hxj hxc
    · intro x hx hxrest
      have hcompl : (⋃ i ∈ s, L i)ᶜ = ⋂ i ∈ s, (L i)ᶜ := by
        simp only [Set.compl_iUnion]
      rw [hcompl]
      refine (Filter.biInter_finset_mem s).mpr fun i hi ↦ ?_
      refine haway i (Finset.mem_insert_of_mem hi) c (Finset.mem_insert_self c s) x hx ?_
      intro hxi
      exact hxrest (Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩)

omit [T1Space X] in
/-- **Ordered disjoint left cuts for a discrete set.** Each point of a discrete set in a linear
order has an interval below it meeting the set only at that point, and those intervals may be taken
so that a smaller point never reaches into a larger point's interval. -/
theorem exists_leftCuts_of_isDiscrete (L : Set X) (hL : IsDiscrete L) :
    ∃ z : ↥L → X, (∀ x : ↥L, z x < (x : X)) ∧
      (∀ x : ↥L, Ioc (z x) (x : X) ∩ L = {(x : X)}) ∧
      ∀ x y : ↥L, (x : X) < (y : X) → (x : X) ≤ z y := by
  have hcuts : ∀ x : ↥L, ∃ z < (x : X), Ioc z (x : X) ∩ L = {(x : X)} := by
    intro x
    obtain ⟨U, hUn, hUint⟩ := nhds_inter_eq_singleton_of_mem_discrete hL x.property
    obtain ⟨z, hzx, hzU⟩ := exists_Ioc_subset_of_mem_nhds hUn (exists_lt (x : X))
    refine ⟨z, hzx, Set.Subset.antisymm ?_ ?_⟩
    · intro y hy
      rw [← hUint]
      exact ⟨hzU hy.1, hy.2⟩
    · intro y hy
      rw [mem_singleton_iff] at hy
      subst y
      exact ⟨⟨hzx, le_rfl⟩, x.property⟩
  choose z hzlt hzlevel using hcuts
  refine ⟨z, hzlt, hzlevel, fun x y hxy ↦ ?_⟩
  by_contra hle
  have hxmem : (x : X) ∈ Ioc (z y) (y : X) ∩ L := ⟨⟨lt_of_not_ge hle, hxy.le⟩, x.property⟩
  rw [hzlevel y, mem_singleton_iff] at hxmem
  exact hxy.ne hxmem

/-- Exact-rank points admit left neighborhoods that are ordered by their centers. This is the
arbitrary-cofinality replacement for choosing successive disjoint intervals along a sequence. -/
theorem exists_rankLevel_leftCuts (s : Closeds X) (hs : (s : Set X).IsPWO)
    (o : Ordinal.{u}) :
    ∃ z : {x // x ∈ s ∧ s.cantorBendixsonRank hs x = o} → X,
      (∀ x, z x < x) ∧
      (∀ x, Ioc (z x) x ∩ {y | y ∈ s ∧ s.cantorBendixsonRank hs y = o} =
        {(x : X)}) ∧
      ∀ x y : {x // x ∈ s ∧ s.cantorBendixsonRank hs x = o},
        (x : X) < y → (x : X) ≤ z y := by
  let level : Set X := {x | x ∈ s ∧ s.cantorBendixsonRank hs x = o}
  have hdisc : IsDiscrete level := s.rankLevel_isDiscrete hs o
  have hcuts : ∀ x : level, ∃ z < (x : X), Ioc z x ∩ level = {(x : X)} := by
    intro x
    obtain ⟨U, hUn, hUint⟩ := nhds_inter_eq_singleton_of_mem_discrete hdisc x.property
    obtain ⟨z, hzx, hzU⟩ := exists_Ioc_subset_of_mem_nhds hUn (exists_lt (x : X))
    refine ⟨z, hzx, Set.Subset.antisymm ?_ ?_⟩
    · intro y hy
      rw [← hUint]
      exact ⟨hzU hy.1, hy.2⟩
    · intro y hy
      rw [mem_singleton_iff] at hy
      subst y
      exact ⟨⟨hzx, le_rfl⟩, x.property⟩
  choose z hzlt hzlevel using hcuts
  refine ⟨z, hzlt, hzlevel, fun x y hxy ↦ ?_⟩
  by_contra hle
  have hxmem : (x : X) ∈ Ioc (z y) y ∩ level :=
    ⟨⟨lt_of_not_ge hle, hxy.le⟩, x.property⟩
  rw [hzlevel y, mem_singleton_iff] at hxmem
  exact hxy.ne hxmem

end TopologicalSpace.Closeds

/-- Homeomorphisms carrying one closed well-ordered support onto another preserve point ranks. -/
theorem Homeomorph.cantorBendixsonRank_eq {X Y : Type u}
    [LinearOrder X] [LinearOrder Y] [TopologicalSpace X] [TopologicalSpace Y]
    [OrderTopology X] [OrderTopology Y] (e : X ≃ₜ Y)
    (s : Closeds X) (t : Closeds Y) (hs : (s : Set X).IsPWO) (ht : (t : Set Y).IsPWO)
    (he : e '' (s : Set X) = (t : Set Y)) (x : X) :
    t.cantorBendixsonRank ht (e x) = s.cantorBendixsonRank hs x := by
  apply le_antisymm
  · apply t.cantorBendixsonRank_le_of_notMem ht (e x)
    intro hx
    exact s.notMem_cantorBendixson_rank_add_one hs x
      ((e.mem_cantorBendixson_iff s t he x _).mp hx)
  · apply s.cantorBendixsonRank_le_of_notMem hs x
    intro hx
    exact t.notMem_cantorBendixson_rank_add_one ht (e x)
      ((e.mem_cantorBendixson_iff s t he x _).mpr hx)

namespace Topology.IsClosedEmbedding

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [T1Space X] [T1Space Y] {f : X → Y}

/-- A closed embedding carries every Cantor–Bendixson derivative onto the corresponding
derivative of its closed image. -/
theorem image_cantorBendixson_eq (hf : IsClosedEmbedding f) (s : Closeds X)
    (o : Ordinal.{w}) :
    f '' (s.cantorBendixson o : Set X) =
      ((⟨f '' (s : Set X), hf.isClosedMap _ s.isClosed⟩ : Closeds Y).cantorBendixson o :
        Set Y) := by
  apply Set.Subset.antisymm
  · induction o using Ordinal.limitRecOn with
    | zero => simp
    | add_one o ih =>
      simp only [Closeds.cantorBendixson_add_one, Closeds.coe_derived]
      exact (hf.continuous.image_derivedSet hf.injective).trans
        (derivedSet_mono _ _ ih)
    | limit o ho ih =>
      rw [Closeds.cantorBendixson_limit _ _ ho,
        Closeds.cantorBendixson_limit _ _ ho]
      rintro _ ⟨x, hx, rfl⟩
      apply Closeds.mem_iInf.mpr
      intro i
      exact ih i.1 i.2 ⟨x, Closeds.mem_iInf.mp hx i, rfl⟩
  · exact hf.isClosedMap.cantorBendixson_image_subset
      (fun y ↦ (Set.finite_singleton y).preimage hf.injective.injOn) s o

end Topology.IsClosedEmbedding

namespace Topology.IsOpenEmbedding

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [T1Space X] [T1Space Y] {f : X → Y}

omit [T1Space X] [T1Space Y] in
private theorem image_derivedSet_eq_inter_range (hf : IsOpenEmbedding f) (s : Set X) :
    f '' derivedSet s = derivedSet (f '' s) ∩ range f := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨hf.continuous.image_derivedSet hf.injective ⟨x, hx, rfl⟩,
      mem_range_self x⟩
  · rintro y ⟨hy, x, rfl⟩
    refine ⟨x, mem_derivedSet.mpr ?_, rfl⟩
    have hy' : AccPt (f x) (Filter.principal (f '' s)) := mem_derivedSet.mp hy
    rw [← hf.accPt_comap_iff] at hy'
    simpa only [comap_principal, preimage_image_eq _ hf.injective] using hy'

/-- Derivatives in an open subspace are the ambient derivatives restricted to that subspace. -/
theorem image_cantorBendixson_top_eq (hf : IsOpenEmbedding f) (o : Ordinal.{w}) :
    f '' (((⊤ : Closeds X).cantorBendixson o : Set X)) =
      ((⊤ : Closeds Y).cantorBendixson o : Set Y) ∩ range f := by
  induction o using Ordinal.limitRecOn with
  | zero => simp
  | add_one o ih =>
      simp only [Closeds.cantorBendixson_add_one, Closeds.coe_derived]
      rw [hf.image_derivedSet_eq_inter_range, ih]
      exact hf.isOpen_range.derivedSet_inter_eq
  | limit o ho ih =>
      rw [Closeds.cantorBendixson_limit _ _ ho,
        Closeds.cantorBendixson_limit _ _ ho]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨Closeds.mem_iInf.mpr fun i ↦ ?_, mem_range_self x⟩
        exact (Set.ext_iff.mp (ih i.1 i.2) (f x)).mp
          ⟨x, Closeds.mem_iInf.mp hx i, rfl⟩ |>.1
      · rintro ⟨hy, x, rfl⟩
        refine ⟨x, Closeds.mem_iInf.mpr fun i ↦ ?_, rfl⟩
        have hi := (Set.ext_iff.mp (ih i.1 i.2) (f x)).mpr
          ⟨Closeds.mem_iInf.mp hy i, mem_range_self x⟩
        obtain ⟨z, hz, hzx⟩ := hi
        exact hf.injective hzx ▸ hz

end Topology.IsOpenEmbedding
