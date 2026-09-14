/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Geometry.ConvexEnlargement

import Mathlib.Order.Partition.Finpartition

/-!
# Merging overlapping convex holes

This file replaces a countable family of possibly overlapping open holes by a countable
pairwise-disjoint family of larger open convex holes.  The sum of the extended diameters does not
increase.

Convexifying a connected component of the original overlap graph is not sufficient: the convex
hulls can acquire new intersections.  We instead repeatedly merge intersecting convex hulls at
each finite stage and then take the increasing union of every eventual cluster.
-/

@[expose] public section

noncomputable section

open Bornology Set
open scoped ENNReal

namespace LeanPool.Besicovitch

private def clusterUnion (U : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (s : Finset ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i ∈ s, U i

private def clusterHull (U : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (s : Finset ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  openConvexHull (clusterUnion U s)

private theorem isOpen_clusterUnion {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hU : ∀ i, IsOpen (U i))
    (s : Finset ℕ) : IsOpen (clusterUnion U s) := by
  exact isOpen_biUnion fun i _ ↦ hU i

private theorem isOpen_clusterHull (U : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (s : Finset ℕ) :
    IsOpen (clusterHull U s) :=
  isOpen_openConvexHull _

private theorem convex_clusterHull (U : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (s : Finset ℕ) :
    Convex ℝ (clusterHull U s) :=
  convex_openConvexHull _

private theorem clusterUnion_subset_clusterHull {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hU : ∀ i, IsOpen (U i)) (s : Finset ℕ) :
    clusterUnion U s ⊆ clusterHull U s :=
  subset_openConvexHull (isOpen_clusterUnion hU s)

private theorem clusterHull_mono {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {s t : Finset ℕ}
    (hst : s ⊆ t) : clusterHull U s ⊆ clusterHull U t := by
  exact interior_mono (convexHull_mono (by
    intro x hx
    simp only [clusterUnion, mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, hst hi, hxi⟩))

private theorem ediam_clusterHull {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hU : ∀ i, IsOpen (U i))
    (s : Finset ℕ) : Metric.ediam (clusterHull U s) = Metric.ediam (clusterUnion U s) :=
  ediam_openConvexHull (isOpen_clusterUnion hU s)

private theorem isBounded_clusterUnion {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hU : ∀ i, IsBounded (U i)) (s : Finset ℕ) : IsBounded (clusterUnion U s) := by
  exact (isBounded_biUnion_finset s).2 fun i _ ↦ hU i

private theorem isBounded_clusterHull {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hU : ∀ i, IsBounded (U i)) (s : Finset ℕ) : IsBounded (clusterHull U s) := by
  exact (isBounded_convexHull.mpr (isBounded_clusterUnion hU s)).subset interior_subset

private theorem clusterUnion_union (U : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (s t : Finset ℕ) :
    clusterUnion U (s ∪ t) = clusterUnion U s ∪ clusterUnion U t := by
  ext x
  simp only [clusterUnion, mem_iUnion, Finset.mem_union, exists_prop]
  aesop

private theorem ediam_clusterHull_union_le {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i)) {s t : Finset ℕ}
    (hst : (clusterHull U s ∩ clusterHull U t).Nonempty) :
    Metric.ediam (clusterHull U (s ∪ t)) ≤
      Metric.ediam (clusterHull U s) + Metric.ediam (clusterHull U t) := by
  rw [ediam_clusterHull hUopen, clusterUnion_union]
  calc
    Metric.ediam (clusterUnion U s ∪ clusterUnion U t) ≤
        Metric.ediam (clusterHull U s ∪ clusterHull U t) :=
      Metric.ediam_mono (union_subset_union (clusterUnion_subset_clusterHull hUopen s)
        (clusterUnion_subset_clusterHull hUopen t))
    _ ≤ Metric.ediam (clusterHull U s) + Metric.ediam (clusterHull U t) :=
      Metric.ediam_union_le hst

private def GoodPartition (U : ℕ → Set (EuclideanSpace ℝ (Fin 2))) {s : Finset ℕ}
    (P : Finpartition s) : Prop :=
  ∀ t ∈ P.parts, Metric.ediam (clusterHull U t) ≤ ∑ i ∈ t, Metric.ediam (U i)

private def mergePartsFinset {s : Finset ℕ} (P : Finpartition s) (a b : Finset ℕ) :
    Finset (Finset ℕ) :=
  insert (a ∪ b) ((P.parts.erase a).erase b)

private theorem mergeParts_subset {s : Finset ℕ} (P : Finpartition s) {a b t : Finset ℕ}
    (ha : a ∈ P.parts) (hb : b ∈ P.parts) (ht : t ∈ mergePartsFinset P a b) : t ⊆ s := by
  simp only [mergePartsFinset, Finset.mem_insert, Finset.mem_erase] at ht
  rcases ht with rfl | ⟨_, _, ht⟩
  · exact Finset.union_subset (P.subset ha) (P.subset hb)
  · exact P.subset ht

private theorem mergeParts_existsUnique {s : Finset ℕ} (P : Finpartition s) {a b : Finset ℕ}
    (ha : a ∈ P.parts) (hb : b ∈ P.parts) (_hab : a ≠ b) {i : ℕ} (hi : i ∈ s) :
    ∃! t ∈ mergePartsFinset P a b, i ∈ t := by
  obtain ⟨p, ⟨hp, hip⟩, hp_unique⟩ := P.existsUnique_mem hi
  by_cases hpa : p = a
  · subst p
    refine ⟨a ∪ b, ⟨by simp [mergePartsFinset], Finset.mem_union_left _ hip⟩, ?_⟩
    rintro t ⟨ht, hit⟩
    simp only [mergePartsFinset, Finset.mem_insert, Finset.mem_erase] at ht
    rcases ht with rfl | ⟨htb, hta, htP⟩
    · rfl
    · exact (hta (hp_unique t ⟨htP, hit⟩)).elim
  · by_cases hpb : p = b
    · subst p
      refine ⟨a ∪ b, ⟨by simp [mergePartsFinset], Finset.mem_union_right _ hip⟩, ?_⟩
      rintro t ⟨ht, hit⟩
      simp only [mergePartsFinset, Finset.mem_insert, Finset.mem_erase] at ht
      rcases ht with rfl | ⟨htb, _, htP⟩
      · rfl
      · exact (htb (hp_unique t ⟨htP, hit⟩)).elim
    · have hpmerged : p ∈ mergePartsFinset P a b := by
        simp [mergePartsFinset, hp, hpa, hpb]
      refine ⟨p, ⟨hpmerged, hip⟩, ?_⟩
      rintro t ⟨ht, hit⟩
      simp only [mergePartsFinset, Finset.mem_insert, Finset.mem_erase] at ht
      rcases ht with rfl | ⟨_, _, htP⟩
      · rcases Finset.mem_union.mp hit with hia | hib
        · exact (hpa (hp_unique a ⟨ha, hia⟩).symm).elim
        · exact (hpb (hp_unique b ⟨hb, hib⟩).symm).elim
      · exact hp_unique t ⟨htP, hit⟩

private theorem empty_notMem_mergeParts {s : Finset ℕ} (P : Finpartition s)
    {a b : Finset ℕ} (ha : a ∈ P.parts) : ∅ ∉ mergePartsFinset P a b := by
  intro h
  simp only [mergePartsFinset, Finset.mem_insert, Finset.mem_erase] at h
  rcases h with h | ⟨_, _, hP⟩
  · exact P.ne_empty ha (Finset.union_eq_empty.mp h.symm).1
  · exact P.bot_notMem hP

private def mergeParts {s : Finset ℕ} (P : Finpartition s) {a b : Finset ℕ}
    (ha : a ∈ P.parts) (hb : b ∈ P.parts) (hab : a ≠ b) : Finpartition s :=
  Finpartition.ofExistsUnique (mergePartsFinset P a b)
    (fun _ ht ↦ mergeParts_subset P ha hb ht)
    (fun _ hi ↦ mergeParts_existsUnique P ha hb hab hi) (empty_notMem_mergeParts P ha)

private theorem parts_mergeParts {s : Finset ℕ} (P : Finpartition s) {a b : Finset ℕ}
    (ha : a ∈ P.parts) (hb : b ∈ P.parts) (hab : a ≠ b) :
    (mergeParts P ha hb hab).parts = mergePartsFinset P a b :=
  rfl

private theorem le_mergeParts {s : Finset ℕ} (P : Finpartition s) {a b : Finset ℕ}
    (ha : a ∈ P.parts) (hb : b ∈ P.parts) (hab : a ≠ b) :
    P ≤ mergeParts P ha hb hab := by
  intro t ht
  by_cases hta : t = a
  · subst t
    exact ⟨a ∪ b, by simp [parts_mergeParts, mergePartsFinset], Finset.subset_union_left⟩
  · by_cases htb : t = b
    · subst t
      exact ⟨a ∪ b, by simp [parts_mergeParts, mergePartsFinset], Finset.subset_union_right⟩
    · exact ⟨t, by simp [parts_mergeParts, mergePartsFinset, ht, hta, htb], Subset.rfl⟩

private theorem card_mergeParts {s : Finset ℕ} (P : Finpartition s) {a b : Finset ℕ}
    (ha : a ∈ P.parts) (hb : b ∈ P.parts) (hab : a ≠ b) :
    (mergeParts P ha hb hab).parts.card + 1 = P.parts.card := by
  rw [parts_mergeParts, mergePartsFinset]
  have hab_union : a ∪ b ∉ (P.parts.erase a).erase b := by
    intro h
    have huP : a ∪ b ∈ P.parts := (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2
    have haub : a = a ∪ b := by
      apply P.disjoint.eq_of_le ha huP (P.ne_empty ha)
      exact Finset.subset_union_left
    have hbsub : b ⊆ a := by rw [haub]; exact Finset.subset_union_right
    exact hab (P.disjoint.eq_of_le hb ha (P.ne_empty hb) hbsub).symm
  have hcard : 1 < P.parts.card :=
    Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  rw [Finset.card_insert_of_notMem hab_union, Finset.card_erase_of_mem
    (Finset.mem_erase.mpr ⟨hab.symm, hb⟩), Finset.card_erase_of_mem ha]
  omega

private theorem good_mergeParts {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    {s : Finset ℕ} {P : Finpartition s} (hP : GoodPartition U P) {a b : Finset ℕ}
    (ha : a ∈ P.parts) (hb : b ∈ P.parts) (hab : a ≠ b)
    (hinter : (clusterHull U a ∩ clusterHull U b).Nonempty) :
    GoodPartition U (mergeParts P ha hb hab) := by
  intro t ht
  simp only [parts_mergeParts, mergePartsFinset, Finset.mem_insert, Finset.mem_erase] at ht
  rcases ht with rfl | ⟨_, _, htP⟩
  · calc
      Metric.ediam (clusterHull U (a ∪ b)) ≤
          Metric.ediam (clusterHull U a) + Metric.ediam (clusterHull U b) :=
        ediam_clusterHull_union_le hUopen hinter
      _ ≤ (∑ i ∈ a, Metric.ediam (U i)) + ∑ i ∈ b, Metric.ediam (U i) :=
        add_le_add (hP a ha) (hP b hb)
      _ = ∑ i ∈ a ∪ b, Metric.ediam (U i) := by
        have hd : Disjoint a b := by
          change Disjoint (id a) (id b)
          exact P.disjoint ha hb hab
        exact (Finset.sum_union hd).symm
  · exact hP t htP

private def SeparatedPartition (U : ℕ → Set (EuclideanSpace ℝ (Fin 2))) {s : Finset ℕ}
    (P : Finpartition s) : Prop :=
  ∀ a ∈ P.parts, ∀ b ∈ P.parts, a ≠ b → Disjoint (clusterHull U a) (clusterHull U b)

private theorem exists_separated_coarsening {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i)) {s : Finset ℕ} (P : Finpartition s)
    (hP : GoodPartition U P) :
    ∃ Q : Finpartition s, P ≤ Q ∧ GoodPartition U Q ∧ SeparatedPartition U Q := by
  classical
  induction hn : P.parts.card using Nat.strong_induction_on generalizing P with
  | h n ih =>
      by_cases hsep : SeparatedPartition U P
      · exact ⟨P, le_rfl, hP, hsep⟩
      · simp only [SeparatedPartition] at hsep
        push Not at hsep
        obtain ⟨a, ha, b, hb, hab, hinter⟩ := hsep
        have hinter' : (clusterHull U a ∩ clusterHull U b).Nonempty :=
          Set.not_disjoint_iff.mp hinter
        let P' := mergeParts P ha hb hab
        have hcard : P'.parts.card < n := by
          change (mergeParts P ha hb hab).parts.card < n
          rw [← hn]
          have := card_mergeParts P ha hb hab
          omega
        obtain ⟨Q, hP'Q, hQgood, hQsep⟩ :=
          ih P'.parts.card hcard P' (good_mergeParts hUopen hP ha hb hab hinter') rfl
        exact ⟨Q, (le_mergeParts P ha hb hab).trans hP'Q, hQgood, hQsep⟩

private theorem good_extendRange {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    {n : ℕ} (P : Finpartition (Finset.range n)) (hP : GoodPartition U P) :
    GoodPartition U (P.extendOfLE (Finset.range_mono n.le_succ)) := by
  intro t ht
  rcases P.mem_parts_or_eq_sdiff_of_mem_extendOfLE (Finset.range_mono n.le_succ) ht with
    htP | rfl
  · exact hP t htP
  · have hdiff : Finset.range (n + 1) \ Finset.range n = {n} := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [hdiff, ediam_clusterHull hUopen]
    simp [clusterUnion]

private structure HoleStage (U : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (n : ℕ) where
  partition : Finpartition (Finset.range n)
  good : GoodPartition U partition
  separated : SeparatedPartition U partition

private def initialHoleStage (U : ℕ → Set (EuclideanSpace ℝ (Fin 2))) : HoleStage U 0 where
  partition := Finpartition.empty _
  good := by simp [GoodPartition]
  separated := by simp [SeparatedPartition]

private noncomputable def nextHoleStage {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    {n : ℕ} (S : HoleStage U n) : HoleStage U (n + 1) := by
  let P := S.partition.extendOfLE (Finset.range_mono n.le_succ)
  have hP : GoodPartition U P := good_extendRange hUopen S.partition S.good
  let Q := Classical.choose (exists_separated_coarsening hUopen P hP)
  exact {
    partition := Q
    good := (Classical.choose_spec (exists_separated_coarsening hUopen P hP)).2.1
    separated := (Classical.choose_spec (exists_separated_coarsening hUopen P hP)).2.2 }

private theorem extend_le_nextHoleStage {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    {n : ℕ} (S : HoleStage U n) :
    S.partition.extendOfLE (Finset.range_mono n.le_succ) ≤
      (nextHoleStage hUopen S).partition := by
  exact (Classical.choose_spec (exists_separated_coarsening hUopen
    (S.partition.extendOfLE (Finset.range_mono n.le_succ))
    (good_extendRange hUopen S.partition S.good))).1

private noncomputable def holeStages (U : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : ∀ i, IsOpen (U i)) :
    (n : ℕ) → HoleStage U n
  | 0 => initialHoleStage U
  | n + 1 => nextHoleStage hUopen (holeStages U hUopen n)

private theorem stage_part_subset_succ {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    {n i : ℕ} (hi : i < n) :
    (holeStages U hUopen n).partition.part i ⊆
      (holeStages U hUopen (n + 1)).partition.part i := by
  let P := (holeStages U hUopen n).partition
  let Q := (holeStages U hUopen (n + 1)).partition
  have hiP : i ∈ Finset.range n := Finset.mem_range.mpr hi
  have htP : P.part i ∈ P.parts := P.part_mem.mpr hiP
  have htE : P.part i ∈ (P.extendOfLE (Finset.range_mono n.le_succ)).parts :=
    P.parts_subset_extendOfLE (Finset.range_mono n.le_succ) htP
  have hle : P.extendOfLE (Finset.range_mono n.le_succ) ≤ Q := by
    simpa only [Q, P, holeStages] using
      extend_le_nextHoleStage hUopen (holeStages U hUopen n)
  obtain ⟨t, htQ, hsub⟩ := hle htE
  have hit : i ∈ t := hsub (P.mem_part hiP)
  have hpart : Q.part i = t := Q.part_eq_of_mem htQ hit
  rwa [hpart]

private theorem stage_part_mono {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    {n m i : ℕ} (hi : i < n) (hnm : n ≤ m) :
    (holeStages U hUopen n).partition.part i ⊆
      (holeStages U hUopen m).partition.part i := by
  induction m, hnm using Nat.le_induction with
  | base => exact Subset.rfl
  | succ m hnm ih =>
      exact ih.trans (stage_part_subset_succ hUopen (hi.trans_le hnm))

private theorem stage_part_subset_succ_all {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i)) (n i : ℕ) :
    (holeStages U hUopen n).partition.part i ⊆
      (holeStages U hUopen (n + 1)).partition.part i := by
  by_cases hi : i < n
  · exact stage_part_subset_succ hUopen hi
  · have hi' : i ∉ Finset.range n := by simpa only [Finset.mem_range] using hi
    rw [(holeStages U hUopen n).partition.part_eq_empty.mpr hi']
    exact Finset.empty_subset _

private theorem stage_part_mono_all {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    {n m : ℕ} (i : ℕ) (hnm : n ≤ m) :
    (holeStages U hUopen n).partition.part i ⊆
      (holeStages U hUopen m).partition.part i := by
  induction m, hnm using Nat.le_induction with
  | base => exact Subset.rfl
  | succ m _ ih => exact ih.trans (stage_part_subset_succ_all hUopen m i)

private theorem stage_cluster_mono {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    {n m : ℕ} (i : ℕ) (hnm : n ≤ m) :
    clusterHull U ((holeStages U hUopen n).partition.part i) ⊆
      clusterHull U ((holeStages U hUopen m).partition.part i) :=
  clusterHull_mono (stage_part_mono_all hUopen i hnm)

private def mergedHole (U : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : ∀ i, IsOpen (U i)) (i : ℕ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ n, clusterHull U ((holeStages U hUopen n).partition.part i)

private theorem isOpen_mergedHole {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    (i : ℕ) : IsOpen (mergedHole U hUopen i) := by
  exact isOpen_iUnion fun _ ↦ isOpen_clusterHull _ _

private theorem convex_mergedHole {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    (i : ℕ) : Convex ℝ (mergedHole U hUopen i) := by
  apply (monotone_nat_of_le_succ fun n ↦
    stage_cluster_mono hUopen i n.le_succ).directed_le.convex_iUnion
  exact fun _ ↦ convex_clusterHull _ _

private theorem subset_mergedHole {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    (i : ℕ) : U i ⊆ mergedHole U hUopen i := by
  intro x hx
  apply mem_iUnion.mpr
  refine ⟨i + 1, clusterUnion_subset_clusterHull hUopen _ ?_⟩
  simp only [clusterUnion, mem_iUnion]
  exact ⟨i, (holeStages U hUopen (i + 1)).partition.mem_part (by simp), hx⟩

private theorem stage_part_eq_of_inter {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    {n i j : ℕ} (hi : i < n) (hj : j < n)
    (hinter : (clusterHull U ((holeStages U hUopen n).partition.part i) ∩
      clusterHull U ((holeStages U hUopen n).partition.part j)).Nonempty) :
    (holeStages U hUopen n).partition.part i =
      (holeStages U hUopen n).partition.part j := by
  let P := (holeStages U hUopen n).partition
  have hiP : i ∈ Finset.range n := Finset.mem_range.mpr hi
  have hjP : j ∈ Finset.range n := Finset.mem_range.mpr hj
  have hpi : P.part i ∈ P.parts := P.part_mem.mpr hiP
  have hpj : P.part j ∈ P.parts := P.part_mem.mpr hjP
  by_contra hne
  have hd := (holeStages U hUopen n).separated (P.part i) hpi (P.part j) hpj hne
  obtain ⟨x, hxi, hxj⟩ := hinter
  exact Set.disjoint_left.mp hd hxi hxj

private theorem stage_part_eq_mono {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i))
    {n m i j : ℕ} (hi : i < n) (hj : j < n) (hnm : n ≤ m)
    (heq : (holeStages U hUopen n).partition.part i =
      (holeStages U hUopen n).partition.part j) :
    (holeStages U hUopen m).partition.part i =
      (holeStages U hUopen m).partition.part j := by
  let P := (holeStages U hUopen n).partition
  let Q := (holeStages U hUopen m).partition
  have hj_old : j ∈ P.part i := by
    rw [heq]
    exact P.mem_part (Finset.mem_range.mpr hj)
  have hj_new : j ∈ Q.part i := stage_part_mono_all hUopen i hnm hj_old
  have hiQ : i ∈ Finset.range m := Finset.mem_range.mpr (hi.trans_le hnm)
  have hjQ : j ∈ Finset.range m := Finset.mem_range.mpr (hj.trans_le hnm)
  exact ((Q.mem_part_iff_part_eq_part hjQ hiQ).mp hj_new).symm

private theorem mergedHole_eq_of_inter {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i)) {i j : ℕ}
    (hinter : (mergedHole U hUopen i ∩ mergedHole U hUopen j).Nonempty) :
    mergedHole U hUopen i = mergedHole U hUopen j := by
  obtain ⟨x, hxi, hxj⟩ := hinter
  obtain ⟨ni, hxni⟩ := mem_iUnion.mp hxi
  obtain ⟨nj, hxnj⟩ := mem_iUnion.mp hxj
  let N := max (max ni nj) (max (i + 1) (j + 1))
  have hniN : ni ≤ N := by simp [N]
  have hnjN : nj ≤ N := by simp [N]
  have hiN : i < N := by
    have : i + 1 ≤ N := by simp [N]
    omega
  have hjN : j < N := by
    have : j + 1 ≤ N := by simp [N]
    omega
  have hxNi := stage_cluster_mono hUopen i hniN hxni
  have hxNj := stage_cluster_mono hUopen j hnjN hxnj
  have heqN := stage_part_eq_of_inter hUopen hiN hjN ⟨x, hxNi, hxNj⟩
  apply Subset.antisymm
  · intro y hy
    obtain ⟨k, hyk⟩ := mem_iUnion.mp hy
    let M := max k N
    have hkM : k ≤ M := by simp [M]
    have hNM : N ≤ M := by simp [M]
    have heqM := stage_part_eq_mono hUopen hiN hjN hNM heqN
    apply mem_iUnion.mpr
    refine ⟨M, ?_⟩
    have hyM := stage_cluster_mono hUopen i hkM hyk
    rwa [heqM] at hyM
  · intro y hy
    obtain ⟨k, hyk⟩ := mem_iUnion.mp hy
    let M := max k N
    have hkM : k ≤ M := by simp [M]
    have hNM : N ≤ M := by simp [M]
    have heqM := stage_part_eq_mono hUopen hiN hjN hNM heqN
    apply mem_iUnion.mpr
    refine ⟨M, ?_⟩
    have hyM := stage_cluster_mono hUopen j hkM hyk
    rwa [← heqM] at hyM

private theorem mergedHole_eq_of_stage_part_eq {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i)) {n i j : ℕ} (hi : i < n) (hj : j < n)
    (heq : (holeStages U hUopen n).partition.part i =
      (holeStages U hUopen n).partition.part j) :
    mergedHole U hUopen i = mergedHole U hUopen j := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
    let m := max k n
    have hkm : k ≤ m := by simp [m]
    have hnm : n ≤ m := by simp [m]
    have heqm := stage_part_eq_mono hUopen hi hj hnm heq
    apply mem_iUnion.mpr
    refine ⟨m, ?_⟩
    have hxm := stage_cluster_mono hUopen i hkm hxk
    rwa [heqm] at hxm
  · intro x hx
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
    let m := max k n
    have hkm : k ≤ m := by simp [m]
    have hnm : n ≤ m := by simp [m]
    have heqm := stage_part_eq_mono hUopen hi hj hnm heq
    apply mem_iUnion.mpr
    refine ⟨m, ?_⟩
    have hxm := stage_cluster_mono hUopen j hkm hxk
    rwa [← heqm] at hxm

private theorem ediam_mergedHole_le_fiber {U : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hUopen : ∀ i, IsOpen (U i)) (i : ℕ) :
    Metric.ediam (mergedHole U hUopen i) ≤
      ∑' j, if mergedHole U hUopen j = mergedHole U hUopen i
        then Metric.ediam (U j) else 0 := by
  apply Metric.ediam_le
  intro x hx y hy
  obtain ⟨nx, hnx⟩ := mem_iUnion.mp hx
  obtain ⟨ny, hny⟩ := mem_iUnion.mp hy
  let n := max (max nx ny) (i + 1)
  have hnxn : nx ≤ n := by simp [n]
  have hnyn : ny ≤ n := by simp [n]
  have hin : i < n := by
    have : i + 1 ≤ n := by simp [n]
    omega
  let P := (holeStages U hUopen n).partition
  have hpart : P.part i ∈ P.parts := P.part_mem.mpr (Finset.mem_range.mpr hin)
  calc
    edist x y ≤ Metric.ediam (clusterHull U (P.part i)) :=
      Metric.edist_le_ediam_of_mem (stage_cluster_mono hUopen i hnxn hnx)
        (stage_cluster_mono hUopen i hnyn hny)
    _ ≤ ∑ j ∈ P.part i, Metric.ediam (U j) := (holeStages U hUopen n).good _ hpart
    _ = ∑ j ∈ P.part i, if mergedHole U hUopen j = mergedHole U hUopen i
        then Metric.ediam (U j) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp (P.part_subset i hj)
      have heqpart : P.part j = P.part i := (P.mem_part_iff_part_eq_part
        (Finset.mem_range.mpr hjn) (Finset.mem_range.mpr hin)).mp hj
      have heqholes := mergedHole_eq_of_stage_part_eq hUopen hjn hin heqpart
      simp only [heqholes, if_pos]
    _ ≤ ∑' j, if mergedHole U hUopen j = mergedHole U hUopen i
        then Metric.ediam (U j) else 0 := ENNReal.sum_le_tsum _

private theorem tsum_range_ediam_le
    (W : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (d : ℕ → ℝ≥0∞)
    (hW : ∀ i, Metric.ediam (W i) ≤ ∑' j, if W j = W i then d j else 0) :
    (∑' V : Set.range W, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))) ≤
      ∑' i, d i := by
  calc
    _ ≤ ∑' V : Set.range W,
        ∑' j, if W j = (V : Set (EuclideanSpace ℝ (Fin 2))) then d j else 0 := by
      apply ENNReal.tsum_le_tsum
      rintro ⟨V, i, rfl⟩
      exact hW i
    _ = ∑' j, ∑' V : Set.range W,
        if W j = (V : Set (EuclideanSpace ℝ (Fin 2))) then d j else 0 :=
      ENNReal.tsum_comm
    _ = ∑' j, d j := by
      congr 1
      funext j
      let Vj : Set.range W := ⟨W j, mem_range_self j⟩
      rw [tsum_eq_single Vj]
      · simp [Vj]
      · intro V hV
        rw [if_neg]
        intro h
        apply hV
        exact Subtype.ext h.symm

/-- A countable family of open holes with finite total diameter has a pairwise-disjoint
open convex enlargement without any increase in total diameter. -/
theorem exists_pairwiseDisjoint_convex_hole_cover (U : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : ∀ i, IsOpen (U i))
    (hsum : (∑' i, Metric.ediam (U i)) ≠ ∞) :
    ∃ W : Set (Set (EuclideanSpace ℝ (Fin 2))),
      W.Countable ∧ W.PairwiseDisjoint id ∧
        (∀ V : W, IsOpen (V : Set (EuclideanSpace ℝ (Fin 2))) ∧
          Convex ℝ (V : Set (EuclideanSpace ℝ (Fin 2))) ∧
          IsBounded (V : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        (⋃ i, U i) ⊆ ⋃ V : W, (V : Set (EuclideanSpace ℝ (Fin 2))) ∧
        (∑' V : W, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))) ≤
          ∑' i, Metric.ediam (U i) := by
  let Wfun : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := mergedHole U hUopen
  let W : Set (Set (EuclideanSpace ℝ (Fin 2))) := Set.range Wfun
  have hdisjoint : W.PairwiseDisjoint id := by
    rintro V ⟨i, rfl⟩ V' ⟨j, rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hne (mergedHole_eq_of_inter hUopen ⟨x, hxi, hxj⟩)
  have hproperties : ∀ V : W, IsOpen (V : Set (EuclideanSpace ℝ (Fin 2))) ∧
      Convex ℝ (V : Set (EuclideanSpace ℝ (Fin 2))) ∧
      IsBounded (V : Set (EuclideanSpace ℝ (Fin 2))) := by
    rintro ⟨V, i, rfl⟩
    refine ⟨isOpen_mergedHole hUopen i, convex_mergedHole hUopen i, ?_⟩
    apply Metric.isBounded_iff_ediam_ne_top.mpr
    apply ne_top_of_le_ne_top hsum
    calc
      Metric.ediam (mergedHole U hUopen i) ≤
          ∑' j, if mergedHole U hUopen j = mergedHole U hUopen i
            then Metric.ediam (U j) else 0 := ediam_mergedHole_le_fiber hUopen i
      _ ≤ ∑' j, Metric.ediam (U j) := by
        apply ENNReal.tsum_le_tsum
        intro j
        split_ifs <;> simp
  have hcover : (⋃ i, U i) ⊆ ⋃ V : W, (V : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨⟨Wfun i, mem_range_self i⟩, ?_⟩
    exact subset_mergedHole hUopen i hxi
  refine ⟨W, Set.countable_range Wfun, hdisjoint, hproperties, hcover, ?_⟩
  exact tsum_range_ediam_le Wfun (fun i ↦ Metric.ediam (U i))
    (ediam_mergedHole_le_fiber hUopen)

end LeanPool.Besicovitch
