/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import LeanPool.FrontierMathOpenHypergraphs.Basic

/-!
# Support gadgets and the substitution theorem
-/

open Finset

namespace HypergraphLowerBound

/-! ## Support patterns and frames -/

/-- A support pattern on `[t]` is a subset of `Fin t` of size at least `2`. -/
def SupportPattern (t : ℕ) := { S : Finset (Fin t) // 2 ≤ S.card }

/-- The block hypergraphs used in a substitution construction. -/
abbrev BlockFamily (t : ℕ) := HypergraphFamily (Fin t) ℕ

/-- An occurrence of a support pattern in a support multiset. -/
abbrev SupportOcc {t : ℕ} (F : Multiset (SupportPattern t)) := Fin F.card

/-- The support pattern attached to a given support-vertex occurrence. -/
noncomputable def supportPatternAt {t : ℕ}
    (F : Multiset (SupportPattern t)) (s : SupportOcc F) : SupportPattern t :=
  F.toList.get ⟨s.1, by
    rw [Multiset.length_toList]
    exact s.2
  ⟩

/-- The underlying subset of `[t]` attached to a support occurrence. -/
noncomputable def supportSetAt {t : ℕ}
    (F : Multiset (SupportPattern t)) (s : SupportOcc F) : Finset (Fin t) :=
  (supportPatternAt F s).1

/-- `omegaCount F T I` counts the occurrences of support patterns `S` in `F`
    with `S ⊆ T` and `|S ∩ I| = 1`, counting multiplicity. -/
noncomputable def omegaCount {t : ℕ}
    (F : Multiset (SupportPattern t))
    (T I : Finset (Fin t)) : ℕ :=
  ((Finset.univ : Finset (Fin F.card)).filter fun s =>
      supportSetAt F s ⊆ T ∧ ((supportSetAt F s ∩ I).card = 1)).card

/-- A support multiset `F` is an `n`-frame if the frame inequality holds for every
    `I ⊆ T ⊆ [t]`. -/
def IsFrame {t : ℕ}
    (F : Multiset (SupportPattern t))
    (cap : Fin t → ℕ) : Prop :=
  ∀ T I : Finset (Fin t), I ⊆ T →
    omegaCount F T I ≤ (T \ I).sum cap

/-- Vertices of the substituted hypergraph: tagged block vertices together with one
    vertex for each occurrence of a support pattern. -/
inductive SubstVertex (t : ℕ) (F : Multiset (SupportPattern t)) where
  | old (i : Fin t) (v : ℕ)
  | new (s : Fin F.card)
deriving DecidableEq

/-- The substituted hypergraph whose vertices live in `SubstVertex t F`. -/
abbrev SubstitutedHypergraph {t : ℕ} (F : Multiset (SupportPattern t)) :=
  Hypergraph (SubstVertex t F)

/-- The support vertices incident to every edge in block `i`. -/
noncomputable def supportVerticesOnBlock {t : ℕ}
    (F : Multiset (SupportPattern t)) (i : Fin t) : Finset (SubstVertex t F) :=
  ((Finset.univ : Finset (Fin F.card)).filter fun s =>
      i ∈ supportSetAt F s).image
    SubstVertex.new

/-- Lift one edge from block `i` into the substituted hypergraph. -/
noncomputable def liftBlockEdge {t : ℕ}
    (F : Multiset (SupportPattern t)) (i : Fin t) (e : Finset ℕ) :
    Finset (SubstVertex t F) :=
  (e.image fun v => SubstVertex.old i v) ∪ supportVerticesOnBlock F i

/-- The substitution hypergraph `F[G_1, ..., G_t]`, realized as the hypergraph whose
    vertices are tagged block vertices plus support vertices, and whose edges are the
    lifted edges of the blocks. -/
noncomputable def substitutionHypergraph {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t) : SubstitutedHypergraph F :=
  ((Finset.univ : Finset (Fin t)).biUnion fun i =>
    (blocks i).image (liftBlockEdge F i))

/-- The selected edges from block `i` inside a chosen subfamily `P` of the substituted
    hypergraph. -/
noncomputable def selectedBlockEdges {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) (i : Fin t) : Hypergraph ℕ :=
  (blocks i).filter fun e => liftBlockEdge F i e ∈ P

/-- The number of selected edges from block `i`. -/
noncomputable def selectedBlockCount {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) (i : Fin t) : ℕ :=
  (selectedBlockEdges F blocks P i).card

/-- The number of selected edges from block `i` containing `v`. -/
noncomputable def selectedOldVertexCount {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) (i : Fin t) (v : ℕ) : ℕ :=
  ((selectedBlockEdges F blocks P i).filter fun e => v ∈ e).card

/-- The number of selected substituted edges incident to a support occurrence. -/
noncomputable def selectedSupportCount {t : ℕ}
    {F : Multiset (SupportPattern t)}
    (P : SubstitutedHypergraph F) (s : SupportOcc F) : ℕ :=
  (P.filter fun E => SubstVertex.new s ∈ E).card

/-- The blocks from which at most one selected edge is taken. -/
noncomputable def tOf {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) : Finset (Fin t) :=
  (Finset.univ : Finset (Fin t)).filter fun i =>
    selectedBlockCount F blocks P i ≤ 1

/-- The blocks from which exactly one selected edge is taken. -/
noncomputable def iOf {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) : Finset (Fin t) :=
  (Finset.univ : Finset (Fin t)).filter fun i =>
    selectedBlockCount F blocks P i = 1

/-- The old vertices in block `i` that are seen exactly once by the selected family `P`. -/
noncomputable def oldUniqueVerticesOnBlock {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) (i : Fin t) : Finset ℕ :=
  (vertexSet (blocks i)).filter fun v =>
    (selectedOldVertexCount F blocks P i v = 1)

/-- The support-vertex occurrences seen exactly once by the selected family `P`. -/
noncomputable def newUniqueSupportVertices {t : ℕ}
    (F : Multiset (SupportPattern t))
    (P : SubstitutedHypergraph F) : Finset (SupportOcc F) :=
  (Finset.univ : Finset (Fin F.card)).filter fun s =>
    (selectedSupportCount P s = 1)

/-- The uniquely covered old vertices in the substituted hypergraph, grouped blockwise. -/
noncomputable def oldUniqueVertexUnion {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) : Finset (SubstVertex t F) :=
  ((Finset.univ : Finset (Fin t)).biUnion fun i =>
    (oldUniqueVerticesOnBlock F blocks P i).image (SubstVertex.old i))

/-- The uniquely covered support vertices in the substituted hypergraph. -/
noncomputable def newUniqueVertexUnion {t : ℕ}
    (F : Multiset (SupportPattern t))
    (P : SubstitutedHypergraph F) : Finset (SubstVertex t F) :=
  (newUniqueSupportVertices F P).image SubstVertex.new

/-- The old vertices coming from the block hypergraphs, tagged by their block index. -/
noncomputable def oldVertexUnion {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t) : Finset (SubstVertex t F) :=
  ((Finset.univ : Finset (Fin t)).biUnion fun i =>
    (vertexSet (blocks i)).image (SubstVertex.old i))

/-- All support vertices of the substituted hypergraph, indexed by their occurrences in `F`. -/
noncomputable def allNewVertices {t : ℕ}
    (F : Multiset (SupportPattern t)) : Finset (SubstVertex t F) :=
  (Finset.univ : Finset (Fin F.card)).image SubstVertex.new

@[simp] lemma mem_supportVerticesOnBlock_iff {t : ℕ}
    {F : Multiset (SupportPattern t)} {i : Fin t} {s : SupportOcc F} :
    SubstVertex.new s ∈ supportVerticesOnBlock F i ↔ i ∈ supportSetAt F s := by
  simp [supportVerticesOnBlock]

@[simp] lemma old_mem_liftBlockEdge_iff {t : ℕ}
    {F : Multiset (SupportPattern t)} {i j : Fin t} {v : ℕ} {e : Finset ℕ} :
    SubstVertex.old i v ∈ liftBlockEdge F j e ↔ i = j ∧ v ∈ e := by
  constructor
  · intro h
    rw [liftBlockEdge, Finset.mem_union] at h
    rcases h with h | h
    · rcases Finset.mem_image.mp h with ⟨v', hv', hEq⟩
      lia
    · rcases Finset.mem_image.mp h with ⟨s, hs, hEq⟩
      cases hEq
  · rintro ⟨rfl, hv⟩
    simp [liftBlockEdge, hv]

@[simp] lemma new_mem_liftBlockEdge_iff {t : ℕ}
    {F : Multiset (SupportPattern t)} {s : SupportOcc F} {i : Fin t} {e : Finset ℕ} :
    SubstVertex.new s ∈ liftBlockEdge F i e ↔ i ∈ supportSetAt F s := by
  simp [liftBlockEdge]

lemma liftBlockEdge_injective {t : ℕ}
    (F : Multiset (SupportPattern t)) (i : Fin t) :
    Function.Injective (liftBlockEdge F i) := by
  intro e e' hEq
  ext v
  constructor
  · intro hv
    have hmem : SubstVertex.old i v ∈ liftBlockEdge F i e := by
      simp [hv]
    rw [hEq] at hmem
    simpa using (old_mem_liftBlockEdge_iff.mp hmem).2
  · intro hv
    have hmem : SubstVertex.old i v ∈ liftBlockEdge F i e' := by
      simp [hv]
    rw [← hEq] at hmem
    simpa using (old_mem_liftBlockEdge_iff.mp hmem).2

lemma selectedBlockEdges_subset {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F) (i : Fin t) :
    selectedBlockEdges F blocks P i ⊆ blocks i := by
  intro e he
  exact (Finset.mem_filter.mp he).1

lemma mem_vertexSet_of_count_eq_one {V : Type*} [DecidableEq V]
    {edges P : Hypergraph V} {x : V} (hP : P ⊆ edges)
    (hx : (P.filter fun E => x ∈ E).card = 1) :
    x ∈ vertexSet edges := by
  have hpos : 0 < (P.filter fun E => x ∈ E).card := by simp [hx]
  rcases Finset.card_pos.mp hpos with ⟨E, hE⟩
  rw [vertexSet, Finset.mem_biUnion]
  exact ⟨E, hP (Finset.mem_filter.mp hE).1, (Finset.mem_filter.mp hE).2⟩

lemma liftBlockEdge_ne_of_ne {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (hEdgeDisjoint : Pairwise fun i j => Disjoint (blocks i) (blocks j))
    {i j : Fin t} (hij : i ≠ j) {e e' : Finset ℕ}
    (he : e ∈ blocks i) (he' : e' ∈ blocks j) :
    liftBlockEdge F i e ≠ liftBlockEdge F j e' := by
  intro hEq
  by_cases hne : e.Nonempty
  · rcases hne with ⟨v, hv⟩
    have hmem : SubstVertex.old i v ∈ liftBlockEdge F j e' := by
      rw [← hEq]
      simp [hv]
    exact hij (old_mem_liftBlockEdge_iff.mp hmem).1
  · have he0 : e = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    by_cases hne' : e'.Nonempty
    · rcases hne' with ⟨v, hv⟩
      have hmem : SubstVertex.old j v ∈ liftBlockEdge F i e := by
        rw [hEq]
        simp [hv]
      exact hij.symm (old_mem_liftBlockEdge_iff.mp hmem).1
    · have he'0 : e' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      exact Finset.disjoint_left.mp (hEdgeDisjoint hij)
        (by simpa [he0] using he) (by simpa [he'0] using he')

lemma liftedBlockImages_disjoint {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (hEdgeDisjoint : Pairwise fun i j => Disjoint (blocks i) (blocks j))
    {i j : Fin t} (hij : i ≠ j) :
    Disjoint ((blocks i).image (liftBlockEdge F i))
      ((blocks j).image (liftBlockEdge F j)) := by
  refine Finset.disjoint_left.mpr ?_
  intro E hEi hEj
  rcases Finset.mem_image.mp hEi with ⟨e, he, rfl⟩
  rcases Finset.mem_image.mp hEj with ⟨e', he', hEq⟩
  exact (liftBlockEdge_ne_of_ne F blocks hEdgeDisjoint hij he he') hEq.symm

lemma old_mem_vertexSet_substitution_iff {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (i : Fin t) (v : ℕ) :
    SubstVertex.old i v ∈ vertexSet (substitutionHypergraph F blocks) ↔
      v ∈ vertexSet (blocks i) := by
  constructor
  · intro h
    rw [vertexSet, Finset.mem_biUnion] at h
    rcases h with ⟨E, hE, hmemE⟩
    rw [substitutionHypergraph, Finset.mem_biUnion] at hE
    rcases hE with ⟨j, -, hEj⟩
    rcases Finset.mem_image.mp hEj with ⟨e, he, rfl⟩
    rcases old_mem_liftBlockEdge_iff.mp hmemE with ⟨hij, hv⟩
    subst hij
    rw [vertexSet, Finset.mem_biUnion]
    exact ⟨e, he, hv⟩
  · intro hv
    rw [vertexSet, Finset.mem_biUnion] at hv
    rcases hv with ⟨e, he, hv⟩
    rw [vertexSet, Finset.mem_biUnion]
    refine ⟨liftBlockEdge F i e, ?_, ?_⟩
    · rw [substitutionHypergraph, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
    · exact old_mem_liftBlockEdge_iff.mpr ⟨rfl, hv⟩

lemma new_mem_vertexSet_substitution_iff {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (s : SupportOcc F) :
    SubstVertex.new s ∈ vertexSet (substitutionHypergraph F blocks) ↔
      ∃ i ∈ supportSetAt F s, (blocks i).Nonempty := by
  constructor
  · intro h
    rw [vertexSet, Finset.mem_biUnion] at h
    rcases h with ⟨E, hE, hmemE⟩
    rw [substitutionHypergraph, Finset.mem_biUnion] at hE
    rcases hE with ⟨i, -, hEi⟩
    rcases Finset.mem_image.mp hEi with ⟨e, he, rfl⟩
    exact ⟨i, new_mem_liftBlockEdge_iff.mp hmemE, ⟨e, he⟩⟩
  · rintro ⟨i, hi, e, he⟩
    rw [vertexSet, Finset.mem_biUnion]
    refine ⟨liftBlockEdge F i e, ?_, ?_⟩
    · rw [substitutionHypergraph, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
    · exact new_mem_liftBlockEdge_iff.mpr hi

lemma old_selected_count_eq {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F)
    (hP : P ⊆ substitutionHypergraph F blocks)
    (i : Fin t) (v : ℕ) :
    (P.filter fun E => SubstVertex.old i v ∈ E).card =
      selectedOldVertexCount F blocks P i v := by
  have hEq :
      P.filter (fun E => SubstVertex.old i v ∈ E) =
        ((selectedBlockEdges F blocks P i).filter fun e => v ∈ e).image (liftBlockEdge F i) := by
    ext E
    constructor
    · intro hE
      rcases Finset.mem_filter.mp hE with ⟨hEP, hOld⟩
      have hEP' := hP hEP
      rw [substitutionHypergraph, Finset.mem_biUnion] at hEP'
      rcases hEP' with ⟨j, -, hEj⟩
      rcases Finset.mem_image.mp hEj with ⟨e, he, rfl⟩
      rcases old_mem_liftBlockEdge_iff.mp hOld with ⟨hij, hv⟩
      subst hij
      exact Finset.mem_image.mpr ⟨e, by
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he, hEP⟩, hv⟩, rfl⟩
    · intro hE
      rcases Finset.mem_image.mp hE with ⟨e, he, rfl⟩
      rcases Finset.mem_filter.mp he with ⟨heSel, hv⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp heSel).2, by simp [hv]⟩
  rw [hEq, Finset.card_image_of_injective _ (liftBlockEdge_injective F i)]
  simp [selectedOldVertexCount]

lemma filter_new_eq_biUnion {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F)
    (hP : P ⊆ substitutionHypergraph F blocks)
    (s : SupportOcc F) :
    P.filter (fun E => SubstVertex.new s ∈ E) =
      (supportSetAt F s).biUnion fun i =>
        (selectedBlockEdges F blocks P i).image (liftBlockEdge F i) := by
  ext E
  constructor
  · intro hE
    rcases Finset.mem_filter.mp hE with ⟨hEP, hNew⟩
    have hEP' := hP hEP
    rw [substitutionHypergraph, Finset.mem_biUnion] at hEP'
    rcases hEP' with ⟨i, hi, hEi⟩
    rcases Finset.mem_image.mp hEi with ⟨e, he, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨i, new_mem_liftBlockEdge_iff.mp hNew, ?_⟩
    exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hEP⟩, rfl⟩
  · intro hE
    rcases Finset.mem_biUnion.mp hE with ⟨i, hi, hEi⟩
    rcases Finset.mem_image.mp hEi with ⟨e, he, rfl⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).2, by simp [hi]⟩

lemma selectedImages_disjoint {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F)
    (hEdgeDisjoint : Pairwise fun i j => Disjoint (blocks i) (blocks j))
    {S : Finset (Fin t)} :
    (S : Set (Fin t)).PairwiseDisjoint fun i =>
      (selectedBlockEdges F blocks P i).image (liftBlockEdge F i) := by
  intro i hi j hj hij
  refine Finset.disjoint_left.mpr ?_
  intro E hEi hEj
  rcases Finset.mem_image.mp hEi with ⟨e, he, rfl⟩
  rcases Finset.mem_image.mp hEj with ⟨e', he', hEq⟩
  exact (liftBlockEdge_ne_of_ne F blocks hEdgeDisjoint hij
    (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he').1) hEq.symm

lemma new_selected_count_eq_sum {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F)
    (hP : P ⊆ substitutionHypergraph F blocks)
    (hEdgeDisjoint : Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (s : SupportOcc F) :
    selectedSupportCount P s =
      ∑ i ∈ supportSetAt F s, selectedBlockCount F blocks P i := by
  unfold selectedSupportCount
  rw [filter_new_eq_biUnion F blocks P hP s]
  rw [Finset.card_biUnion (selectedImages_disjoint F blocks P hEdgeDisjoint)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.card_image_of_injective _ (liftBlockEdge_injective F i), selectedBlockCount]

@[simp] lemma mem_tOf_iff {t : ℕ}
    {F : Multiset (SupportPattern t)}
    {blocks : BlockFamily t}
    {P : SubstitutedHypergraph F} {i : Fin t} :
    i ∈ tOf F blocks P ↔ selectedBlockCount F blocks P i ≤ 1 := by
  simp [tOf]

@[simp] lemma mem_iOf_iff {t : ℕ}
    {F : Multiset (SupportPattern t)}
    {blocks : BlockFamily t}
    {P : SubstitutedHypergraph F} {i : Fin t} :
    i ∈ iOf F blocks P ↔ selectedBlockCount F blocks P i = 1 := by
  simp [iOf]

lemma card_inter_iOf_eq_sum_indicator {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F)
    (S : Finset (Fin t)) :
    (S ∩ iOf F blocks P).card =
      ∑ i ∈ S, if selectedBlockCount F blocks P i = 1 then 1 else 0 := by
  rw [show S ∩ iOf F blocks P =
      S.filter (fun i => selectedBlockCount F blocks P i = 1) by
      ext i
      simp [iOf]]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

lemma sum_selected_eq_card_inter_iOf {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F)
    (S : Finset (Fin t))
    (hST : S ⊆ tOf F blocks P) :
    ∑ i ∈ S, selectedBlockCount F blocks P i = (S ∩ iOf F blocks P).card := by
  rw [card_inter_iOf_eq_sum_indicator F blocks P S]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : selectedBlockCount F blocks P i ≤ 1 := by
    exact (mem_tOf_iff.mp (hST hi))
  lia

lemma sum_selected_eq_one_iff {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F)
    (S : Finset (Fin t)) :
    (∑ i ∈ S, selectedBlockCount F blocks P i = 1) ↔
      S ⊆ tOf F blocks P ∧ (S ∩ iOf F blocks P).card = 1 := by
  constructor
  · intro hsum
    have hST : S ⊆ tOf F blocks P := by
      intro i hi
      rw [mem_tOf_iff]
      have hle : selectedBlockCount F blocks P i ≤
          ∑ j ∈ S, selectedBlockCount F blocks P j := by
        exact single_le_sum_of_canonicallyOrdered hi
      omega
    refine ⟨hST, ?_⟩
    rw [← sum_selected_eq_card_inter_iOf F blocks P S hST, hsum]
  · rintro ⟨hST, hcard⟩
    rw [sum_selected_eq_card_inter_iOf F blocks P S hST, hcard]

lemma new_unique_iff {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (P : SubstitutedHypergraph F)
    (hP : P ⊆ substitutionHypergraph F blocks)
    (hEdgeDisjoint : Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (s : SupportOcc F) :
    (selectedSupportCount P s = 1) ↔
      supportSetAt F s ⊆ tOf F blocks P ∧
      ((supportSetAt F s ∩ iOf F blocks P).card = 1) := by
  rw [new_selected_count_eq_sum F blocks P hP hEdgeDisjoint s]
  exact sum_selected_eq_one_iff F blocks P (supportSetAt F s)

lemma support_vertex_realized {t : ℕ}
    (F : Multiset (SupportPattern t))
    (edgeCounts : Fin t → ℕ)
    (blocks : BlockFamily t)
    (hFrame : IsFrame F edgeCounts)
    (hEdgeCounts : ∀ i, (blocks i).card = edgeCounts i)
    (s : SupportOcc F) :
    ∃ i ∈ supportSetAt F s, (blocks i).Nonempty := by
  let S := supportSetAt F s
  have hSnonempty : S.Nonempty := by
    refine Finset.card_pos.mp ?_
    exact lt_of_lt_of_le (by decide : 0 < 2) (supportPatternAt F s).2
  rcases hSnonempty with ⟨i, hi⟩
  have hOmegaPos : 0 < omegaCount F S ({i} : Finset (Fin t)) := by
    unfold omegaCount
    apply Finset.card_pos.mpr
    refine ⟨s, ?_⟩
    simp [S, hi]
  have hBound := hFrame S ({i} : Finset (Fin t)) (Finset.singleton_subset_iff.mpr hi)
  have hSumPos : 0 < (S \ {i}).sum edgeCounts := lt_of_lt_of_le hOmegaPos hBound
  have hExists : ∃ j ∈ S \ {i}, 0 < edgeCounts j := by
    exact sum_pos_iff.mp hSumPos
  rcases hExists with ⟨j, hj, hjPos⟩
  refine ⟨j, (Finset.mem_sdiff.mp hj).1, ?_⟩
  rw [← hEdgeCounts j] at hjPos
  exact Finset.card_pos.mp hjPos

/-! ## Substitution theorem -/

/-- The assumptions on a family of block hypergraphs needed for the qualitative
    substitution theorem. -/
structure PartitionedBlocks {t : ℕ}
    (cap : Fin t → ℕ) (blocks : BlockFamily t) : Prop where
  vertexDisjoint : Pairwise fun i j => Disjoint (vertexSet (blocks i)) (vertexSet (blocks j))
  edgeDisjoint : Pairwise fun i j => Disjoint (blocks i) (blocks j)
  partitionBound : ∀ i, NoLargePartition (blocks i) (cap i)

/-- The additional edge/vertex count data needed for the quantitative recurrence. -/
structure CountedBlocks {t : ℕ}
    (edgeCounts vertexCounts : Fin t → ℕ) (blocks : BlockFamily t)
    : Prop extends PartitionedBlocks edgeCounts blocks where
  edgeCard : ∀ i, (blocks i).card = edgeCounts i
  vertexCard : ∀ i, (vertexSet (blocks i)).card = vertexCounts i

/-- If `F` is an `n`-frame and each block hypergraph has no partition larger than its
    capacity, then the substituted hypergraph has no partition larger than the total
    capacity. The hypotheses on pairwise disjoint vertex and edge sets match the setup
    in `frontier.tex`. -/
theorem substitution_theorem {t : ℕ}
    (F : Multiset (SupportPattern t))
    (cap : Fin t → ℕ)
    (blocks : BlockFamily t)
    (hFrame : IsFrame F cap)
    (hBlocks : PartitionedBlocks cap blocks) :
    NoLargePartition (substitutionHypergraph F blocks)
      ((Finset.univ : Finset (Fin t)).sum cap) := by
  intro P hP
  let T := tOf F blocks P
  let I := iOf F blocks P
  let oldCount : Fin t → ℕ := fun i => (oldUniqueVerticesOnBlock F blocks P i).card
  have hIT : I ⊆ T := by
    intro i hi
    rw [mem_tOf_iff]
    rw [mem_iOf_iff] at hi
    omega
  have hUniqueSet :
      (vertexSet (substitutionHypergraph F blocks)).filter
        (fun x => (P.filter fun E => x ∈ E).card = 1) =
      oldUniqueVertexUnion F blocks P ∪ newUniqueVertexUnion F P := by
    ext x
    cases x with
    | old i v =>
        constructor
        · intro hx
          rcases Finset.mem_filter.mp hx with ⟨hxVert, hxCount⟩
          have hvVert : v ∈ vertexSet (blocks i) :=
            (old_mem_vertexSet_substitution_iff F blocks i v).mp hxVert
          have hvCount :
              selectedOldVertexCount F blocks P i v = 1 := by
            rw [← old_selected_count_eq F blocks P hP i v]
            exact hxCount
          exact Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
              Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hvVert, hvCount⟩, rfl⟩⟩
        · intro hx
          rcases Finset.mem_union.mp hx with hxOld | hxNew
          · rcases Finset.mem_biUnion.mp hxOld with ⟨j, -, hEj⟩
            rcases Finset.mem_image.mp hEj with ⟨v', hv', hEq⟩
            rcases Finset.mem_filter.mp hv' with ⟨hvVert, hvCount⟩
            cases hEq
            exact Finset.mem_filter.mpr
              ⟨(old_mem_vertexSet_substitution_iff F blocks i v).2 hvVert, by
                rwa [old_selected_count_eq F blocks P hP i v]⟩
          · rcases Finset.mem_image.mp hxNew with ⟨s, hs, hEq⟩
            cases hEq
    | new s =>
        constructor
        · intro hx
          rcases Finset.mem_filter.mp hx with ⟨_, hs1⟩
          exact Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs1⟩, rfl⟩
        · intro hx
          rcases Finset.mem_union.mp hx with hxOld | hxNew
          · rcases Finset.mem_biUnion.mp hxOld with ⟨i, -, hEi⟩
            rcases Finset.mem_image.mp hEi with ⟨v, hv, hEq⟩
            cases hEq
          · rcases Finset.mem_image.mp hxNew with ⟨s', hs, hEq⟩
            cases hEq
            exact Finset.mem_filter.mpr
              ⟨mem_vertexSet_of_count_eq_one hP (Finset.mem_filter.mp hs).2,
                (Finset.mem_filter.mp hs).2⟩
  have hOldNewDisj :
      Disjoint (oldUniqueVertexUnion F blocks P) (newUniqueVertexUnion F P) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    cases x with
    | old i v =>
        rcases Finset.mem_image.mp hy with ⟨s, hs, hEq⟩
        cases hEq
    | new s =>
        rcases Finset.mem_biUnion.mp hx with ⟨i, -, hEi⟩
        rcases Finset.mem_image.mp hEi with ⟨v, hv, hEq⟩
        cases hEq
  have hUniqueEq :
      uniqueCoverage (substitutionHypergraph F blocks) P =
        (oldUniqueVertexUnion F blocks P).card +
        (newUniqueVertexUnion F P).card := by
    rw [uniqueCoverage, hUniqueSet, Finset.card_union_of_disjoint hOldNewDisj]
  have hOldCard :
      (oldUniqueVertexUnion F blocks P).card = (Finset.univ : Finset (Fin t)).sum oldCount := by
    rw [oldUniqueVertexUnion, Finset.card_biUnion]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.card_image_of_injective]
      intro v w h
      simpa using h
    · intro i hi j hj hij
      refine Finset.disjoint_left.mpr ?_
      intro x hx hy
      rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨w, hw, hEq⟩
      exact hij (by cases hEq; rfl)
  have hOldLe : ∀ i, oldCount i ≤ cap i := by
    intro i
    simpa [oldCount, uniqueCoverage, oldUniqueVerticesOnBlock, selectedOldVertexCount] using
      hBlocks.partitionBound i (selectedBlockEdges F blocks P i)
        (selectedBlockEdges_subset F blocks P i)
  have hOldZero : ∀ i ∈ T \ I, oldCount i = 0 := by
    intro i hi
    have hle : selectedBlockCount F blocks P i ≤ 1 :=
      mem_tOf_iff.mp (Finset.mem_sdiff.mp hi).1
    have hne : selectedBlockCount F blocks P i ≠ 1 := fun h1 =>
      (Finset.mem_sdiff.mp hi).2 (mem_iOf_iff.mpr h1)
    have h0 : selectedBlockCount F blocks P i = 0 := by
      omega
    have hEmpty : selectedBlockEdges F blocks P i = ∅ := Finset.card_eq_zero.mp h0
    simp [oldCount, oldUniqueVerticesOnBlock, selectedOldVertexCount, hEmpty]
  have hOldBound :
      (oldUniqueVertexUnion F blocks P).card ≤
        (((Finset.univ : Finset (Fin t)) \ T).sum cap) + I.sum cap := by
    have hRestrict :
        (Finset.univ : Finset (Fin t)).sum oldCount =
          ((((Finset.univ : Finset (Fin t)) \ T) ∪ I)).sum oldCount := by
      symm
      apply Finset.sum_subset (by simp)
      intro i hiU hiNot
      have hiT : i ∈ T := by
        by_contra hiT
        exact hiNot <| Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiT⟩
      have hiNotI : i ∉ I := by
        exact fun hiI => hiNot <| Finset.mem_union.mpr <| Or.inr hiI
      exact hOldZero i (Finset.mem_sdiff.mpr ⟨hiT, hiNotI⟩)
    have hDisjCompI : Disjoint ((Finset.univ : Finset (Fin t)) \ T) I :=
      Finset.disjoint_left.mpr fun i hi1 hi2 => (Finset.mem_sdiff.mp hi1).2 (hIT hi2)
    calc
      (oldUniqueVertexUnion F blocks P).card
          = (Finset.univ : Finset (Fin t)).sum oldCount := hOldCard
      _ = ((((Finset.univ : Finset (Fin t)) \ T) ∪ I)).sum oldCount := hRestrict
      _ ≤ ((((Finset.univ : Finset (Fin t)) \ T) ∪ I)).sum cap :=
        Finset.sum_le_sum fun i _ => hOldLe i
      _ = (((Finset.univ : Finset (Fin t)) \ T).sum cap) + I.sum cap := by
        rw [Finset.sum_union hDisjCompI]
  have hNewCard :
      (newUniqueVertexUnion F P).card = omegaCount F T I := by
    rw [newUniqueVertexUnion, Finset.card_image_of_injective]
    · apply congrArg Finset.card
      ext s
      constructor
      · intro hs
        have hs' : selectedSupportCount P s = 1 := by
          simpa [newUniqueSupportVertices] using hs
        simpa [T, I] using (new_unique_iff F blocks P hP hBlocks.edgeDisjoint s).1 hs'
      · intro hs
        have hsProp :
            supportSetAt F s ⊆ tOf F blocks P ∧
              ((supportSetAt F s ∩ iOf F blocks P).card = 1) :=
          (Finset.mem_filter.mp hs).2
        have hs' : selectedSupportCount P s = 1 := by
          simpa [T, I] using (new_unique_iff F blocks P hP hBlocks.edgeDisjoint s).2 hsProp
        simpa [newUniqueSupportVertices] using hs'
    · intro s s' h
      simpa using h
  have hNewBound :
      (newUniqueVertexUnion F P).card ≤ (T \ I).sum cap := by
    simpa [hNewCard] using hFrame T I hIT
  have hSumT :
      T.sum cap = (T \ I).sum cap + I.sum cap := by
    exact Eq.symm (sum_sdiff hIT)
  have hSumUniv :
      (Finset.univ : Finset (Fin t)).sum cap =
        (((Finset.univ : Finset (Fin t)) \ T).sum cap) + T.sum cap := by
    calc
      (Finset.univ : Finset (Fin t)).sum cap =
          (((Finset.univ : Finset (Fin t)) \ T) ∪ T).sum cap := by
            simpa using
              (congrArg (fun S : Finset (Fin t) => S.sum cap)
                (by simp : ((Finset.univ : Finset (Fin t)) \ T) ∪ T
                  = (Finset.univ : Finset (Fin t)))).symm
      _ = (((Finset.univ : Finset (Fin t)) \ T).sum cap) + T.sum cap :=
        Finset.sum_union (s₁ := ((Finset.univ : Finset (Fin t)) \ T)) (s₂ := T)
          Finset.sdiff_disjoint
  lia

/-- Quantitative corollary of the substitution theorem used throughout the recursive
    constructions. Since hypergraphs are encoded by their edge sets, "no isolated
    vertices" is implicit in the use of `vertexSet`. -/
theorem frame_recurrence {t : ℕ}
    (F : Multiset (SupportPattern t))
    (edgeCounts vertexCounts : Fin t → ℕ)
    (blocks : BlockFamily t)
    (hFrame : IsFrame F edgeCounts)
    (hBlocks : CountedBlocks edgeCounts vertexCounts blocks) :
    (substitutionHypergraph F blocks).card = ((Finset.univ : Finset (Fin t)).sum edgeCounts) ∧
    (vertexSet (substitutionHypergraph F blocks)).card =
      ((Finset.univ : Finset (Fin t)).sum vertexCounts) + F.card ∧
    NoLargePartition (substitutionHypergraph F blocks)
      ((Finset.univ : Finset (Fin t)).sum edgeCounts) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [substitutionHypergraph, Finset.card_biUnion]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.card_image_of_injective _ (liftBlockEdge_injective F i), hBlocks.edgeCard i]
    · intro i hi j hj hij
      simpa using liftedBlockImages_disjoint F blocks hBlocks.edgeDisjoint hij
  · have hOldCard :
        (oldVertexUnion F blocks).card = ∑ i, vertexCounts i := by
      rw [oldVertexUnion, Finset.card_biUnion]
      · refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Finset.card_image_of_injective]
        · exact hBlocks.vertexCard i
        · intro v w h
          simpa using h
      · intro i hi j hj hij
        refine Finset.disjoint_left.mpr ?_
        intro x hx hy
        rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨w, hw, hEq⟩
        exact hij (by cases hEq; rfl)
    have hNewCard : (allNewVertices F).card = F.card := by
      rw [allNewVertices, Finset.card_image_of_injective]
      · simp
      · intro s s' h
        simpa using h
    have hOldNewDisj : Disjoint (oldVertexUnion F blocks) (allNewVertices F) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hy
      cases x with
      | old i v =>
          rcases Finset.mem_image.mp hy with ⟨s, hs, hEq⟩
          cases hEq
      | new s =>
          rcases Finset.mem_biUnion.mp hx with ⟨i, -, hEi⟩
          rcases Finset.mem_image.mp hEi with ⟨v, hv, hEq⟩
          cases hEq
    have hVertexSetEq :
        vertexSet (substitutionHypergraph F blocks) =
          oldVertexUnion F blocks ∪ allNewVertices F := by
      ext x
      cases x with
      | old i v =>
          constructor
          · intro hx
            exact Finset.mem_union.mpr <| Or.inl <|
              Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
                Finset.mem_image.mpr ⟨v,
                  (old_mem_vertexSet_substitution_iff F blocks i v).mp hx, rfl⟩⟩
          · intro hx
            rcases Finset.mem_union.mp hx with hxOld | hxNew
            · rcases Finset.mem_biUnion.mp hxOld with ⟨j, -, hEj⟩
              rcases Finset.mem_image.mp hEj with ⟨v', hv', hEq⟩
              cases hEq
              exact (old_mem_vertexSet_substitution_iff F blocks i v).2 hv'
            · rcases Finset.mem_image.mp hxNew with ⟨s, hs, hEq⟩
              cases hEq
      | new s =>
          constructor
          · intro hx
            exact Finset.mem_union.mpr <| Or.inr <|
              Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
          · intro hx
            rcases Finset.mem_union.mp hx with hxOld | hxNew
            · rcases Finset.mem_biUnion.mp hxOld with ⟨i, -, hEi⟩
              rcases Finset.mem_image.mp hEi with ⟨v, hv, hEq⟩
              cases hEq
            · rcases Finset.mem_image.mp hxNew with ⟨s', hs, hEq⟩
              cases hEq
              exact (new_mem_vertexSet_substitution_iff F blocks s).2
                (support_vertex_realized F edgeCounts blocks hFrame hBlocks.edgeCard s)
    rw [hVertexSetEq, Finset.card_union_of_disjoint hOldNewDisj, hOldCard, hNewCard]
  · exact substitution_theorem F edgeCounts blocks hFrame hBlocks.toPartitionedBlocks

end HypergraphLowerBound
