/-
Copyright (c) 2026 Axiom Math contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AgreeToDisagree contributors
-/
import Mathlib.Data.Setoid.Partition
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Aumann's agreement theorem

This file develops information partitions and conditional probabilities needed
for Aumann's agreement theorem.
-/

namespace AgreeToDisagree

open Set

variable {α Ω : Type*}

section Prerequisites

/-- We write `Partition α` for the type of partitions of a set `α`, implemented as a subtype
of `Set (Set α)`. Mathlib already equips this subtype with the order given by refinement (such that
`P ≤ Q` iff `P` refines `Q`) and proves that it is a complete lattice, i.e. that arbitrary infima
and suprema of partitions exist. -/
abbrev Partition (α : Type*) := Setoid.Partitions α

/-- When we write `s ∈ P` for a partition `P : Partition α`, we mean that `s` is a `Set α` that is
an element of the `Set (Set α)` underlying `P`. -/
@[reducible]
instance Partition.instSetLike : SetLike (Partition α) (Set α) where
  coe := Subtype.val
  coe_injective := Subtype.val_injective

/-- As expected, a partition `P` refines a partition `Q` iff every set in `P` is contained in
a set in `Q`. -/
lemma Partition.le_iff {P Q : Partition α} : P ≤ Q ↔ ∀ s ∈ P, ∃ t ∈ Q, s ⊆ t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro s hs
    have ⟨a, ha⟩ := Setoid.nonempty_of_mem_partition P.2 hs
    refine ⟨{b | Setoid.mkClasses _ Q.2.2 b a}, ?_, ?_⟩
    · have := Setoid.mem_classes (Setoid.mkClasses _ Q.2.2) a
      rwa [Setoid.classes_mkClasses Q.1 Q.2] at this
    · refine fun b hb ↦ h fun s' hs' hbs' ↦ ?_
      rwa [← P.2.pairwiseDisjoint.elim hs hs' <| not_disjoint_iff.2 ⟨b, hb, hbs'⟩]
  · intro a b hab s hs has
    have ⟨t, ⟨ht, hat⟩, _⟩ := P.2.2 a
    have ⟨s', hs'⟩ := h t ht
    rw [Q.2.pairwiseDisjoint.elim hs hs'.1 <| not_disjoint_iff.2 ⟨a, has, hs'.2 hat⟩]
    exact hs'.2 <| hab t ht hat

/-- We call a partition of a measurable space measurable if it consists of measurable sets. -/
protected def Partition.Measurable [MeasurableSpace Ω] (P : Partition Ω) :=
  ∀ s ∈ P, MeasurableSet s

/-- If a countable partition is measurable, every partition it refines is measurable too.
Note that the countability assumption is necessary because e.g. the partition into singletons is
usually measurable but refines all other partitions, even nonmeasurable ones. -/
lemma Partition.Measurable.mono [MeasurableSpace Ω] {P Q : Partition Ω}
    (hP : P.Measurable) (hP' : P.val.Countable) (hQ : P ≤ Q) : Q.Measurable := by
  intro s hs
  rw [← inter_univ s, ← P.2.sUnion_eq_univ, sUnion_eq_iUnion, inter_iUnion]
  have := hP'.to_subtype
  refine MeasurableSet.iUnion fun t ↦ ?_
  have ⟨s', hs'⟩ := le_iff.1 hQ _ t.2
  obtain h | h := Q.2.pairwiseDisjoint.eq_or_disjoint hs hs'.1
  · rw [h, inter_eq_right.2 hs'.2]
    exact hP _ t.2
  · suffices s ∩ t ⊆ ∅ by simp_all
    exact (inter_subset_inter_right s hs'.2).trans <| Set.disjoint_iff.1 h

/-- The supremum of two measurable partitions is measurable if at least one of the two partitions
is countable. -/
lemma Partition.Measurable.sup [MeasurableSpace Ω] {P Q : Partition Ω}
    (hP : P.Measurable) (hQ : Q.Measurable) (h : P.val.Countable ∨ Q.val.Countable) :
    (P ⊔ Q).Measurable := by
  obtain h | h := h
  · exact hP.mono h le_sup_left
  · exact hQ.mono h le_sup_right

/-- `P.class a` is the element of a partition `P : Partition α` that contains `a : α`. -/
protected def Partition.class (P : Partition α) (a : α) : Set α :=
  {b | Setoid.mkClasses P.1 P.2.2 b a}

lemma Partition.mem_class (P : Partition α) (a : α) : a ∈ P.class a :=
  (Setoid.mkClasses P.1 P.2.2).2.refl _

lemma Partition.class_mem (P : Partition α) (a : α) : P.class a ∈ P :=
  (Setoid.classes_mkClasses P.1 P.2 ▸ (Setoid.mkClasses P.1 P.2.2).mem_classes a:)

lemma Partition.Measurable.measurableSet_class [MeasurableSpace Ω] {P : Partition Ω}
    (hP : P.Measurable) (ω : Ω) : MeasurableSet (P.class ω) :=
  hP _ (P.class_mem ω)

lemma Partition.class_mono {P Q : Partition α} (h : P ≤ Q) (a : α) :
    P.class a ⊆ Q.class a :=
  fun x ↦ @h x a

lemma Partition.class_eq_class_of_mem {P : Partition α} {a a' : α} (h : a' ∈ P.class a) :
    P.class a' = P.class a :=
  (Setoid.eq_eqv_class_of_mem P.2.2 (P.class_mem a) h).symm

lemma Partition.class_eq_of_mem {P : Partition α} {s : Set α} {a : α}
    (hs : s ∈ P) (ha : a ∈ s) : P.class a = s :=
  (Setoid.eq_eqv_class_of_mem P.2.2 hs ha).symm

lemma Partition.class_eq_biUnion_of_le {P Q : Partition α} (h : P ≤ Q) (a : α) :
    Q.class a = ⋃ s ∈ {s ∈ P | s ⊆ Q.class a}, s := by
  ext b
  refine ⟨fun hb ↦ ?_, fun hb ↦ ?_⟩
  · exact mem_biUnion ⟨P.class_mem b, (P.class_mono h b).trans_eq (Q.class_eq_class_of_mem hb)⟩
      (P.mem_class b)
  · obtain ⟨s, hs, hs'⟩ := mem_iUnion₂.mp hb
    exact hs.2 hs'

lemma Partition.class_subset_of_le {P Q : Partition α} (hle : P ≤ Q) (ω : α) :
    P.class ω ⊆ Q.class ω :=
  P.class_mono hle ω

lemma Partition.class_eq_of_mem_part {P : Partition α} {s : Set α} {ω : α}
    (hs : s ∈ P) (hω : ω ∈ s) : P.class ω = s :=
  P.class_eq_of_mem hs hω

lemma Partition.pairwise_disjoint_subtype_val (P : Partition α) :
    Pairwise (Function.onFun Disjoint (fun i : ↑(P.val) => (i : Set α))) :=
  fun ⟨_, hs⟩ ⟨_, ht⟩ hne => Set.disjoint_left.mpr fun _ has hat =>
    hne <| Subtype.ext ((class_eq_of_mem_part hs has).symm.trans (class_eq_of_mem_part ht hat))

end Prerequisites

open MeasureTheory

variable [MeasurableSpace Ω] {μ μ₁ μ₂ : Measure Ω} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- Conditional probability of an event inside the atom of a partition containing a point. -/
noncomputable abbrev Partition.probabilityAt (P : Partition Ω)
    (μ : Measure Ω) (E : Set Ω) (ω : Ω) : ENNReal :=
  μ (E ∩ P.class ω) / μ (P.class ω)

/-- A partition with all parts of positive measure is countable. -/
lemma Partition.countable_of_measure_pos {μ : Measure Ω} [IsProbabilityMeasure μ]
    {P : Partition Ω} (hP : P.Measurable) (hP' : ∀ s ∈ P, μ s > 0) :
    P.val.Countable := by
  rw [← Set.countable_coe_iff, ← Set.countable_univ_iff]
  convert μ.countable_meas_pos_of_disjoint_iUnion (fun s : P.1 ↦ hP s.1 s.2) ?_ using 1
  · ext ⟨s, hs⟩; simp [hP' s hs]
  · intro s t hst
    exact P.2.pairwiseDisjoint s.2 t.2 (fun h ↦ hst (Subtype.ext h))

lemma Partition.countable_of_pos_measure {μ : Measure Ω} [IsProbabilityMeasure μ]
    (P : Partition Ω) (hP : P.Measurable) (hP' : ∀ s ∈ P, μ s > 0) :
    P.val.Countable :=
  P.countable_of_measure_pos hP hP'

lemma measure_inter_eq_mul_of_probabilityAt_eq
    (P : Partition Ω) (hP' : ∀ s ∈ P, μ s > 0)
    {E : Set Ω} {s S : Set Ω} {p : ENNReal}
    (hs : s ∈ P) (hsS : s ⊆ S)
    (hconst : ∀ ω' ∈ S, P.probabilityAt μ E ω' = p) :
    μ (E ∩ s) = p * μ s := by
  obtain ⟨ω, hω⟩ := Setoid.nonempty_of_mem_partition P.2 hs
  have hprob : μ (E ∩ s) / μ s = p := by
    simpa only [Partition.probabilityAt, Partition.class_eq_of_mem_part hs hω]
      using hconst ω (hsS hω)
  rw [← hprob, ENNReal.div_mul_cancel (ne_of_gt (hP' s hs)) (measure_ne_top μ s)]

lemma measure_inter_sup_class_eq_mul
    (P : Partition Ω) (hPm : P.Measurable) (hP' : ∀ s ∈ P, μ s > 0)
    {E S : Set Ω} {p : ENNReal}
    (hE : MeasurableSet E)
    (hS : S = ⋃ s ∈ {s ∈ P | s ⊆ S}, s)
    (hctbl : P.val.Countable)
    (hconst : ∀ ω' ∈ S, P.probabilityAt μ E ω' = p) :
    μ (E ∩ S) = p * μ S := by
  set T := {s ∈ P | s ⊆ S}
  have hT_ctbl : T.Countable := hctbl.mono fun _ hs => hs.1
  have hT_disj : T.PairwiseDisjoint id := fun s hs t ht hne =>
    P.2.pairwiseDisjoint hs.1 ht.1 (fun heq => hne (heq ▸ rfl))
  have hT_meas : ∀ s ∈ T, MeasurableSet s := fun s hs => hPm s hs.1
  rw [show μ (E ∩ S) = ∑' (t : T), μ (E ∩ ↑t) by
      conv_lhs => rw [hS, inter_iUnion₂]
      exact measure_biUnion hT_ctbl
        (fun s hs t ht hne => (hT_disj hs ht hne).mono inf_le_right inf_le_right)
        (fun s hs => hE.inter (hT_meas s hs)),
    show μ S = ∑' (t : T), μ (t : Set Ω) by
      conv_lhs => rw [hS]
      exact measure_biUnion hT_ctbl hT_disj hT_meas]
  simp_rw [show ∀ t : T, μ (E ∩ (t : Set Ω)) = p * μ (t : Set Ω) from
    fun t => measure_inter_eq_mul_of_probabilityAt_eq P hP' t.2.1 t.2.2 hconst]
  exact ENNReal.tsum_mul_left

/-- Let `P` be a partition of `Ω` into measurable non-null sets, `Q` a coarser partition and
`E` a set such that `P.probabilityAt E ω' = p` for all `ω' ∈ Q.class ω`.
Then `Q.probabilityAt E ω = p`. -/
lemma Partition.probabilityAt_eq_of_le {P Q : Partition Ω} (hP : P.Measurable)
    (hP' : ∀ s ∈ P, μ s > 0) (hQ : P ≤ Q) {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ENNReal}
    (h : ∀ ω' ∈ Q.class ω, P.probabilityAt μ E ω' = p) :
    Q.probabilityAt μ E ω = p := by
  have hP'' := P.countable_of_measure_pos hP hP'
  rw [eq_comm, ENNReal.eq_div_iff (pos_mono (P.class_mono hQ ω) (hP' _ (P.class_mem ω))).ne'
      (measure_ne_top _ _),
    P.class_eq_biUnion_of_le hQ ω, Set.inter_iUnion₂,
    measure_biUnion (hP''.mono fun s hs ↦ hs.1) ?_ (fun s hs ↦ hP s hs.1), ← ENNReal.tsum_mul_right,
    measure_biUnion (hP''.mono fun s hs ↦ hs.1) ?_ (fun s hs ↦ hE.inter (hP s hs.1))]
  · congr; ext s
    have ⟨ω', hω'⟩ := Setoid.nonempty_of_mem_partition P.2 s.2.1
    rw [← P.class_eq_of_mem s.2.1 hω',
      ← ENNReal.eq_div_iff (hP' _ (P.class_mem ω')).ne' (measure_ne_top _ _), eq_comm]
    exact h _ (s.2.2 hω')
  · exact (Set.Pairwise.mono inter_subset_left P.2.pairwiseDisjoint).mono'
      (fun s t h ↦ h.mono inf_le_right inf_le_right)
  · exact Set.Pairwise.mono inter_subset_left P.2.pairwiseDisjoint

/-- Let `Ω` be a probability measure space, `P₁` and `P₂` two measurable partitions representing
the information partitions of two agents, `E` a measurable set and `ω` an event. Then if it is
common knowledge at `ω` that `E` appears to have probability `p₁` to the first agent and probability
`p₂` to the second agent, `p₁ = p₂` - that is, the two agents agree on the probability of `E`. -/
lemma agreeToDisagree {P₁ P₂ : Partition Ω} (hP₁ : P₁.Measurable) (hP₂ : P₂.Measurable)
    (hP₁' : ∀ s ∈ P₁, μ₁ s > 0) (hP₂' : ∀ s ∈ P₂, μ₂ s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p₁ p₂ : ENNReal}
    (h : (P₁ ⊔ P₂).class ω ⊆ {ω' | P₁.probabilityAt μ₁ E ω' = p₁ ∧ P₂.probabilityAt μ₂ E ω' = p₂})
    (h' : (P₁ ⊔ P₂).probabilityAt μ₁ E ω = (P₁ ⊔ P₂).probabilityAt μ₂ E ω) :
    p₁ = p₂ := by
  rw [← P₁.probabilityAt_eq_of_le hP₁ hP₁' le_sup_left hE ω (h.trans inter_subset_left),
    ← P₂.probabilityAt_eq_of_le hP₂ hP₂' le_sup_right hE ω (h.trans inter_subset_right)]
  exact h'

/-- Let `Ω` be a probability measure space, `P` a family of measurable partitions representing
the information partitions of agents indexed by a type `ι`, `E` a measurable set and `ω` an event.
Then if it is common knowledge at `ω` that `E` appears to have probability `p i` to each agent `i`,
`p i = p j` for all `i`, `j` - that is, all agents agree on the probability of `E`. -/
lemma agreeToDisagree' {ι : Type*} {μ : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)]
    {P : ι → Partition Ω} (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, μ i s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ι → ENNReal}
    (h : (⨆ i, P i).class ω ⊆ {ω' | ∀ i, (P i).probabilityAt (μ i) E ω' = p i})
    (h' : ∀ i j, (⨆ i, P i).probabilityAt (μ i) E ω = (⨆ i, P i).probabilityAt (μ j) E ω) :
    ∀ i j, p i = p j := by
  intro i j
  rw [← (P i).probabilityAt_eq_of_le (hP i) (hP' i) (le_iSup _ i) hE ω (fun ω' hω'↦ h hω' i),
    ← (P j).probabilityAt_eq_of_le (hP j) (hP' j) (le_iSup _ j) hE ω (fun ω' hω'↦ h hω' j)]
  exact h' i j

end AgreeToDisagree
