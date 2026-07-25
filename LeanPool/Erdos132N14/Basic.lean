/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Card

/-!
# Finite planar distance configurations

This module defines unordered index pairs, realized distances, their
multiplicities, and the low-multiplicity distances in Erdős Problem 132.
The definitions work on a selected finite subset of a labelled configuration,
which makes deletion and insertion statements literal finset identities.
-/

namespace LeanPool.Erdos132N14

open scoped BigOperators

noncomputable section

/-- A labelled finite planar configuration. -/
structure Configuration (ι : Type*) where
  /-- The planar point carrying a label. -/
  point : ι → ℂ
  injective : Function.Injective point

variable {ι κ : Type*} [LinearOrder ι]

/-- The unordered pairs in `S`, represented by their increasing orientation. -/
def pairs (S : Finset ι) : Finset (ι × ι) :=
  (S ×ˢ S).filter fun e ↦ e.1 < e.2

/-- The increasing representative of the unordered pair containing `v` and `w`. -/
def pairWith (v w : ι) : ι × ι :=
  if w < v then (w, v) else (v, w)

/-- The new unordered pairs created by inserting `v` into `S`. -/
def insertionPairs (v : ι) (S : Finset ι) : Finset (ι × ι) :=
  S.image (pairWith v)

theorem pairWith_injective (v : ι) : Function.Injective (pairWith v) := by
  intro a b hab
  by_cases ha : a < v <;> by_cases hb : b < v
  · simpa [pairWith, ha, hb] using congrArg Prod.fst hab
  · simp only [pairWith, ha, hb, if_pos] at hab
    have hav : a = v := congrArg Prod.fst hab
    exact (ne_of_lt ha hav).elim
  · simp only [pairWith, ha, hb, if_pos] at hab
    have hvb : v = b := congrArg Prod.fst hab
    exact (ne_of_gt hb hvb).elim
  · simpa [pairWith, ha, hb] using congrArg Prod.snd hab

theorem pairs_insert {v : ι} {S : Finset ι} (hv : v ∉ S) :
    pairs (insert v S) = pairs S ∪ insertionPairs v S := by
  ext e
  constructor
  · intro he
    have he' := Finset.mem_filter.mp he
    have hmembers := Finset.mem_product.mp he'.1
    rcases Finset.mem_insert.mp hmembers.1 with hfirst | hfirst
    · have hsecond : e.2 ∈ S := by
        rcases Finset.mem_insert.mp hmembers.2 with hsecond | hsecond
        · exact absurd (hfirst.trans hsecond.symm) (ne_of_lt he'.2)
        · exact hsecond
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨e.2, hsecond, ?_⟩
      have hnot : ¬e.2 < v := by simpa [hfirst] using (not_lt_of_ge (le_of_lt he'.2))
      apply Prod.ext
      · simp [pairWith, hfirst, hnot]
      · simp [pairWith, hnot]
    · rcases Finset.mem_insert.mp hmembers.2 with hsecond | hsecond
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨e.1, hfirst, ?_⟩
        have hlt : e.1 < v := by simpa [hsecond] using he'.2
        apply Prod.ext
        · simp [pairWith, hlt]
        · simp [pairWith, hlt, hsecond]
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hfirst, hsecond⟩, he'.2⟩)
  · intro he
    rcases Finset.mem_union.mp he with hold | hnew
    · have hold' := Finset.mem_filter.mp hold
      have hmembers := Finset.mem_product.mp hold'.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_insert_of_mem hmembers.1, Finset.mem_insert_of_mem hmembers.2⟩,
          hold'.2⟩
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hnew
      have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
      by_cases hlt : w < v
      · simp [pairs, pairWith, hlt, hw]
      · have hgt : v < w := lt_of_le_of_ne (le_of_not_gt hlt) hwv.symm
        simp [pairs, pairWith, hlt, hw, hgt]

theorem pairs_disjoint_insertionPairs {v : ι} {S : Finset ι} (hv : v ∉ S) :
    Disjoint (pairs S) (insertionPairs v S) := by
  refine Finset.disjoint_left.mpr ?_
  intro e hold hnew
  have hold' := Finset.mem_filter.mp hold
  have hmembers := Finset.mem_product.mp hold'.1
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hnew
  by_cases hlt : w < v
  · exact hv (by simpa [pairWith, hlt] using hmembers.2)
  · exact hv (by simpa [pairWith, hlt] using hmembers.1)

theorem pairWith_mem_pairs
    {S : Finset ι} {a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    pairWith a b ∈ pairs S := by
  by_cases hlt : b < a
  · simp [pairs, pairWith, hlt, ha, hb]
  · have hgt : a < b := lt_of_le_of_ne (le_of_not_gt hlt) hab
    simp [pairs, pairWith, hlt, ha, hb, hgt]

theorem pairWith_map_injectiveOn_orderedPairs
    [LinearOrder κ] (f : κ → ι) (hf : Function.Injective f) :
    Set.InjOn (fun e : κ × κ ↦ pairWith (f e.1) (f e.2)) {e | e.1 < e.2} := by
  intro e he g hg heq
  by_cases heOrder : f e.2 < f e.1 <;> by_cases hgOrder : f g.2 < f g.1
  · simp only [pairWith, heOrder, hgOrder, if_pos] at heq
    apply Prod.ext
    · exact hf (congrArg Prod.snd heq)
    · exact hf (congrArg Prod.fst heq)
  · simp only [pairWith, heOrder, hgOrder, if_pos] at heq
    have heSecond : e.2 = g.1 := hf (congrArg Prod.fst heq)
    have heFirst : e.1 = g.2 := hf (congrArg Prod.snd heq)
    exact ((not_lt_of_ge (heFirst ▸ heSecond ▸ hg.le)) he).elim
  · simp only [pairWith, heOrder, hgOrder, if_pos] at heq
    have heFirst : e.1 = g.2 := hf (congrArg Prod.fst heq)
    have heSecond : e.2 = g.1 := hf (congrArg Prod.snd heq)
    exact ((not_lt_of_ge (heFirst ▸ heSecond ▸ hg.le)) he).elim
  · simp only [pairWith, heOrder, hgOrder] at heq
    apply Prod.ext
    · exact hf (congrArg Prod.fst heq)
    · exact hf (congrArg Prod.snd heq)

namespace Configuration

/-- The Euclidean length belonging to an indexed pair. -/
def pairDistance (P : Configuration ι) (e : ι × ι) : ℝ :=
  dist (P.point e.1) (P.point e.2)

/-- The positive distances realized inside `S`. -/
def realizedDistances (P : Configuration ι) (S : Finset ι) : Finset ℝ :=
  (pairs S).image P.pairDistance

/-- The number of unordered pairs in `S` at distance `d`. -/
def distanceMultiplicity (P : Configuration ι) (S : Finset ι) (d : ℝ) : ℕ :=
  ((pairs S).filter fun e ↦ P.pairDistance e = d).card

/-- Realized distances represented by at most `threshold` unordered pairs. -/
def lowMultiplicityDistances
    (P : Configuration ι) (S : Finset ι) (threshold : ℕ) : Finset ℝ :=
  (P.realizedDistances S).filter fun d ↦ P.distanceMultiplicity S d ≤ threshold

theorem mem_realizedDistances_iff (P : Configuration ι) (S : Finset ι) (d : ℝ) :
    d ∈ P.realizedDistances S ↔
      ∃ e ∈ pairs S, P.pairDistance e = d := by
  simp [realizedDistances]

theorem distanceMultiplicity_pos_iff (P : Configuration ι) (S : Finset ι) (d : ℝ) :
    0 < P.distanceMultiplicity S d ↔ d ∈ P.realizedDistances S := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := Finset.card_pos.mp h
    exact (P.mem_realizedDistances_iff S d).mpr
      ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  · intro h
    obtain ⟨e, he, hed⟩ := (P.mem_realizedDistances_iff S d).mp h
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hed⟩⟩

theorem pairDistance_pos
    (P : Configuration ι) {S : Finset ι} {e : ι × ι} (he : e ∈ pairs S) :
    0 < P.pairDistance e := by
  have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
  exact dist_pos.mpr (P.injective.ne (ne_of_lt hlt))

theorem realizedDistance_pos
    (P : Configuration ι) {S : Finset ι} {d : ℝ}
    (hd : d ∈ P.realizedDistances S) :
    0 < d := by
  obtain ⟨e, he, rfl⟩ := (P.mem_realizedDistances_iff S d).mp hd
  exact P.pairDistance_pos he

theorem pairs_mono {S T : Finset ι} (hST : S ⊆ T) : pairs S ⊆ pairs T := by
  intro e he
  simp only [pairs, Finset.mem_filter, Finset.mem_product] at he ⊢
  exact ⟨⟨hST he.1.1, hST he.1.2⟩, he.2⟩

theorem realizedDistances_mono
    (P : Configuration ι) {S T : Finset ι} (hST : S ⊆ T) :
    P.realizedDistances S ⊆ P.realizedDistances T := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := (P.mem_realizedDistances_iff S d).mp hd
  exact (P.mem_realizedDistances_iff T _).mpr ⟨e, pairs_mono hST he, rfl⟩

theorem distanceMultiplicity_mono
    (P : Configuration ι) {S T : Finset ι} (hST : S ⊆ T) (d : ℝ) :
    P.distanceMultiplicity S d ≤ P.distanceMultiplicity T d := by
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  exact ⟨pairs_mono hST he.1, he.2⟩

/-- Multiplicities partition the unordered pairs. -/
theorem sum_distanceMultiplicity (P : Configuration ι) (S : Finset ι) :
    ∑ d ∈ P.realizedDistances S, P.distanceMultiplicity S d = (pairs S).card := by
  classical
  let D := P.realizedDistances S
  let E := {e // e ∈ pairs S}
  let distanceClass : E → D := fun e ↦
    ⟨P.pairDistance e, by
      dsimp [D]
      exact Finset.mem_image.mpr ⟨e, e.property, rfl⟩⟩
  have hpartition :=
    Finset.sum_fiberwise (Finset.univ : Finset E) distanceClass (fun _ ↦ (1 : ℕ))
  have hfiber (d : D) :
      ((Finset.univ : Finset E).filter fun e ↦ distanceClass e = d).card =
        P.distanceMultiplicity S d := by
    rw [distanceMultiplicity, Finset.card_filter, Finset.card_filter]
    simpa [D, E, distanceClass, Subtype.ext_iff] using
      (Finset.sum_attach (pairs S)
        fun e ↦ if P.pairDistance e = d then (1 : ℕ) else 0)
  have hsubtype :
      ∑ d : D, P.distanceMultiplicity S d = (pairs S).card := by
    calc
      ∑ d : D, P.distanceMultiplicity S d =
          ∑ d : D,
            ((Finset.univ : Finset E).filter fun e ↦ distanceClass e = d).card := by
        apply Finset.sum_congr rfl
        intro d _
        exact (hfiber d).symm
      _ = (pairs S).card := by simpa [E] using hpartition
  change ∑ d ∈ D, P.distanceMultiplicity S d = (pairs S).card
  calc
    ∑ d ∈ D, P.distanceMultiplicity S d =
        ∑ d : D, P.distanceMultiplicity S d := by
      apply Finset.sum_subtype
      simp
    _ = (pairs S).card := hsubtype

/-- Number of new edges of length `d` created by inserting `v` into `S`. -/
def insertionMultiplicity
    (P : Configuration ι) (v : ι) (S : Finset ι) (d : ℝ) : ℕ :=
  (S.filter fun w ↦ dist (P.point v) (P.point w) = d).card

theorem pairDistance_pairWith (P : Configuration ι) (v w : ι) :
    P.pairDistance (pairWith v w) = dist (P.point v) (P.point w) := by
  by_cases h : w < v
  · simp [pairDistance, pairWith, h, dist_comm]
  · simp [pairDistance, pairWith, h]

theorem filter_insertionPairs
    (P : Configuration ι) (v : ι) (S : Finset ι) (d : ℝ) :
    (insertionPairs v S).filter (fun e ↦ P.pairDistance e = d) =
      (S.filter fun w ↦ dist (P.point v) (P.point w) = d).image (pairWith v) := by
  ext e
  constructor
  · intro he
    have he' := Finset.mem_filter.mp he
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp he'.1
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_filter.mpr ⟨hw, ?_⟩, hwe⟩
    rw [← P.pairDistance_pairWith v w, hwe]
    exact he'.2
  · intro he
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨w, (Finset.mem_filter.mp hw).1, hwe⟩, ?_⟩
    rw [← hwe, P.pairDistance_pairWith]
    exact (Finset.mem_filter.mp hw).2

/-- Exact insertion formula for distance multiplicity. -/
theorem distanceMultiplicity_insert
    (P : Configuration ι) {v : ι} {S : Finset ι} (hv : v ∉ S) (d : ℝ) :
    P.distanceMultiplicity (insert v S) d =
      P.distanceMultiplicity S d + P.insertionMultiplicity v S d := by
  rw [distanceMultiplicity, pairs_insert hv, Finset.filter_union]
  rw [Finset.card_union_of_disjoint]
  · rw [filter_insertionPairs]
    exact congrArg (P.distanceMultiplicity S d + ·)
      (Finset.card_image_of_injective _ (pairWith_injective v))
  · apply Finset.disjoint_left.mpr
    intro e hold hnew
    exact Finset.disjoint_left.mp (pairs_disjoint_insertionPairs hv)
      (Finset.mem_filter.mp hold).1 (Finset.mem_filter.mp hnew).1

end Configuration

/-- A distance-scaling equivalence of the Euclidean plane. -/
structure PlaneSimilarity where
  /-- The underlying bijection of the plane. -/
  toEquiv : ℂ ≃ ℂ
  /-- The positive distance scale factor. -/
  ratio : ℝ
  ratio_pos : 0 < ratio
  map_dist : ∀ x y, dist (toEquiv x) (toEquiv y) = ratio * dist x y

instance : CoeFun PlaneSimilarity fun _ ↦ ℂ → ℂ :=
  ⟨fun f ↦ f.toEquiv⟩

/-- A selected configuration is a relabelled Euclidean similarity image of a template. -/
structure SimilarTo
    (P : Configuration ι) (S : Finset ι) {κ : Type*} (template : κ → ℂ) where
  /-- A relabelling from the template onto the selected points. -/
  reindex : κ ≃ {i // i ∈ S}
  /-- The Euclidean similarity carrying the template to the selection. -/
  similarity : PlaneSimilarity
  point_eq : ∀ i, P.point (reindex i) = similarity (template i)

theorem PlaneSimilarity.injective (f : PlaneSimilarity) : Function.Injective f := by
  exact f.toEquiv.injective

omit [LinearOrder ι] in
theorem SimilarTo.distance_eq
    {S : Finset ι} {template : κ → ℂ}
    (h : SimilarTo P S template) (i j : κ) :
    dist (P.point (h.reindex i)) (P.point (h.reindex j)) =
      h.similarity.ratio * dist (template i) (template j) := by
  rw [h.point_eq, h.point_eq, h.similarity.map_dist]

/-- A Euclidean similarity injects every template distance class into the
corresponding scaled class of the selected configuration. -/
theorem SimilarTo.distanceMultiplicity_le
    [Fintype κ] [LinearOrder κ]
    {S : Finset ι} (Q : Configuration κ) (h : SimilarTo P S Q.point) (d : ℝ) :
    Q.distanceMultiplicity Finset.univ d ≤
      P.distanceMultiplicity S (h.similarity.ratio * d) := by
  let indexMap : κ → ι := fun i ↦ h.reindex i
  have hindexMap : Function.Injective indexMap := by
    intro i j hij
    apply h.reindex.injective
    exact Subtype.ext hij
  let edgeMap : κ × κ → ι × ι := fun e ↦ pairWith (indexMap e.1) (indexMap e.2)
  apply Finset.card_le_card_of_injOn edgeMap
  · intro e he
    have he' := Finset.mem_filter.mp he
    have hmembers := Finset.mem_product.mp (Finset.mem_filter.mp he'.1).1
    apply Finset.mem_filter.mpr
    refine ⟨pairWith_mem_pairs (h.reindex e.1).property (h.reindex e.2).property ?_, ?_⟩
    · intro heq
      exact (ne_of_lt (Finset.mem_filter.mp he'.1).2) (hindexMap heq)
    · rw [Configuration.pairDistance_pairWith, h.distance_eq]
      exact congrArg (h.similarity.ratio * ·) he'.2
  · intro e he g hg heq
    apply pairWith_map_injectiveOn_orderedPairs indexMap hindexMap
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).2
    · exact heq

/-- Euclidean similarities preserve every distance multiplicity exactly. -/
theorem SimilarTo.distanceMultiplicity_eq
    [Fintype κ] [LinearOrder κ]
    {S : Finset ι} (Q : Configuration κ) (h : SimilarTo P S Q.point) (d : ℝ) :
    P.distanceMultiplicity S (h.similarity.ratio * d) =
      Q.distanceMultiplicity Finset.univ d := by
  rw [Configuration.distanceMultiplicity, Configuration.distanceMultiplicity]
  let indexMap : κ → ι := fun i ↦ h.reindex i
  have hindexMap : Function.Injective indexMap := by
    intro i j hij
    apply h.reindex.injective
    exact Subtype.ext hij
  let edgeMap : κ × κ → ι × ι := fun e ↦
    pairWith (indexMap e.1) (indexMap e.2)
  symm
  apply Finset.card_bij (fun e _ ↦ edgeMap e)
  · intro e he
    have he' := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨pairWith_mem_pairs (h.reindex e.1).property
      (h.reindex e.2).property ?_, ?_⟩
    · intro heq
      exact (ne_of_lt (Finset.mem_filter.mp he'.1).2) (hindexMap heq)
    · rw [Configuration.pairDistance_pairWith, h.distance_eq]
      exact congrArg (h.similarity.ratio * ·) he'.2
  · intro e he g hg heq
    apply pairWith_map_injectiveOn_orderedPairs indexMap hindexMap
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).2
    · exact heq
  · intro e he
    have he' := Finset.mem_filter.mp he
    have hePairs := Finset.mem_filter.mp he'.1
    have heMembers := Finset.mem_product.mp hePairs.1
    let i := h.reindex.symm ⟨e.1, heMembers.1⟩
    let j := h.reindex.symm ⟨e.2, heMembers.2⟩
    have hi : (h.reindex i).val = e.1 := by
      exact congrArg Subtype.val
        (h.reindex.apply_symm_apply ⟨e.1, heMembers.1⟩)
    have hj : (h.reindex j).val = e.2 := by
      exact congrArg Subtype.val
        (h.reindex.apply_symm_apply ⟨e.2, heMembers.2⟩)
    have hij : i ≠ j := by
      intro hij
      apply ne_of_lt hePairs.2
      rw [← hi, ← hj, hij]
    refine ⟨pairWith i j, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨pairWith_mem_pairs (Finset.mem_univ i) (Finset.mem_univ j) hij, ?_⟩
      rw [Q.pairDistance_pairWith]
      have hdistance := h.distance_eq i j
      rw [hi, hj] at hdistance
      have heDistance : dist (P.point e.1) (P.point e.2) =
          h.similarity.ratio * d := by
        simpa [Configuration.pairDistance] using he'.2
      apply mul_left_cancel₀ (ne_of_gt h.similarity.ratio_pos)
      exact hdistance.symm.trans heDistance
    · dsimp [edgeMap, indexMap]
      by_cases hji : j < i
      · rw [show pairWith i j = (j, i) by simp [pairWith, hji]]
        dsimp
        rw [hi, hj]
        simp [pairWith, hePairs.2]
      · rw [show pairWith i j = (i, j) by simp [pairWith, hji]]
        dsimp
        rw [hi, hj]
        simp [pairWith, not_lt_of_ge hePairs.2.le]

end

end LeanPool.Erdos132N14
