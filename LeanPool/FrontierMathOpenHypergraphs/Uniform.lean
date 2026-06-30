/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/

import LeanPool.FrontierMathOpenHypergraphs.Uniform.Frames

/-!
# The uniform 26/25 factor and the finite bootstrap
-/

namespace HypergraphLowerBound

local macro "eval_A_small" : tactic =>
  `(tactic| (
    first
    | rw [Fin.sum_univ_two]
    | rw [Fin.sum_univ_three]
    | rw [Fin.sum_univ_four]
    | skip
    try unfold A
    first | rfl | decide | omega))

local macro "eval_Ak_small" : tactic =>
  `(tactic| (unfold A; norm_num [bootstrapValues, k]))

private theorem core4Spec_valid : core4Spec.IsValid := by
  decide

private theorem core4Spec_cap_eq_three (i : Fin 4) : core4Spec.cap i = 3 := by
  fin_cases i <;> decide

private theorem core4Spec_bonus_eq : core4Spec.bonus = 13 := by
  decide

private lemma FrameSpec.supportList_length (spec : FrameSpec) :
    spec.supportList.length = spec.bonus := by
  simp [FrameSpec.supportList, FrameSpec.bonus]

private lemma FrameSpec.supports_card (spec : FrameSpec) :
    spec.supports.card = spec.bonus := by
  simp [FrameSpec.supports, spec.supportList_length]

private def SupportsValid {t : ℕ}
    (l : List (SupportPattern t)) (cap : Fin t → ℕ) : Prop :=
  ∀ T I : Finset (Fin t), I ⊆ T →
    l.countP (frameWitnesses T I) ≤ (T \ I).sum cap

private theorem SupportsValid.ofSpec (spec : FrameSpec) :
    SupportsValid spec.supportList spec.cap ↔ spec.IsValid := by
  rfl

private theorem SupportsValid.toIsFrame {t : ℕ}
    {l : List (SupportPattern t)} {cap : Fin t → ℕ}
    (h : SupportsValid l cap) :
    IsFrame (l : Multiset (SupportPattern t)) cap := by
  intro T I hIT
  rw [omegaCount_coe_eq_countP]
  exact h T I hIT

private theorem SupportsValid.append {t : ℕ}
    {l₁ l₂ : List (SupportPattern t)}
    {cap₁ cap₂ : Fin t → ℕ}
    (h₁ : SupportsValid l₁ cap₁)
    (h₂ : SupportsValid l₂ cap₂) :
    SupportsValid (l₁ ++ l₂) (fun i => cap₁ i + cap₂ i) := by
  intro T I hIT
  calc
    (l₁ ++ l₂).countP (frameWitnesses T I)
        = l₁.countP (frameWitnesses T I) + l₂.countP (frameWitnesses T I) := by
            simp [List.countP_append]
    _ ≤ (T \ I).sum cap₁ + (T \ I).sum cap₂ := by
          exact Nat.add_le_add (h₁ T I hIT) (h₂ T I hIT)
    _ = (T \ I).sum (fun i => cap₁ i + cap₂ i) := by
          symm
          exact Finset.sum_add_distrib

private def EdgesNonempty {V : Type*} (edges : Hypergraph V) : Prop :=
  ∀ e ∈ edges, e.Nonempty

private def mapHypergraph {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (edges : Finset (Finset α)) : Finset (Finset β) :=
  edges.image (fun e => e.image f)

private theorem edgeImage_injective {α β : Type*} [DecidableEq β]
    (f : α ↪ β) : Function.Injective (fun e : Finset α => e.image f) := by
  intro e e' h
  ext x
  constructor
  · intro hx
    have hxImg : f x ∈ e.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hx' : f x ∈ e'.image f := by
      simpa [h] using hxImg
    rcases Finset.mem_image.mp hx' with ⟨y, hy, hyx⟩
    have : y = x := f.injective hyx
    simpa [this] using hy
  · intro hx
    have hxImg : f x ∈ e'.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hx' : f x ∈ e.image f := by
      simpa [h] using hxImg
    rcases Finset.mem_image.mp hx' with ⟨y, hy, hyx⟩
    have : y = x := f.injective hyx
    simpa [this] using hy

private theorem mapHypergraph_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (edges : Finset (Finset α)) :
    (mapHypergraph f edges).card = edges.card := by
  simpa [mapHypergraph] using Finset.card_image_of_injective edges (edgeImage_injective f)

private theorem vertexSet_mapHypergraph {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (edges : Finset (Finset α)) :
    vertexSet (mapHypergraph f edges) = (vertexSet edges).image f := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_biUnion.mp hy with ⟨E, hE, hyE⟩
    rcases Finset.mem_image.mp hE with ⟨e, he, rfl⟩
    rcases Finset.mem_image.mp hyE with ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_biUnion.mpr ⟨e, he, hx⟩, rfl⟩
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_biUnion.mp hx with ⟨e, he, hxE⟩
    exact Finset.mem_biUnion.mpr ⟨e.image f, Finset.mem_image.mpr ⟨e, he, rfl⟩,
      Finset.mem_image.mpr ⟨x, hxE, rfl⟩⟩

private theorem mapHypergraph_vertexSet_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (edges : Finset (Finset α)) :
    (vertexSet (mapHypergraph f edges)).card = (vertexSet edges).card := by
  rw [vertexSet_mapHypergraph]
  exact Finset.card_image_of_injective _ f.injective

private lemma mapHypergraph_filter_mem_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (Q : Finset (Finset α)) (x : α) :
    (mapHypergraph f Q).filter (fun E => f x ∈ E) =
      mapHypergraph f (Q.filter fun e => x ∈ e) := by
  ext E
  constructor
  · intro hE
    rcases Finset.mem_filter.mp hE with ⟨hEmap, hxE⟩
    rcases Finset.mem_image.mp hEmap with ⟨e, heQ, rfl⟩
    rcases Finset.mem_image.mp hxE with ⟨y, hy, hyx⟩
    have : y = x := f.injective hyx
    exact Finset.mem_image.mpr
      ⟨e, Finset.mem_filter.mpr ⟨heQ, by simpa [this] using hy⟩, rfl⟩
  · intro hE
    rcases Finset.mem_image.mp hE with ⟨e, he, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩
    · exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp he).2, rfl⟩

private lemma card_filter_mapHypergraph_mem {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (Q : Finset (Finset α)) (x : α) :
    ((mapHypergraph f Q).filter fun E => f x ∈ E).card =
      (Q.filter fun e => x ∈ e).card := by
  rw [mapHypergraph_filter_mem_eq, mapHypergraph_card]

private theorem uniqueCoverage_mapHypergraph {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (edges Q : Finset (Finset α)) :
    uniqueCoverage (mapHypergraph f edges) (mapHypergraph f Q) =
      uniqueCoverage edges Q := by
  unfold uniqueCoverage
  have hset :
      (vertexSet (mapHypergraph f edges)).filter
          (fun y => ((mapHypergraph f Q).filter fun E => y ∈ E).card = 1) =
        ((vertexSet edges).filter
          (fun x => ((Q.filter fun e => x ∈ e).card = 1))).image f := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_filter.mp hy with ⟨hyv, hy1⟩
      rw [vertexSet_mapHypergraph] at hyv
      rcases Finset.mem_image.mp hyv with ⟨x, hxv, rfl⟩
      refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxv, ?_⟩, rfl⟩
      simpa [card_filter_mapHypergraph_mem f Q x] using hy1
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      rcases Finset.mem_filter.mp hx with ⟨hxv, hx1⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [vertexSet_mapHypergraph]
        exact Finset.mem_image.mpr ⟨x, hxv, rfl⟩
      · simpa [card_filter_mapHypergraph_mem f Q x] using hx1
  rw [hset, Finset.card_image_of_injective]
  exact f.injective

private theorem NoLargePartition.map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {edges : Finset (Finset α)} {n : ℕ}
    (h : NoLargePartition edges n) (f : α ↪ β) :
    NoLargePartition (mapHypergraph f edges) n := by
  intro P hP
  let Q : Finset (Finset α) := edges.filter fun e => e.image f ∈ P
  have hQsub : Q ⊆ edges := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hP_eq : mapHypergraph f Q = P := by
    ext E
    constructor
    · intro hE
      rcases Finset.mem_image.mp hE with ⟨e, heQ, hEq⟩
      exact hEq ▸ (Finset.mem_filter.mp heQ).2
    · intro hE
      have hEmap : E ∈ mapHypergraph f edges := hP hE
      rcases Finset.mem_image.mp hEmap with ⟨e, he, hEq⟩
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hEq ▸ hE⟩, hEq⟩
  have hQ := h Q hQsub
  rw [← hP_eq, uniqueCoverage_mapHypergraph]
  exact hQ

private theorem EdgesNonempty.map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {edges : Finset (Finset α)} (h : ∀ e ∈ edges, e.Nonempty) (f : α ↪ β) :
    ∀ E ∈ mapHypergraph f edges, E.Nonempty := by
  intro E hE
  rcases Finset.mem_image.mp hE with ⟨e, he, rfl⟩
  rcases h e he with ⟨x, hx⟩
  exact ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

private def blockEmb {t : ℕ} (i : Fin t) : ℕ ↪ ℕ where
  toFun := fun v => Nat.pair i.1 v
  inj' := by
    intro v w h
    exact (Nat.pair_eq_pair.mp h).2

private def encodeSubstVertex {t : ℕ}
    (F : Multiset (SupportPattern t)) : SubstVertex t F ↪ ℕ where
  toFun
    | .old i v => Nat.pair 0 (Nat.pair i.1 v)
    | .new s => Nat.pair 1 s.1
  inj' := by
    intro x y h
    cases x with
    | old i v =>
        cases y with
        | old j w =>
            rcases Nat.pair_eq_pair.mp h with ⟨_, hinner⟩
            rcases Nat.pair_eq_pair.mp hinner with ⟨hij, hvw⟩
            have hij' : i = j := Fin.ext hij
            subst hij'
            subst hvw
            rfl
        | new s =>
            have : (0 : ℕ) = 1 := (Nat.pair_eq_pair.mp h).1
            omega
    | new s =>
        cases y with
        | old i v =>
            have : (1 : ℕ) = 0 := (Nat.pair_eq_pair.mp h).1
            omega
        | new s' =>
            exact congrArg SubstVertex.new (Fin.ext ((Nat.pair_eq_pair.mp h).2))

private theorem substitution_edgesNonempty {t : ℕ}
    (F : Multiset (SupportPattern t))
    (blocks : BlockFamily t)
    (h : ∀ i, EdgesNonempty (blocks i)) :
    EdgesNonempty (substitutionHypergraph F blocks) := by
  intro E hE
  rcases Finset.mem_biUnion.mp hE with ⟨i, -, hEi⟩
  rcases Finset.mem_image.mp hEi with ⟨e, he, rfl⟩
  rcases h i e he with ⟨v, hv⟩
  exact ⟨SubstVertex.old i v, by
    simp [liftBlockEdge, hv]⟩

/-- A concrete witness hypergraph with prescribed edge and vertex counts. -/
structure Witness (edgeCount vertexCount : ℕ) where
  /-- The witness hypergraph. -/
  edges : Hypergraph ℕ
  /-- The witness has the prescribed number of edges. -/
  edgeCard : edges.card = edgeCount
  /-- The witness has the prescribed number of vertices. -/
  vertexCard : (vertexSet edges).card = vertexCount
  /-- The witness satisfies the no-large-partition obstruction. -/
  noLargePartition : NoLargePartition edges edgeCount

/-- A witness together with the auxiliary fact that every edge is nonempty. -/
private def WitnessStrong (edgeCount vertexCount : ℕ) : Prop :=
  ∃ w : Witness edgeCount vertexCount, EdgesNonempty w.edges

/-- Forget the auxiliary nonemptiness data and retain only the public witness fields. -/
private noncomputable def WitnessStrong.toWitnessData {edgeCount vertexCount : ℕ}
    (w : WitnessStrong edgeCount vertexCount) : Witness edgeCount vertexCount :=
  Classical.choose w

/-- The nonempty-edge part of a strong witness. -/
private theorem WitnessStrong.edgesNonempty {edgeCount vertexCount : ℕ}
    (w : WitnessStrong edgeCount vertexCount) :
    EdgesNonempty w.toWitnessData.edges :=
  Classical.choose_spec w

/-- The pointwise witness package used in the main `26/25` theorem. -/
private structure MainPointwiseWitness (n : ℕ) where
  witness : Witness n (A n)
  lowerBound : 15 ≤ n → 25 * (vertexSet witness.edges).card ≥ 26 * k n

/-- A packaged witness family for the sequence-level form of the main theorem. -/
structure WitnessFamily (G : ℕ → Hypergraph ℕ) : Prop where
  edgeCard : ∀ n, 1 ≤ n → (G n).card = n
  noLargePartition : ∀ n, 1 ≤ n → NoLargePartition (G n) n
  lowerBoundWitness : ∀ n, 15 ≤ n → 25 * (vertexSet (G n)).card ≥ 26 * k n
  lowerBoundH : ∀ n, 15 ≤ n → 25 * H n ≥ 26 * k n

private lemma sum_get_eq_sum (l : List ℕ) :
    ((Finset.univ : Finset (Fin l.length)).sum fun i => l.get i) = l.sum := by
  simp

private lemma sum_map_get_eq_sum_map (l : List ℕ) (f : ℕ → ℕ) :
    ((Finset.univ : Finset (Fin l.length)).sum fun i => f (l.get i)) = (l.map f).sum := by
  simp

private theorem apply_frameData {t : ℕ}
    (F : Multiset (SupportPattern t))
    (edgeCounts vertexCounts : Fin t → ℕ)
    (bonus : ℕ)
    (hBonus : F.card = bonus)
    (hFrame : IsFrame F edgeCounts)
    (hw : ∀ i, WitnessStrong (edgeCounts i) (vertexCounts i)) :
    WitnessStrong ((Finset.univ : Finset (Fin t)).sum edgeCounts)
      (((Finset.univ : Finset (Fin t)).sum vertexCounts) + bonus) := by
  classical
  choose childWitness hNonempty using hw
  let childEdges : Fin t → Hypergraph ℕ := fun i => (childWitness i).edges
  let blocks : BlockFamily t := fun i =>
    mapHypergraph (blockEmb i) (childEdges i)
  have hVertexDisjoint : Pairwise fun i j =>
      Disjoint (vertexSet (blocks i)) (vertexSet (blocks j)) := by
    intro i j hij
    rw [vertexSet_mapHypergraph, vertexSet_mapHypergraph]
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨w, hw, hEq⟩
    exact hij (Fin.ext (Nat.pair_eq_pair.mp hEq).1.symm)
  have hEdgeDisjoint : Pairwise fun i j => Disjoint (blocks i) (blocks j) := by
    intro i j hij
    refine Finset.disjoint_left.mpr ?_
    intro E hEi hEj
    rcases Finset.mem_image.mp hEi with ⟨e, he, rfl⟩
    rcases Finset.mem_image.mp hEj with ⟨e', he', hEq⟩
    rcases hNonempty i e he with ⟨v, hv⟩
    have hxImg : Nat.pair i.1 v ∈ e.image (blockEmb i) :=
      Finset.mem_image.mpr ⟨v, hv, rfl⟩
    have hmem : Nat.pair i.1 v ∈ e'.image (blockEmb j) := by
      simpa [hEq] using hxImg
    rcases Finset.mem_image.mp hmem with ⟨w, hw, hPair⟩
    exact hij (Fin.ext (Nat.pair_eq_pair.mp hPair).1.symm)
  have hEdgeCounts : ∀ i, (blocks i).card = edgeCounts i := by
    intro i
    calc
      (blocks i).card = (childEdges i).card := mapHypergraph_card (blockEmb i) (childEdges i)
      _ = edgeCounts i := (childWitness i).edgeCard
  have hVertexCounts : ∀ i, (vertexSet (blocks i)).card = vertexCounts i := by
    intro i
    calc
      (vertexSet (blocks i)).card = (vertexSet (childEdges i)).card :=
        mapHypergraph_vertexSet_card (blockEmb i) (childEdges i)
      _ = vertexCounts i := (childWitness i).vertexCard
  have hPartition : ∀ i, NoLargePartition (blocks i) (edgeCounts i) := by
    intro i
    exact NoLargePartition.map ((childWitness i).noLargePartition) (blockEmb i)
  have hBlocks : CountedBlocks edgeCounts vertexCounts blocks := by
    refine
      { vertexDisjoint := hVertexDisjoint
        edgeDisjoint := hEdgeDisjoint
        partitionBound := hPartition
        edgeCard := hEdgeCounts
        vertexCard := hVertexCounts }
  obtain ⟨hCardSubst, hVertexSubst, hPartSubst⟩ := frame_recurrence
    F edgeCounts vertexCounts blocks hFrame hBlocks
  have hBlocksNonempty : ∀ i, EdgesNonempty (blocks i) := by
    intro i
    exact EdgesNonempty.map (h := hNonempty i) (blockEmb i)
  refine ⟨{
      edges := mapHypergraph (encodeSubstVertex F) (substitutionHypergraph F blocks)
      edgeCard := ?_
      vertexCard := ?_
      noLargePartition := ?_ }, ?_⟩
  · calc
      (mapHypergraph (encodeSubstVertex F) (substitutionHypergraph F blocks)).card
          = (substitutionHypergraph F blocks).card := by
              exact mapHypergraph_card (encodeSubstVertex F) (substitutionHypergraph F blocks)
      _ = ((Finset.univ : Finset (Fin t)).sum edgeCounts) := hCardSubst
  · calc
      (vertexSet (mapHypergraph (encodeSubstVertex F) (substitutionHypergraph F blocks))).card
          = (vertexSet (substitutionHypergraph F blocks)).card := by
              exact mapHypergraph_vertexSet_card (encodeSubstVertex F)
                (substitutionHypergraph F blocks)
      _ = ((Finset.univ : Finset (Fin t)).sum vertexCounts) + F.card := hVertexSubst
      _ = ((Finset.univ : Finset (Fin t)).sum vertexCounts) + bonus := by simp [hBonus]
  · exact NoLargePartition.map hPartSubst (encodeSubstVertex F)
  · exact EdgesNonempty.map
      (h := substitution_edgesNonempty F blocks hBlocksNonempty) (encodeSubstVertex F)

private def pairSupport : SupportPattern 2 :=
  ⟨({0, 1} : Finset (Fin 2)), by decide⟩

private def binarySupports (c : ℕ) : Multiset (SupportPattern 2) :=
  List.replicate c pairSupport

private def binaryCap (a b : ℕ) : Fin 2 → ℕ
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

private def binaryValues (a b : ℕ) : Fin 2 → ℕ
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

private theorem binary_isFrame (a b c : ℕ) (hc : c ≤ min a b) :
    IsFrame (binarySupports c) (binaryCap a b) := by
  simpa [binarySupports] using
    (SupportsValid.toIsFrame (l := List.replicate c pairSupport) (cap := binaryCap a b) (by
      intro T I hIT
      have hcount :
          ∀ n, (List.replicate n pairSupport).countP (frameWitnesses T I) =
            if frameWitnesses T I pairSupport then n else 0 := by
        intro n
        induction n with
        | zero =>
            simp
          | succ n ih =>
              by_cases hw : frameWitnesses T I pairSupport <;> simp [List.replicate, ih, hw]
      have hpair_subset :
          (({0, 1} : Finset (Fin 2)) ⊆ T) ↔ ((0 : Fin 2) ∈ T ∧ (1 : Fin 2) ∈ T) := by
        constructor
        · intro h
          exact ⟨h (by simp), h (by simp)⟩
        · rintro ⟨h0, h1⟩ x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact h0
          · exact h1
      have hsum :
          (if (0 : Fin 2) ∈ T \ I then a else 0) +
            (if (1 : Fin 2) ∈ T \ I then b else 0) =
              (T \ I).sum (binaryCap a b) := by
        simpa [Fin.sum_univ_two, binaryCap] using
          (Finset.sum_ite_mem_eq (s := T \ I) (f := binaryCap a b))
      rw [hcount c]
      rw [← hsum]
      by_cases hT0 : (0 : Fin 2) ∈ T <;> by_cases hT1 : (1 : Fin 2) ∈ T <;>
        by_cases hI0 : (0 : Fin 2) ∈ I <;> by_cases hI1 : (1 : Fin 2) ∈ I <;>
        simp [hpair_subset, pairSupport, frameWitnesses, hT0, hT1, hI0, hI1] at hIT ⊢ <;>
        omega))

/-! ## Four-way identities for k_n -/

private lemma k_unfold (n : ℕ) :
    k (n + 2) = (n + 2) / 2 + k ((n + 2) / 2) + k ((n + 3) / 2) := by
  conv_lhs => unfold k

private lemma k_two_mul (m : ℕ) (hm : 1 ≤ m) : k (2 * m) = m + 2 * k m := by
  have h : 2 * m = (2 * m - 2) + 2 := by omega
  conv_lhs => rw [h]
  rw [k_unfold]
  have h1 : (2 * m - 2 + 2) / 2 = m := by omega
  have h2 : (2 * m - 2 + 3) / 2 = m := by omega
  rw [h1, h2]
  ring

private lemma k_two_mul_succ (m : ℕ) (hm : 1 ≤ m) :
    k (2 * m + 1) = m + k m + k (m + 1) := by
  have h : 2 * m + 1 = (2 * m - 1) + 2 := by omega
  conv_lhs => rw [h]
  rw [k_unfold]
  have h1 : (2 * m - 1 + 2) / 2 = m := by omega
  have h2 : (2 * m - 1 + 3) / 2 = m + 1 := by omega
  rw [h1, h2]

/-- The four-way identities satisfied by k_n. -/
theorem k_four_way (m : ℕ) (hm : 1 ≤ m) :
    k (4 * m) = 4 * k m + 4 * m ∧
    k (4 * m + 1) = 3 * k m + k (m + 1) + 4 * m ∧
    k (4 * m + 2) = 2 * k m + 2 * k (m + 1) + 4 * m + 1 ∧
    k (4 * m + 3) = k m + 3 * k (m + 1) + 4 * m + 2 := by
  have h2m : 1 ≤ 2 * m := by omega
  have h2m1 : 1 ≤ 2 * m + 1 := by omega
  have hm1 : 1 ≤ m + 1 := by omega
  have hk2m : k (2 * m) = m + 2 * k m := k_two_mul m hm
  have hk2m1 : k (2 * m + 1) = m + k m + k (m + 1) := k_two_mul_succ m hm
  have hk2m2 : k (2 * (m + 1)) = (m + 1) + 2 * k (m + 1) := k_two_mul (m + 1) hm1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- k(4m) = 4*k(m) + 4*m
    have : k (4 * m) = k (2 * (2 * m)) := by ring_nf
    rw [this, k_two_mul (2 * m) h2m, hk2m]
    ring
  · -- k(4m+1) = 3*k(m) + k(m+1) + 4*m
    have : k (4 * m + 1) = k (2 * (2 * m) + 1) := by ring_nf
    rw [this, k_two_mul_succ (2 * m) h2m, hk2m, hk2m1]
    ring
  · -- k(4m+2) = 2*k(m) + 2*k(m+1) + 4*m + 1
    have : k (4 * m + 2) = k (2 * (2 * m + 1)) := by ring_nf
    rw [this, k_two_mul (2 * m + 1) h2m1, hk2m1]
    omega
  · -- k(4m+3) = k(m) + 3*k(m+1) + 4*m + 2
    have : k (4 * m + 3) = k (2 * (2 * m + 1) + 1) := by ring_nf
    rw [this, k_two_mul_succ (2 * m + 1) h2m1, hk2m1]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by ring]
    rw [hk2m2]
    omega

/-! ## The floor inequalities -/

/-- The bonus e_r(m) ≥ (26/25) × (additive term) for m ≥ 15. -/
theorem floor_26_25 (m : ℕ) (hm : 15 ≤ m) :
    25 * eBonus 0 m ≥ 26 * (4 * m) ∧
    25 * eBonus 1 m ≥ 26 * (4 * m) ∧
    25 * eBonus 2 m ≥ 26 * (4 * m + 1) ∧
    25 * eBonus 3 m ≥ 26 * (4 * m + 2) := by
  simp only [eBonus]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := Nat.div_add_mod (13 * m) 3
    have hmod := Nat.mod_lt (13 * m) (by norm_num : 0 < 3)
    omega
  · have h := Nat.div_add_mod (13 * m + 1) 3
    have hmod := Nat.mod_lt (13 * m + 1) (by norm_num : 0 < 3)
    omega
  · have h := Nat.div_add_mod (13 * m + 5) 3
    have hmod := Nat.mod_lt (13 * m + 5) (by norm_num : 0 < 3)
    omega
  · have h := Nat.div_add_mod (13 * m + 6) 3
    have hmod := Nat.mod_lt (13 * m + 6) (by norm_num : 0 < 3)
    omega

/-! ## The finite bootstrap -/

/-- For 15 ≤ n < 60, 25 * A_n ≥ 26 * k_n, with equality exactly at n = 17. -/
theorem bootstrap_26_25 (n : ℕ) (h1 : 15 ≤ n) (h2 : n < 60) :
    25 * A n ≥ 26 * k n ∧ (25 * A n = 26 * k n ↔ n = 17) := by
  interval_cases n <;> eval_Ak_small

/-! ## Unfolding A for large n -/

private lemma A_mod0 (n : ℕ) (hn : 60 ≤ n) (hr : n % 4 = 0) :
    A n = A (n / 4) + A (n / 4) + A (n / 4) + A (n / 4) + eBonus 0 (n / 4) := by
  have h1 : n ≠ 0 := by omega
  have h2 : ¬(n < 60) := by omega
  conv_lhs => unfold A
  simp only [h1, h2, ↓reduceIte, hr]

private lemma A_mod1 (n : ℕ) (hn : 60 ≤ n) (hr : n % 4 = 1) :
    A n = A (n / 4) + A (n / 4) + A (n / 4) + A (n / 4 + 1) + eBonus 1 (n / 4) := by
  have h1 : n ≠ 0 := by omega
  have h2 : ¬(n < 60) := by omega
  conv_lhs => unfold A
  simp only [h1, h2, ↓reduceIte, hr]

private lemma A_mod2 (n : ℕ) (hn : 60 ≤ n) (hr : n % 4 = 2) :
    A n = A (n / 4) + A (n / 4) + A (n / 4 + 1) + A (n / 4 + 1) + eBonus 2 (n / 4) := by
  have h1 : n ≠ 0 := by omega
  have h2 : ¬(n < 60) := by omega
  conv_lhs => unfold A
  simp only [h1, h2, ↓reduceIte, hr]

private lemma A_mod3 (n : ℕ) (hn : 60 ≤ n) (hr : n % 4 = 3) :
    A n = A (n / 4) + A (n / 4 + 1) + A (n / 4 + 1) + A (n / 4 + 1) + eBonus 3 (n / 4) := by
  have h1 : n ≠ 0 := by omega
  have h2 : ¬(n < 60) := by omega
  conv_lhs => unfold A
  simp only [h1, h2, ↓reduceIte, hr]

private lemma q_mul_three_add_mod (m q : ℕ) (hq : q = m / 3) :
    q * 3 + m % 3 = m := by
  subst q
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.mod_add_div m 3)

private lemma four_mul_div_add_mod (n m : ℕ) (hm : m = n / 4) :
    4 * m + n % 4 = n := by
  subst m
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.mod_add_div n 4)

private lemma q_mul_three_add_two (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 2) :
    q * 3 + 2 = m := by
  simpa [hs] using q_mul_three_add_mod m q hq

private lemma q_mul_three_add_three (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 2) :
    q * 3 + 3 = m + 1 := by
  have hq2 : q * 3 + 2 = m := q_mul_three_add_two m q hq hs
  omega

private lemma add_three_of_add_two {a b : ℕ} (h : a + 2 = b) :
    a + 3 = b + 1 := by
  simpa [Nat.add_assoc] using congrArg Nat.succ h

private lemma four_mul_div_add_three (n m : ℕ) (hm : m = n / 4) (hr : n % 4 = 3) :
    4 * m + 3 = n := by
  simpa [hr] using four_mul_div_add_mod n m hm

private lemma four_way_sum_mod3 (n m : ℕ) (hm : m = n / 4) (hr : n % 4 = 3) :
    m + (m + 1) + (m + 1) + (m + 1) = n := by
  have hn3 : 4 * m + 3 = n := four_mul_div_add_three n m hm hr
  omega

private lemma eBonus1_mod0 (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 0) :
    eBonus 1 m = q * 13 := by
  have hq0 : q * 3 = m := by
    simpa [hs] using q_mul_three_add_mod m q hq
  simp only [eBonus]
  have hnum : 13 * m + 1 = 1 + 3 * (q * 13) := by
    rw [← hq0]
    omega
  rw [hnum, Nat.add_mul_div_left _ _ (by decide)]
  norm_num

private lemma eBonus1_mod1 (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 1) :
    eBonus 1 m = q * 13 + 4 := by
  have hq1 : q * 3 + 1 = m := by
    simpa [hs] using q_mul_three_add_mod m q hq
  simp only [eBonus]
  have hnum : 13 * m + 1 = 2 + 3 * (q * 13 + 4) := by
    rw [← hq1]
    omega
  rw [hnum, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (by decide)]
  simp

private lemma eBonus1_mod2 (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 2) :
    eBonus 1 m = q * 13 + 9 := by
  have hq2 : q * 3 + 2 = m := by
    simpa [hs] using q_mul_three_add_mod m q hq
  simp only [eBonus]
  have hnum : 13 * m + 1 = 3 * (q * 13 + 9) := by
    rw [← hq2]
    omega
  rw [hnum]
  simp

private lemma eBonus2_mod0 (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 0) :
    eBonus 2 m = q * 13 + 1 := by
  have hq0 : q * 3 = m := by
    simpa [hs] using q_mul_three_add_mod m q hq
  simp only [eBonus]
  have hnum : 13 * m + 5 = 2 + 3 * (q * 13 + 1) := by
    rw [← hq0]
    omega
  rw [hnum, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (by decide)]
  simp

private lemma eBonus2_mod1 (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 1) :
    eBonus 2 m = q * 13 + 6 := by
  have hq1 : q * 3 + 1 = m := by
    simpa [hs] using q_mul_three_add_mod m q hq
  simp only [eBonus]
  have hnum : 13 * m + 5 = 3 * (q * 13 + 6) := by
    rw [← hq1]
    omega
  rw [hnum]
  simp

private lemma eBonus2_mod2 (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 2) :
    eBonus 2 m = q * 13 + 10 := by
  have hq2 : q * 3 + 2 = m := by
    simpa [hs] using q_mul_three_add_mod m q hq
  simp only [eBonus]
  have hnum : 13 * m + 5 = 1 + 3 * (q * 13 + 10) := by
    rw [← hq2]
    omega
  rw [hnum, Nat.add_mul_div_left _ _ (by decide)]
  norm_num

private lemma eBonus3_mod0 (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 0) :
    eBonus 3 m = q * 13 + 2 := by
  have hq0 : q * 3 = m := by
    simpa [hs] using q_mul_three_add_mod m q hq
  simp only [eBonus]
  have hnum : 13 * m + 6 = 3 * (q * 13 + 2) := by
    rw [← hq0]
    omega
  rw [hnum]
  simp

private lemma eBonus3_mod1 (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 1) :
    eBonus 3 m = q * 13 + 6 := by
  have hq1 : q * 3 + 1 = m := by
    simpa [hs] using q_mul_three_add_mod m q hq
  simp only [eBonus]
  have hnum : 13 * m + 6 = 1 + 3 * (q * 13 + 6) := by
    rw [← hq1]
    omega
  rw [hnum, Nat.add_mul_div_left _ _ (by decide)]
  norm_num

private lemma eBonus3_mod2 (m q : ℕ) (hq : q = m / 3) (hs : m % 3 = 2) :
    eBonus 3 m = q * 13 + 10 := by
  have hq2 : q * 3 + 2 = m := by
    simpa [hs] using q_mul_three_add_mod m q hq
  simp only [eBonus]
  have hnum : 13 * m + 6 = 2 + 3 * (q * 13 + 10) := by
    rw [← hq2]
    omega
  rw [hnum, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (by decide)]
  simp

/-! ## The main uniform bound -/

/-- For all n ≥ 15, 25 * A_n ≥ 26 * k_n, i.e. A_n ≥ (26/25) k_n. -/
theorem uniform_26_25 (n : ℕ) (hn : 15 ≤ n) :
    25 * A n ≥ 26 * k n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h60 : n < 60
    · exact (bootstrap_26_25 n hn h60).1
    · push Not at h60
      set m := n / 4 with hm_def
      have hm15 : 15 ≤ m := by omega
      have hm_lt : m < n := Nat.div_lt_self (by omega) (by omega)
      have hm1_lt : m + 1 < n := by omega
      have ih_m := ih m hm_lt hm15
      have ih_m1 := ih (m + 1) hm1_lt (by omega)
      obtain ⟨hk0, hk1, hk2, hk3⟩ := k_four_way m (by omega)
      obtain ⟨hf0, hf1, hf2, hf3⟩ := floor_26_25 m hm15
      have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases this with hr | hr | hr | hr
      · -- n % 4 = 0
        have hA := A_mod0 n (by omega) hr
        rw [hA]
        have hkn : k n = 4 * k m + 4 * m := by
          rw [show n = 4 * m from by omega]; exact hk0
        rw [hkn]; linarith
      · -- n % 4 = 1
        have hA := A_mod1 n (by omega) hr
        rw [hA]
        have hkn : k n = 3 * k m + k (m + 1) + 4 * m := by
          rw [show n = 4 * m + 1 from by omega]; exact hk1
        rw [hkn]; linarith
      · -- n % 4 = 2
        have hA := A_mod2 n (by omega) hr
        rw [hA]
        have hkn : k n = 2 * k m + 2 * k (m + 1) + 4 * m + 1 := by
          rw [show n = 4 * m + 2 from by omega]; exact hk2
        rw [hkn]; linarith
      · -- n % 4 = 3
        have hA := A_mod3 n (by omega) hr
        rw [hA]
        have hkn : k n = k m + 3 * k (m + 1) + 4 * m + 2 := by
          rw [show n = 4 * m + 3 from by omega]; exact hk3
        rw [hkn]; linarith

/-- Each edge has at most n vertices when NoLargePartition holds. -/
private lemma edge_card_le_of_noLargePartition
    (edges : Finset (Finset ℕ)) (n : ℕ) (h : NoLargePartition edges n)
    (e : Finset ℕ) (he : e ∈ edges) : e.card ≤ n := by
  have h1 := h {e} (Finset.singleton_subset_iff.mpr he)
  unfold uniqueCoverage at h1
  -- uniqueCoverage edges {e} counts vertices in vertexSet edges that are in exactly one edge of {e}
  -- For v ∈ e: filter gives {e}, card = 1. For v ∉ e: filter gives ∅, card = 0.
  -- So uniqueCoverage edges {e} = |(vertexSet edges) ∩ e| = |e| (since e ⊆ vertexSet edges).
  have h2 : ∀ v ∈ e, v ∈ vertexSet edges := by
    intro v hv
    simp only [vertexSet, Finset.mem_biUnion]
    exact ⟨e, he, hv⟩
  have h3 :
      e ⊆ (vertexSet edges).filter
        (fun v => (({e} : Finset (Finset ℕ)).filter (fun e' => v ∈ e')).card = 1) := by
    intro v hv
    simp only [Finset.mem_filter]
    refine ⟨h2 v hv, ?_⟩
    simp only [Finset.filter_singleton, if_pos hv, Finset.card_singleton]
  exact le_trans (Finset.card_le_card h3) h1

private lemma vertexSet_card_le_sum_card (edges : Finset (Finset ℕ)) :
    (vertexSet edges).card ≤ edges.sum Finset.card := by
  induction edges using Finset.induction_on with
  | empty =>
      simp [vertexSet]
  | @insert e edges he ih =>
      simpa [vertexSet, he, add_comm, add_left_comm, add_assoc] using
        le_trans (Finset.card_union_le e (vertexSet edges))
          (Nat.add_le_add_left ih e.card)

private theorem exists_cover_subset_card_le_of_noLargePartition
    (edges : Finset (Finset ℕ)) (n : ℕ) (hpart : NoLargePartition edges n) :
    ∃ C ⊆ edges, vertexSet C = vertexSet edges ∧ C.card ≤ n := by
  let covers : Finset (Finset (Finset ℕ)) :=
    edges.powerset.filter fun P => vertexSet P = vertexSet edges
  have hcovers_nonempty : covers.Nonempty := by
    refine ⟨edges, ?_⟩
    simp [covers]
  obtain ⟨C, hCmem, hCmin⟩ := covers.exists_min_image Finset.card hcovers_nonempty
  have hCsub : C ⊆ edges := Finset.mem_powerset.mp ((Finset.mem_filter.mp hCmem).1)
  have hCcover : vertexSet C = vertexSet edges := (Finset.mem_filter.mp hCmem).2
  have hprivate :
      ∀ e, e ∈ C → ∃ v, v ∈ e ∧ v ∉ vertexSet (C.erase e) := by
    intro e heC
    by_contra h
    push Not at h
    have hsubset : e ⊆ vertexSet (C.erase e) := h
    have hcoverErase : vertexSet (C.erase e) = vertexSet edges := by
      refine le_antisymm ?_ ?_
      · intro v hv
        rw [← hCcover]
        exact Finset.mem_biUnion.mpr <| by
          rcases Finset.mem_biUnion.mp hv with ⟨e', he', hv'⟩
          exact ⟨e', (Finset.mem_erase.mp he').2, hv'⟩
      · rw [← hCcover]
        intro v hv
        rcases Finset.mem_biUnion.mp hv with ⟨e', he', hv'⟩
        by_cases hEq : e' = e
        · subst hEq
          exact hsubset hv'
        · exact Finset.mem_biUnion.mpr ⟨e', Finset.mem_erase.mpr ⟨hEq, he'⟩, hv'⟩
    have hEraseMem : C.erase e ∈ covers := by
      refine Finset.mem_filter.mpr ⟨?_, hcoverErase⟩
      exact Finset.mem_powerset.mpr <| fun e' he' => hCsub ((Finset.mem_erase.mp he').2)
    have hEraseCard : (C.erase e).card < C.card := Finset.card_erase_lt_of_mem heC
    exact (Nat.not_le_of_lt hEraseCard) (hCmin _ hEraseMem)
  choose priv hpriv_mem hpriv_not using hprivate
  let uniqVerts : Finset ℕ :=
    (vertexSet edges).filter fun v => (C.filter fun e => v ∈ e).card = 1
  have hpriv_injective : Function.Injective (fun e : {e // e ∈ C} => priv e.1 e.2) := by
    intro e₁ e₂ hEq
    by_contra hne
    have hne' : e₂.1 ≠ e₁.1 := fun hbase =>
      hne <| Subtype.ext hbase.symm
    have hmem :
        priv e₂.1 e₂.2 ∈ vertexSet (C.erase e₁.1) :=
      Finset.mem_biUnion.mpr
        ⟨e₂.1, Finset.mem_erase.mpr ⟨hne', e₂.2⟩, hpriv_mem e₂.1 e₂.2⟩
    have : priv e₁.1 e₁.2 ∈ vertexSet (C.erase e₁.1) := by
      simpa [hEq] using hmem
    exact hpriv_not e₁.1 e₁.2 this
  have hpriv_subset : C.attach.image (fun e => priv e.1 e.2) ⊆ uniqVerts := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨e, -, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← hCcover]
      exact Finset.mem_biUnion.mpr ⟨e.1, e.2, hpriv_mem e.1 e.2⟩
    · have hsingleton :
          C.filter (fun e' => priv e.1 e.2 ∈ e') ⊆ {e.1} := by
        intro e' he'
        have he'C : e' ∈ C := (Finset.mem_filter.mp he').1
        have hmem' : priv e.1 e.2 ∈ e' := (Finset.mem_filter.mp he').2
        by_contra hne
        have hne' : e' ≠ e.1 := by
          simpa using hne
        have : priv e.1 e.2 ∈ vertexSet (C.erase e.1) :=
          Finset.mem_biUnion.mpr ⟨e', Finset.mem_erase.mpr ⟨hne', he'C⟩, hmem'⟩
        exact hpriv_not e.1 e.2 this
      have hmemFilter : e.1 ∈ C.filter (fun e' => priv e.1 e.2 ∈ e') :=
        Finset.mem_filter.mpr ⟨e.2, hpriv_mem e.1 e.2⟩
      apply le_antisymm
      · exact le_trans (Finset.card_le_card hsingleton) (by simp)
      · exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨e.1, hmemFilter⟩)
  have hCcard : C.card ≤ n := by
    have hUnique :
        C.card ≤ uniqueCoverage edges C := by
      calc
        C.card = (C.attach.image (fun e => priv e.1 e.2)).card := by
          rw [Finset.card_image_of_injective _ hpriv_injective, Finset.card_attach]
        _ ≤ uniqVerts.card := Finset.card_le_card hpriv_subset
        _ = uniqueCoverage edges C := rfl
    exact le_trans hUnique (hpart C hCsub)
  exact ⟨C, hCsub, hCcover, hCcard⟩

/-- The set defining H(n) is bounded above. -/
theorem H_set_bddAbove (n : ℕ) :
    BddAbove {k : ℕ | ∃ (edges : Finset (Finset ℕ)),
      (vertexSet edges).card = k ∧ NoLargePartition edges n} := by
  refine ⟨n * n, ?_⟩
  rintro k ⟨edges, hk, hpart⟩
  obtain ⟨C, hCsub, hCcover, hCcard⟩ :=
    exists_cover_subset_card_le_of_noLargePartition edges n hpart
  have hkBound :
      (vertexSet edges).card ≤ n * n := by
    calc
      (vertexSet edges).card = (vertexSet C).card := by rw [hCcover]
      _ ≤ C.sum Finset.card := vertexSet_card_le_sum_card C
      _ ≤ C.sum (fun _ => n) := Finset.sum_le_sum fun e he =>
            edge_card_le_of_noLargePartition edges n hpart e (hCsub he)
      _ = C.card * n := by simp
      _ ≤ n * n := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hCcard
  simpa [hk] using hkBound

/-! ## Witness construction helpers -/

private theorem ws_one : WitnessStrong 1 1 := by
  refine ⟨{
      edges := {{(0 : ℕ)}}
      edgeCard := ?_
      vertexCard := ?_
      noLargePartition := ?_ }, ?_⟩
  · simp
  · simp [vertexSet]
  · intro P hP
    rw [Finset.subset_singleton_iff] at hP
    rcases hP with rfl | rfl
    · simp [uniqueCoverage]
    · unfold uniqueCoverage vertexSet
      rw [Finset.singleton_biUnion]
      simp [Finset.filter_singleton, Finset.card_singleton]
  · intro e he
    rw [Finset.mem_singleton.mp he]
    exact ⟨0, Finset.mem_singleton.mpr rfl⟩

private theorem ws_bin (a b va vb c : ℕ) (hc : c ≤ min a b)
    (ha : WitnessStrong a va) (hb : WitnessStrong b vb) :
    WitnessStrong (a + b) (va + vb + c) := by
  have hbonus : (binarySupports c).card = c := by
    simp [binarySupports, List.length_replicate]
  have h := apply_frameData (binarySupports c) (binaryCap a b) (binaryValues va vb) c
    hbonus (binary_isFrame a b c hc)
    (fun i => by
      fin_cases i
      · exact ha
      · exact hb)
  simp only [Fin.sum_univ_two, binaryCap, binaryValues] at h
  exact h

private theorem ws_bin_A (a b c : ℕ) (hc : c ≤ min a b)
    (ha : WitnessStrong a (A a)) (hb : WitnessStrong b (A b))
    (hv : A a + A b + c = A (a + b)) :
    WitnessStrong (a + b) (A (a + b)) :=
  hv ▸ ws_bin a b (A a) (A b) c hc ha hb

/-! ## Standalone intermediate witnesses -/

private theorem ws_23 : WitnessStrong 2 3 :=
  ws_bin 1 1 1 1 1 (by omega) ws_one ws_one

private theorem ws_34 : WitnessStrong 3 4 :=
  ws_bin 1 2 1 3 0 (by omega) ws_one ws_23

private theorem ws_35 : WitnessStrong 3 5 :=
  ws_bin 1 2 1 3 1 (by omega) ws_one ws_23

private theorem ws_46 : WitnessStrong 4 6 :=
  ws_bin 1 3 1 4 1 (by omega) ws_one ws_34

private theorem ws_48 : WitnessStrong 4 8 :=
  ws_bin 2 2 3 3 2 (by omega) ws_23 ws_23

private theorem ws_510 : WitnessStrong 5 10 :=
  ws_bin 2 3 3 5 2 (by omega) ws_23 ws_35

private theorem ws_820 : WitnessStrong 8 20 :=
  ws_bin 4 4 8 8 4 (by omega) ws_48 ws_48

private theorem ws_singleton : ∀ n : ℕ, 1 ≤ n → WitnessStrong n n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => exact ws_one
    | succ n =>
      exact ws_bin (n + 1) 1 (n + 1) 1 0 (by omega) (ih (by omega)) ws_one

private theorem ws_of_valid {t : ℕ}
    (supports : Multiset (SupportPattern t))
    (edgeCounts vertexCounts : Fin t → ℕ)
    (bonus : ℕ)
    (hBonus : supports.card = bonus)
    (hFrame : IsFrame supports edgeCounts)
    (hw : ∀ i, WitnessStrong (edgeCounts i) (vertexCounts i)) :
    WitnessStrong (Finset.univ.sum edgeCounts) (Finset.univ.sum vertexCounts + bonus) :=
  apply_frameData supports edgeCounts vertexCounts bonus hBonus hFrame hw

private theorem ws_614 : WitnessStrong 6 14 := by
  let spec := exactSmallFrames.get ⟨0, by decide⟩
  have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
  have hFrame := spec.isValid_iff_isFrame.mp hValid
  have h := apply_frameData spec.supports spec.cap
    (fun _ : Fin spec.t => (3 : ℕ)) spec.bonus
    spec.supports_card hFrame
    (fun i => by
      have : spec.t = 3 := by decide
      fin_cases i <;> exact ws_23)
  convert h using 1 <;> decide

private theorem ws_923 : WitnessStrong 9 23 := by
  let spec := exactSmallFrames.get ⟨3, by decide⟩
  have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
  have hFrame := spec.isValid_iff_isFrame.mp hValid
  have h := apply_frameData spec.supports spec.cap
    (![3, 3, 3, 5] : Fin spec.t → ℕ) spec.bonus
    spec.supports_card hFrame
    (fun i => by
      have : spec.t = 4 := by decide
      fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
        first | exact ws_23 | exact ws_35)
  convert h using 1 <;> decide

private theorem ws_1027 : WitnessStrong 10 27 := by
  let spec := exactSmallFrames.get ⟨4, by decide⟩
  have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
  have hFrame := spec.isValid_iff_isFrame.mp hValid
  have h := apply_frameData spec.supports spec.cap
    (![3, 3, 3, 8] : Fin spec.t → ℕ) spec.bonus
    spec.supports_card hFrame
    (fun i => by
      have : spec.t = 4 := by decide
      fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
        first | exact ws_23 | exact ws_48)
  convert h using 1 <;> decide

private theorem ws_1234 : WitnessStrong 12 34 :=
  ws_bin 6 6 14 14 6 (by omega) ws_614 ws_614

private theorem ws_1337 : WitnessStrong 13 37 := by
  let spec := exactSmallFrames.get ⟨11, by decide⟩
  have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
  have hFrame := spec.isValid_iff_isFrame.mp hValid
  have h := apply_frameData spec.supports spec.cap
    (![3, 3, 3, 5, 8] : Fin spec.t → ℕ) spec.bonus
    spec.supports_card hFrame
    (fun i => by
      have : spec.t = 5 := by decide
      fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
        first | exact ws_23 | exact ws_35 | exact ws_48)
  convert h using 1 <;> decide

private theorem ws_1441 : WitnessStrong 14 41 := by
  let spec := exactSmallFrames.get ⟨1, by decide⟩
  have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
  have hFrame := spec.isValid_iff_isFrame.mp hValid
  have h := apply_frameData spec.supports spec.cap
    (![8, 8, 14] : Fin spec.t → ℕ) spec.bonus
    spec.supports_card hFrame
    (fun i => by
      have : spec.t = 3 := by decide
      fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
        first | exact ws_48 | exact ws_614)
  convert h using 1 <;> decide

private theorem ws_1545 : WitnessStrong 15 45 := by
  let spec := boosters.get ⟨0, by decide⟩
  have hValid := finite_bank_valid.2.1 spec (List.get_mem _ _)
  have hFrame := spec.isValid_iff_isFrame.mp hValid
  have h := apply_frameData spec.supports spec.cap
    (![3, 3, 3, 3, 3, 3, 5] : Fin spec.t → ℕ) spec.bonus
    spec.supports_card hFrame
    (fun i => by
      have : spec.t = 7 := by decide
      fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
        first | exact ws_23 | exact ws_35)
  convert h using 1 <;> decide

private lemma A_bin_38 : A 18 + A 20 + 18 = A 38 := by
  eval_A_small

private lemma A_bin_41 : A 1 + A 40 + 1 = A 41 := by
  eval_A_small

private lemma A_bin_42 : A 18 + A 24 + 18 = A 42 := by
  eval_A_small

private lemma A_bin_43 : A 21 + A 22 + 21 = A 43 := by
  eval_A_small

private lemma A_bin_44 : A 22 + A 22 + 22 = A 44 := by
  eval_A_small

private lemma A_bin_45 : A 1 + A 44 + 1 = A 45 := by
  eval_A_small

private lemma A_bin_46 : A 22 + A 24 + 20 = A 46 := by
  eval_A_small

private lemma A_bin_47 : A 23 + A 24 + 23 = A 47 := by
  eval_A_small

private lemma A_bin_48 : A 24 + A 24 + 24 = A 48 := by
  eval_A_small

private lemma A_bin_50 : A 24 + A 26 + 24 = A 50 := by
  eval_A_small

private lemma A_bin_51 : A 24 + A 27 + 24 = A 51 := by
  eval_A_small

private lemma A_bin_52 : A 24 + A 28 + 24 = A 52 := by
  eval_A_small

private lemma A_bin_53 : A 26 + A 27 + 26 = A 53 := by
  eval_A_small

private lemma A_bin_54 : A 24 + A 30 + 24 = A 54 := by
  eval_A_small

private lemma A_bin_55 : A 27 + A 28 + 27 = A 55 := by
  eval_A_small

private lemma A_bin_56 : A 28 + A 28 + 28 = A 56 := by
  eval_A_small

private lemma A_bin_58 : A 28 + A 30 + 28 = A 58 := by
  eval_A_small

private lemma A_bin_59 : A 29 + A 30 + 29 = A 59 := by
  eval_A_small

/-! ## Replication helpers for the recursive case -/

private def replicateList {α : Type*} (l : List α) : ℕ → List α
  | 0 => []
  | n + 1 => l ++ replicateList l n

private theorem replicateList_length {α : Type*} (l : List α) (q : ℕ) :
    (replicateList l q).length = q * l.length := by
  induction q with
  | zero => simp [replicateList]
  | succ q ih => simp [replicateList, List.length_append, ih]; ring

private theorem replicateList_valid {t : ℕ}
    {l : List (SupportPattern t)} {cap : Fin t → ℕ}
    (h : SupportsValid l cap) (q : ℕ) :
    SupportsValid (replicateList l q) (fun i => q * cap i) := by
  induction q with
  | zero =>
    intro T I _
    simp [replicateList]
  | succ q ih =>
    intro T I hIT
    simp only [replicateList, List.countP_append]
    calc
      l.countP (frameWitnesses T I) + (replicateList l q).countP (frameWitnesses T I)
        ≤ (T \ I).sum cap + (T \ I).sum (fun i => q * cap i) :=
            Nat.add_le_add (h T I hIT) (ih T I hIT)
      _ = (T \ I).sum (fun i => (q + 1) * cap i) := by
          rw [← Finset.sum_add_distrib]
          congr 1; ext i; ring

/-! ## The main witness strength theorem -/

private theorem A_witnessStrong_bootstrap_1_20
    (n : ℕ) (hn : 1 ≤ n) (h20 : n ≤ 20)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m)) :
    WitnessStrong n (A n) := by
  interval_cases n
  -- n = 1
  · convert ws_one using 2; eval_A_small
  -- n = 2: binary(1,1,1)
  · exact ws_bin_A 1 1 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 1 (by omega) (by omega)) (by eval_A_small)
  -- n = 3: binary(1,2,0)
  · exact ws_bin_A 1 2 0 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 2 (by omega) (by omega)) (by eval_A_small)
  -- n = 4: binary(1,3,1)
  · exact ws_bin_A 1 3 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 3 (by omega) (by omega)) (by eval_A_small)
  -- n = 5: binary(1,4,0)
  · exact ws_bin_A 1 4 0 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 4 (by omega) (by omega)) (by eval_A_small)
  -- n = 6: binary(2,4,1)
  · exact ws_bin_A 2 4 1 (by omega)
      (ih 2 (by omega) (by omega))
      (ih 4 (by omega) (by omega)) (by eval_A_small)
  -- n = 7: binary(1,6,0)
  · exact ws_bin_A 1 6 0 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 6 (by omega) (by omega)) (by eval_A_small)
  -- n = 8: binary(2,6,1)
  · exact ws_bin_A 2 6 1 (by omega)
      (ih 2 (by omega) (by omega))
      (ih 6 (by omega) (by omega)) (by eval_A_small)
  -- n = 9: binary(3,6,3)
  · exact ws_bin_A 3 6 3 (by omega)
      (ih 3 (by omega) (by omega))
      (ih 6 (by omega) (by omega)) (by eval_A_small)
  -- n = 10: binary(1,9,1)
  · exact ws_bin_A 1 9 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 9 (by omega) (by omega)) (by eval_A_small)
  -- n = 11: binary(1,10,1)
  · exact ws_bin_A 1 10 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 10 (by omega) (by omega)) (by eval_A_small)
  -- n = 12: binary(2,10,2)
  · exact ws_bin_A 2 10 2 (by omega)
      (ih 2 (by omega) (by omega))
      (ih 10 (by omega) (by omega)) (by eval_A_small)
  -- n = 13: frame [2,2,2,3,4] with singletons
  · let spec := exactSmallFrames.get ⟨11, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have hf := apply_frameData spec.supports spec.cap
      (![2, 2, 2, 3, 4] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 5 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          exact ws_singleton _ (by decide))
    convert hf using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![2, 2, 2, 3, 4] : Fin spec.t → ℕ)) = 13 := by
          have ht : spec.t = 5 := by decide
          decide
      have hbonus : spec.bonus = 15 := by decide
      have hA : A 13 = 28 := by eval_A_small
      calc
        A 13 = 28 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![2, 2, 2, 3, 4] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 14: binary(1,13,1)
  · exact ws_bin_A 1 13 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 13 (by omega) (by omega)) (by eval_A_small)
  -- n = 15: boost15
  · convert ws_1545 using 1
    eval_A_small
  -- n = 16: boost16
  · let spec := boosters.get ⟨1, by decide⟩
    have hValid := finite_bank_valid.2.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (fun _ : Fin spec.t => (3 : ℕ)) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 8 := by decide
        fin_cases i <;> exact ws_23)
    convert h using 1
    · decide
    · have hsum : (∑ _ : Fin spec.t, (3 : ℕ)) = 24 := by
        have ht : spec.t = 8 := by decide
        simp [ht]
      have hbonus : spec.bonus = 26 := by decide
      have hA : A 16 = 50 := by eval_A_small
      calc
        A 16 = 50 := hA
        _ = (∑ _ : Fin spec.t, (3 : ℕ)) + spec.bonus := by omega
  -- n = 17: binary(1,16,1)
  · exact ws_bin_A 1 16 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 16 (by omega) (by omega)) (by eval_A_small)
  -- n = 18: frame [6,6,6] with WS(6,14)×3
  · let spec := exactSmallFrames.get ⟨2, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (fun _ : Fin spec.t => (14 : ℕ)) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 3 := by decide
        fin_cases i <;> exact ws_614)
    convert h using 1
    · decide
    · have hsum : (∑ _ : Fin spec.t, (14 : ℕ)) = 42 := by
        have ht : spec.t = 3 := by decide
        simp [ht]
      have hbonus : spec.bonus = 15 := by decide
      have hA : A 18 = 57 := by eval_A_small
      calc
        A 18 = 57 := hA
        _ = (∑ _ : Fin spec.t, (14 : ℕ)) + spec.bonus := by omega
  -- n = 19: boost19 [2,2,2,3,4,6]
  · let spec := boosters.get ⟨3, by decide⟩
    have hValid := finite_bank_valid.2.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![3, 3, 3, 5, 8, 14] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 6 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_23 | exact ws_35 | exact ws_48 | exact ws_614)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![3, 3, 3, 5, 8, 14] : Fin spec.t → ℕ)) = 36 := by
          have ht : spec.t = 6 := by decide
          decide
      have hbonus : spec.bonus = 24 := by decide
      have hA : A 19 = 60 := by eval_A_small
      calc
        A 19 = 60 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![3, 3, 3, 5, 8, 14] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 20: frame [4,4,4,4,4] with WS(4,8)×5
  · let spec := exactSmallFrames.get ⟨13, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (fun _ : Fin spec.t => (8 : ℕ)) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 5 := by decide
        fin_cases i <;> exact ws_48)
    convert h using 1
    · decide
    · have hsum : (∑ _ : Fin spec.t, (8 : ℕ)) = 40 := by
        have ht : spec.t = 5 := by decide
        simp [ht]
      have hbonus : spec.bonus = 25 := by decide
      have hA : A 20 = 65 := by eval_A_small
      calc
        A 20 = 65 := hA
        _ = (∑ _ : Fin spec.t, (8 : ℕ)) + spec.bonus := by omega

private theorem A_witnessStrong_bootstrap_21_30
    (n : ℕ) (h21 : 21 ≤ n) (h30 : n ≤ 30)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m)) :
    WitnessStrong n (A n) := by
  interval_cases n
  -- n = 21: frame [3,4,4,4,6] with WS(3,5)+WS(4,8)×3+WS(6,14)
  · let spec := exactSmallFrames.get ⟨12, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![5, 8, 8, 8, 14] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 5 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_35 | exact ws_48 | exact ws_614)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![5, 8, 8, 8, 14] : Fin spec.t → ℕ)) = 43 := by
          have ht : spec.t = 5 := by decide
          decide
      have hbonus : spec.bonus = 25 := by decide
      have hA : A 21 = 68 := by eval_A_small
      calc
        A 21 = 68 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![5, 8, 8, 8, 14] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 22: frame [4,4,4,4,6] with WS(4,8)×4+WS(6,14)
  · let spec := exactSmallFrames.get ⟨14, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![8, 8, 8, 8, 14] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 5 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_48 | exact ws_614)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![8, 8, 8, 8, 14] : Fin spec.t → ℕ)) = 46 := by
          have ht : spec.t = 5 := by decide
          decide
      have hbonus : spec.bonus = 27 := by decide
      have hA : A 22 = 73 := by eval_A_small
      calc
        A 22 = 73 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![8, 8, 8, 8, 14] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 23: binary(1,22,1)
  · exact ws_bin_A 1 22 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 22 (by omega) (by omega)) (by eval_A_small)
  -- n = 24: frame [6,6,6,6] with WS(6,14)×4
  · let spec := exactSmallFrames.get ⟨6, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (fun _ : Fin spec.t => (14 : ℕ)) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 4 := by decide
        fin_cases i <;> exact ws_614)
    convert h using 1
    · decide
    · have hsum : (∑ _ : Fin spec.t, (14 : ℕ)) = 56 := by
        have ht : spec.t = 4 := by decide
        simp [ht]
      have hbonus : spec.bonus = 26 := by decide
      have hA : A 24 = 82 := by eval_A_small
      calc
        A 24 = 82 := hA
        _ = (∑ _ : Fin spec.t, (14 : ℕ)) + spec.bonus := by omega
  -- n = 25: binary(1,24,1)
  · exact ws_bin_A 1 24 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 24 (by omega) (by omega)) (by eval_A_small)
  -- n = 26: frame [6,6,6,8] with WS(6,14)×3+WS(8,20)
  · let spec := exactSmallFrames.get ⟨8, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![14, 14, 14, 20] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 4 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_614 | exact ws_820)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![14, 14, 14, 20] : Fin spec.t → ℕ)) = 62 := by
          have ht : spec.t = 4 := by decide
          decide
      have hbonus : spec.bonus = 27 := by decide
      have hA : A 26 = 89 := by eval_A_small
      calc
        A 26 = 89 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![14, 14, 14, 20] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 27: frame [6,6,6,9] with WS(6,14)×3+WS(9,23)
  · let spec := exactSmallFrames.get ⟨9, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![14, 14, 14, 23] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 4 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_614 | exact ws_923)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![14, 14, 14, 23] : Fin spec.t → ℕ)) = 65 := by
          have ht : spec.t = 4 := by decide
          decide
      have hbonus : spec.bonus = 28 := by decide
      have hA : A 27 = 93 := by eval_A_small
      calc
        A 27 = 93 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![14, 14, 14, 23] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 28: frame [6,6,6,10] with WS(6,14)×3+WS(10,27)
  · let spec := exactSmallFrames.get ⟨10, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![14, 14, 14, 27] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 4 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_614 | exact ws_1027)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![14, 14, 14, 27] : Fin spec.t → ℕ)) = 69 := by
          have ht : spec.t = 4 := by decide
          decide
      have hbonus : spec.bonus = 29 := by decide
      have hA : A 28 = 98 := by eval_A_small
      calc
        A 28 = 98 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![14, 14, 14, 27] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 29: frame [5,6,6,6,6] with WS(5,10)+WS(6,14)×4
  · let spec := exactSmallFrames.get ⟨15, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![10, 14, 14, 14, 14] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 5 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_510 | exact ws_614)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![10, 14, 14, 14, 14] : Fin spec.t → ℕ)) = 66 := by
          have ht : spec.t = 5 := by decide
          decide
      have hbonus : spec.bonus = 35 := by decide
      have hA : A 29 = 101 := by eval_A_small
      calc
        A 29 = 101 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![10, 14, 14, 14, 14] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 30: frame [6,6,6,6,6] with WS(6,14)×5
  · let spec := exactSmallFrames.get ⟨16, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (fun _ : Fin spec.t => (14 : ℕ)) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 5 := by decide
        fin_cases i <;> exact ws_614)
    convert h using 1
    · decide
    · have hsum : (∑ _ : Fin spec.t, (14 : ℕ)) = 70 := by
        have ht : spec.t = 5 := by decide
        simp [ht]
      have hbonus : spec.bonus = 38 := by decide
      have hA : A 30 = 108 := by eval_A_small
      calc
        A 30 = 108 := hA
        _ = (∑ _ : Fin spec.t, (14 : ℕ)) + spec.bonus := by omega

private theorem A_witnessStrong_bootstrap_31_38
    (n : ℕ) (h31 : 31 ≤ n) (h38 : n ≤ 38)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m)) :
    WitnessStrong n (A n) := by
  interval_cases n
  -- n = 31: boost31 [3,4,4,4,4,4,4,4] with WS(3,5)+WS(4,8)×7
  · let spec := boosters.get ⟨4, by decide⟩
    have hValid := finite_bank_valid.2.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![5, 8, 8, 8, 8, 8, 8, 8] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 8 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_35 | exact ws_48)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![5, 8, 8, 8, 8, 8, 8, 8] : Fin spec.t → ℕ)) = 61 := by
          have ht : spec.t = 8 := by decide
          decide
      have hbonus : spec.bonus = 50 := by decide
      have hA : A 31 = 111 := by eval_A_small
      rw [hsum, hbonus, hA]
  -- n = 32: boost32 [4,4,4,4,4,4,4,4] with WS(4,8)×8
  · let spec := boosters.get ⟨5, by decide⟩
    have hValid := finite_bank_valid.2.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (fun _ : Fin spec.t => (8 : ℕ)) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 8 := by decide
        fin_cases i <;> exact ws_48)
    convert h using 1
    · decide
    · have hsum : (∑ _ : Fin spec.t, (8 : ℕ)) = 64 := by
        have ht : spec.t = 8 := by decide
        simp [ht]
      have hbonus : spec.bonus = 53 := by decide
      have hA : A 32 = 117 := by eval_A_small
      rw [hsum, hbonus, hA]
  -- n = 33: boost33 [1,4,4,4,4,4,4,4,4] with WS(1,1)+WS(4,8)×8
  · let spec := boosters.get ⟨6, by decide⟩
    have hValid := finite_bank_valid.2.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![1, 8, 8, 8, 8, 8, 8, 8, 8] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 9 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_one | exact ws_48)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![1, 8, 8, 8, 8, 8, 8, 8, 8] : Fin spec.t → ℕ)) = 65 := by
          have ht : spec.t = 9 := by decide
          decide
      have hbonus : spec.bonus = 55 := by decide
      have hA : A 33 = 120 := by eval_A_small
      calc
        A 33 = 120 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![1, 8, 8, 8, 8, 8, 8, 8, 8] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 34: frame [6,6,6,6,10] with WS(6,14)×4+WS(10,27)
  · let spec := exactSmallFrames.get ⟨17, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![14, 14, 14, 14, 27] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 5 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_614 | exact ws_1027)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![14, 14, 14, 14, 27] : Fin spec.t → ℕ)) = 83 := by
          have ht : spec.t = 5 := by decide
          decide
      have hbonus : spec.bonus = 42 := by decide
      have hA : A 34 = 125 := by eval_A_small
      calc
        A 34 = 125 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![14, 14, 14, 14, 27] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 35: binary(1,34,1)
  · exact ws_bin_A 1 34 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 34 (by omega) (by omega)) (by eval_A_small)
  -- n = 36: frame [6,6,6,6,12] with WS(6,14)×4+WS(12,34)
  · let spec := exactSmallFrames.get ⟨19, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![14, 14, 14, 14, 34] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 5 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_614 | exact ws_1234)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![14, 14, 14, 14, 34] : Fin spec.t → ℕ)) = 90 := by
          have ht : spec.t = 5 := by decide
          decide
      have hbonus : spec.bonus = 44 := by decide
      have hA : A 36 = 134 := by eval_A_small
      calc
        A 36 = 134 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![14, 14, 14, 14, 34] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 37: frame [6,6,6,6,13] with WS(6,14)×4+WS(13,37)
  · let spec := exactSmallFrames.get ⟨20, by decide⟩
    have hValid := finite_bank_valid.1 spec (List.get_mem _ _)
    have hFrame := spec.isValid_iff_isFrame.mp hValid
    have h := apply_frameData spec.supports spec.cap
      (![14, 14, 14, 14, 37] : Fin spec.t → ℕ) spec.bonus
      spec.supports_card hFrame
      (fun i => by
        have : spec.t = 5 := by decide
        fin_cases i <;> simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd] <;>
          first | exact ws_614 | exact ws_1337)
    convert h using 1
    · decide
    · have hsum :
        ((Finset.univ : Finset (Fin spec.t)).sum
          (![14, 14, 14, 14, 37] : Fin spec.t → ℕ)) = 93 := by
          have ht : spec.t = 5 := by decide
          decide
      have hbonus : spec.bonus = 44 := by decide
      have hA : A 37 = 137 := by eval_A_small
      calc
        A 37 = 137 := hA
        _ =
            ((Finset.univ : Finset (Fin spec.t)).sum
              (![14, 14, 14, 14, 37] : Fin spec.t → ℕ)) + spec.bonus := by
          omega
  -- n = 38: binary(18,20,18)
  · exact ws_bin_A 18 20 18 (by omega)
      (ih 18 (by omega) (by omega))
      (ih 20 (by omega) (by omega)) A_bin_38

private theorem A_witnessStrong_bootstrap_39_49
    (n : ℕ) (h39 : 39 ≤ n) (h49 : n ≤ 49)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m)) :
    WitnessStrong n (A n) := by
  interval_cases n
  -- n = 39: core4×3+residue[3]
  · have core_valid : SupportsValid core4Spec.supportList core4Spec.cap :=
      (SupportsValid.ofSpec core4Spec).mpr core4Spec_valid
    have res3_valid : SupportsValid (residueGadgets.get ⟨3, by decide⟩).supportList
        (residueGadgets.get ⟨3, by decide⟩).cap :=
      (SupportsValid.ofSpec _).mpr (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have combined := ((core_valid.append core_valid).append core_valid).append res3_valid
    have hFrame := combined.toIsFrame
    let sl_c : List (SupportPattern 4) := core4Spec.supportList
    let sl_r : List (SupportPattern 4) := (residueGadgets.get ⟨3, by decide⟩).supportList
    have h := apply_frameData
      ((sl_c ++ sl_c ++ sl_c ++ sl_r : List _) : Multiset _)
      (fun i : Fin 4 => core4Spec.cap i + core4Spec.cap i + core4Spec.cap i +
        (residueGadgets.get ⟨3, by decide⟩).cap i)
      (![23, 27, 27, 27])
      41
      (by decide)
      hFrame
        (fun i => by
          have : core4Spec.t = 4 := by decide
          fin_cases i
          · exact ws_923
          · exact ws_1027
          · exact ws_1027
          · exact ws_1027)
    convert h using 1
    · decide
    · have hsum :
          ((Finset.univ : Finset (Fin 4)).sum
            (![23, 27, 27, 27] : Fin 4 → ℕ)) = 104 := by
        decide
      have hA : A 39 = 145 := by eval_A_small
      calc
        A 39 = 145 := hA
        _ =
            ((Finset.univ : Finset (Fin 4)).sum
              (![23, 27, 27, 27] : Fin 4 → ℕ)) + 41 := by
          omega
  -- n = 40: core4×3+residue[4]
  · have core_valid : SupportsValid core4Spec.supportList core4Spec.cap :=
      (SupportsValid.ofSpec core4Spec).mpr core4Spec_valid
    have res4_valid : SupportsValid (residueGadgets.get ⟨4, by decide⟩).supportList
        (residueGadgets.get ⟨4, by decide⟩).cap :=
      (SupportsValid.ofSpec _).mpr (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have combined := ((core_valid.append core_valid).append core_valid).append res4_valid
    have hFrame := combined.toIsFrame
    let sl_c : List (SupportPattern 4) := core4Spec.supportList
    let sl_r : List (SupportPattern 4) := (residueGadgets.get ⟨4, by decide⟩).supportList
    have h := apply_frameData
      ((sl_c ++ sl_c ++ sl_c ++ sl_r : List _) : Multiset _)
      (fun i : Fin 4 => core4Spec.cap i + core4Spec.cap i + core4Spec.cap i +
        (residueGadgets.get ⟨4, by decide⟩).cap i)
      (![27, 27, 27, 27])
      43
      (by decide)
      hFrame
        (fun i => by
          have : core4Spec.t = 4 := by decide
          fin_cases i <;> exact ws_1027)
    convert h using 1
    · decide
    · have hsum :
          ((Finset.univ : Finset (Fin 4)).sum
            (![27, 27, 27, 27] : Fin 4 → ℕ)) = 108 := by
        decide
      have hA : A 40 = 151 := by eval_A_small
      calc
        A 40 = 151 := hA
        _ =
            ((Finset.univ : Finset (Fin 4)).sum
              (![27, 27, 27, 27] : Fin 4 → ℕ)) + 43 := by
          omega
  -- n = 41: binary(1,40,1)
  · exact ws_bin_A 1 40 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 40 (by omega) (by omega)) A_bin_41
  -- n = 42: binary(18,24,18)
  · exact ws_bin_A 18 24 18 (by omega)
      (ih 18 (by omega) (by omega))
      (ih 24 (by omega) (by omega)) A_bin_42
  -- n = 43: binary(21,22,21)
  · exact ws_bin_A 21 22 21 (by omega)
      (ih 21 (by omega) (by omega))
      (ih 22 (by omega) (by omega)) A_bin_43
  -- n = 44: binary(22,22,22)
  · exact ws_bin_A 22 22 22 (by omega)
      (ih 22 (by omega) (by omega))
      (ih 22 (by omega) (by omega)) A_bin_44
  -- n = 45: binary(1,44,1)
  · exact ws_bin_A 1 44 1 (by omega)
      (ih 1 (by omega) (by omega))
      (ih 44 (by omega) (by omega)) A_bin_45
  -- n = 46: binary(22,24,20)
  · exact ws_bin_A 22 24 20 (by omega)
      (ih 22 (by omega) (by omega))
      (ih 24 (by omega) (by omega)) A_bin_46
  -- n = 47: binary(23,24,23)
  · exact ws_bin_A 23 24 23 (by omega)
      (ih 23 (by omega) (by omega))
      (ih 24 (by omega) (by omega)) A_bin_47
  -- n = 48: binary(24,24,24)
  · exact ws_bin_A 24 24 24 (by omega)
      (ih 24 (by omega) (by omega))
      (ih 24 (by omega) (by omega)) A_bin_48
  -- n = 49: core4×4+residue[1]
  · have core_valid : SupportsValid core4Spec.supportList core4Spec.cap :=
      (SupportsValid.ofSpec core4Spec).mpr core4Spec_valid
    have res1_valid : SupportsValid (residueGadgets.get ⟨1, by decide⟩).supportList
        (residueGadgets.get ⟨1, by decide⟩).cap :=
      (SupportsValid.ofSpec _).mpr (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have combined :=
      (((core_valid.append core_valid).append core_valid).append core_valid).append res1_valid
    have hFrame := combined.toIsFrame
    let sl_c : List (SupportPattern 4) := core4Spec.supportList
    let sl_r : List (SupportPattern 4) := (residueGadgets.get ⟨1, by decide⟩).supportList
    have h := apply_frameData
      ((sl_c ++ sl_c ++ sl_c ++ sl_c ++ sl_r : List _) : Multiset _)
      (fun i : Fin 4 => core4Spec.cap i + core4Spec.cap i + core4Spec.cap i +
        core4Spec.cap i + (residueGadgets.get ⟨1, by decide⟩).cap i)
      (![34, 34, 34, 37])
      52
      (by decide)
      hFrame
        (fun i => by
          have : core4Spec.t = 4 := by decide
          fin_cases i
          · exact ws_1234
          · exact ws_1234
          · exact ws_1234
          · exact ws_1337)
    convert h using 1
    · decide
    · have hsum :
          ((Finset.univ : Finset (Fin 4)).sum
            (![34, 34, 34, 37] : Fin 4 → ℕ)) = 139 := by
        decide
      have hA : A 49 = 191 := by eval_A_small
      calc
        A 49 = 191 := hA
        _ =
            ((Finset.univ : Finset (Fin 4)).sum
              (![34, 34, 34, 37] : Fin 4 → ℕ)) + 52 := by
          omega

private theorem A_witnessStrong_bootstrap_50_59
    (n : ℕ) (h50 : 50 ≤ n) (h60 : n < 60)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m)) :
    WitnessStrong n (A n) := by
  interval_cases n
  -- n = 50: binary(24,26,24)
  · exact ws_bin_A 24 26 24 (by omega)
      (ih 24 (by omega) (by omega))
      (ih 26 (by omega) (by omega)) A_bin_50
  -- n = 51: binary(24,27,24)
  · exact ws_bin_A 24 27 24 (by omega)
      (ih 24 (by omega) (by omega))
      (ih 27 (by omega) (by omega)) A_bin_51
  -- n = 52: binary(24,28,24)
  · exact ws_bin_A 24 28 24 (by omega)
      (ih 24 (by omega) (by omega))
      (ih 28 (by omega) (by omega)) A_bin_52
  -- n = 53: binary(26,27,26)
  · exact ws_bin_A 26 27 26 (by omega)
      (ih 26 (by omega) (by omega))
      (ih 27 (by omega) (by omega)) A_bin_53
  -- n = 54: binary(24,30,24)
  · exact ws_bin_A 24 30 24 (by omega)
      (ih 24 (by omega) (by omega))
      (ih 30 (by omega) (by omega)) A_bin_54
  -- n = 55: binary(27,28,27)
  · exact ws_bin_A 27 28 27 (by omega)
      (ih 27 (by omega) (by omega))
      (ih 28 (by omega) (by omega)) A_bin_55
  -- n = 56: binary(28,28,28)
  · exact ws_bin_A 28 28 28 (by omega)
      (ih 28 (by omega) (by omega))
      (ih 28 (by omega) (by omega)) A_bin_56
  -- n = 57: core4×4+residue[9]
  · have core_valid : SupportsValid core4Spec.supportList core4Spec.cap :=
      (SupportsValid.ofSpec core4Spec).mpr core4Spec_valid
    have res9_valid : SupportsValid (residueGadgets.get ⟨9, by decide⟩).supportList
        (residueGadgets.get ⟨9, by decide⟩).cap :=
      (SupportsValid.ofSpec _).mpr (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have combined :=
      (((core_valid.append core_valid).append core_valid).append core_valid).append res9_valid
    have hFrame := combined.toIsFrame
    let sl_c : List (SupportPattern 4) := core4Spec.supportList
    let sl_r : List (SupportPattern 4) := (residueGadgets.get ⟨9, by decide⟩).supportList
    have h := apply_frameData
      ((sl_c ++ sl_c ++ sl_c ++ sl_c ++ sl_r : List _) : Multiset _)
      (fun i : Fin 4 => core4Spec.cap i + core4Spec.cap i + core4Spec.cap i +
        core4Spec.cap i + (residueGadgets.get ⟨9, by decide⟩).cap i)
      (![41, 41, 41, 45])
      61
      (by decide)
        hFrame
        (fun i => by
          have : core4Spec.t = 4 := by decide
          fin_cases i
          · exact ws_1441
          · exact ws_1441
          · exact ws_1441
          · exact ws_1545)
    convert h using 1
    · decide
    · have hsum :
          ((Finset.univ : Finset (Fin 4)).sum
            (![41, 41, 41, 45] : Fin 4 → ℕ)) = 168 := by
        decide
      have hA : A 57 = 229 := by eval_A_small
      calc
        A 57 = 229 := hA
        _ =
            ((Finset.univ : Finset (Fin 4)).sum
              (![41, 41, 41, 45] : Fin 4 → ℕ)) + 61 := by
          omega
  -- n = 58: binary(28,30,28)
  · exact ws_bin_A 28 30 28 (by omega)
      (ih 28 (by omega) (by omega))
      (ih 30 (by omega) (by omega)) A_bin_58
  -- n = 59: binary(29,30,29)
  · exact ws_bin_A 29 30 29 (by omega)
      (ih 29 (by omega) (by omega))
      (ih 30 (by omega) (by omega)) A_bin_59

private theorem A_witnessStrong_bootstrap
    (n : ℕ) (hn : 1 ≤ n) (h60 : n < 60)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m)) :
    WitnessStrong n (A n) := by
  by_cases h20 : n ≤ 20
  · exact A_witnessStrong_bootstrap_1_20 n hn h20 ih
  by_cases h30 : n ≤ 30
  · exact A_witnessStrong_bootstrap_21_30 n (by omega) h30 ih
  by_cases h38 : n ≤ 38
  · exact A_witnessStrong_bootstrap_31_38 n (by omega) h38 ih
  by_cases h49 : n ≤ 49
  · exact A_witnessStrong_bootstrap_39_49 n (by omega) h49 ih
  exact A_witnessStrong_bootstrap_50_59 n (by omega) h60 ih

private theorem A_witnessStrong_recursive_mod0
    (n : ℕ) (_hn : 1 ≤ n) (h60 : 60 ≤ n)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m))
    (hr : n % 4 = 0) :
    WitnessStrong n (A n) := by
  set m := n / 4 with hm_def
  have hm_pos : 1 ≤ m := by omega
  have hm_lt : m < n := Nat.div_lt_self (by omega) (by omega)
  have ws_m := ih m hm_lt hm_pos
  have core_valid : SupportsValid core4Spec.supportList core4Spec.cap :=
    (SupportsValid.ofSpec core4Spec).mpr core4Spec_valid
  have hcc : ∀ i : Fin 4, core4Spec.cap i = 3 :=
    core4Spec_cap_eq_three
  set q := m / 3 with hq_def
  have hA := A_mod0 n (by omega) hr
  rw [hA]
  have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases this with hs | hs | hs
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨0, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨0, by decide⟩).supportList
    have hrc : ∀ i : Fin 4, (residueGadgets.get ⟨0, by decide⟩).cap i = 0 := by
      intro i
      fin_cases i <;> decide
    have hqm : q * 3 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨0, by decide⟩).cap i) =
          ![m, m, m, m] := by
      funext i
      fin_cases i <;> change q * 3 + 0 = m <;> simp [hqm]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨0, by decide⟩).cap i)
      (![A m, A m, A m, A m]) (q * 13 + 0)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 0 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> exact ws_m)
    convert h using 1
    · simp only [Fin.sum_univ_four, hcc, hrc]; omega
    · simp only [← hm_def]
      rw [show Finset.univ.sum (![A m, A m, A m, A m] : Fin 4 → ℕ) =
          A m + A m + A m + A m from by rw [Fin.sum_univ_four]; rfl]
      simp only [eBonus]; omega
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨4, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨4, by decide⟩).supportList
    have hrc : ∀ i : Fin 4, (residueGadgets.get ⟨4, by decide⟩).cap i = 1 := by
      intro i
      fin_cases i <;> decide
    have hqm : q * 3 + 1 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨4, by decide⟩).cap i) =
          ![m, m, m, m] := by
      funext i
      fin_cases i <;> change q * 3 + 1 = m <;> simp [hqm]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨4, by decide⟩).cap i)
      (![A m, A m, A m, A m]) (q * 13 + 4)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 4 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> exact ws_m)
    convert h using 1
    · simp only [Fin.sum_univ_four, hcc, hrc]; omega
    · simp only [← hm_def]
      rw [show Finset.univ.sum (![A m, A m, A m, A m] : Fin 4 → ℕ) =
          A m + A m + A m + A m from by rw [Fin.sum_univ_four]; rfl]
      simp only [eBonus]; omega
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨8, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨8, by decide⟩).supportList
    have hrc : ∀ i : Fin 4, (residueGadgets.get ⟨8, by decide⟩).cap i = 2 := by
      intro i
      fin_cases i <;> decide
    have hqm : q * 3 + 2 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨8, by decide⟩).cap i) =
          ![m, m, m, m] := by
      funext i
      fin_cases i <;> change q * 3 + 2 = m <;> simp [hqm]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨8, by decide⟩).cap i)
      (![A m, A m, A m, A m]) (q * 13 + 8)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 8 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> exact ws_m)
    convert h using 1
    · simp only [Fin.sum_univ_four, hcc, hrc]; omega
    · simp only [← hm_def]
      rw [show Finset.univ.sum (![A m, A m, A m, A m] : Fin 4 → ℕ) =
          A m + A m + A m + A m from by rw [Fin.sum_univ_four]; rfl]
      simp only [eBonus]; omega

private theorem A_witnessStrong_recursive_mod1
    (n : ℕ) (_hn : 1 ≤ n) (h60 : 60 ≤ n)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m))
    (hr : n % 4 = 1) :
    WitnessStrong n (A n) := by
  set m := n / 4 with hm_def
  have hm_pos : 1 ≤ m := by omega
  have hm1_pos : 1 ≤ m + 1 := by omega
  have hm_lt : m < n := Nat.div_lt_self (by omega) (by omega)
  have hm1_lt : m + 1 < n := by omega
  have ws_m := ih m hm_lt hm_pos
  have ws_m1 := ih (m + 1) hm1_lt hm1_pos
  have core_valid : SupportsValid core4Spec.supportList core4Spec.cap :=
    (SupportsValid.ofSpec core4Spec).mpr core4Spec_valid
  set q := m / 3 with hq_def
  have hA := A_mod1 n (by omega) hr
  rw [hA]
  have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases this with hs | hs | hs
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨1, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨1, by decide⟩).supportList
    have hqm : q * 3 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hqm1 : q * 3 + 1 = m + 1 := by omega
    have hn1 : 4 * m + 1 = n := by
      simpa [hr] using four_mul_div_add_mod n m hm_def
    have hbonus : eBonus 1 m = q * 13 := eBonus1_mod0 m q hq_def hs
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨1, by decide⟩).cap i) =
          ![m, m, m, m + 1] := by
      funext i
      fin_cases i
      · change q * 3 + 0 = m; simp [hqm]
      · change q * 3 + 0 = m; simp [hqm]
      · change q * 3 + 0 = m; simp [hqm]
      · change q * 3 + 1 = m + 1; simp [hqm1]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨1, by decide⟩).cap i)
      (![A m, A m, A m, A (m + 1)]) (q * 13 + 0)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 0 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> first | exact ws_m | exact ws_m1)
    convert h using 1
    · rw [← hn1, hedgeCounts, Fin.sum_univ_four]
      simp
      omega
    · simp only [← hm_def]
      rw [show Finset.univ.sum (![A m, A m, A m, A (m + 1)] : Fin 4 → ℕ) =
          A m + A m + A m + A (m + 1) from by rw [Fin.sum_univ_four]; rfl]
      simp [hbonus]
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨5, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨5, by decide⟩).supportList
    have hqm : q * 3 + 1 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hqm1 : q * 3 + 2 = m + 1 := by omega
    have hn1 : 4 * m + 1 = n := by
      simpa [hr] using four_mul_div_add_mod n m hm_def
    have hbonus : eBonus 1 m = q * 13 + 4 := eBonus1_mod1 m q hq_def hs
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨5, by decide⟩).cap i) =
          ![m, m, m, m + 1] := by
      funext i
      fin_cases i
      · change q * 3 + 1 = m; simp [hqm]
      · change q * 3 + 1 = m; simp [hqm]
      · change q * 3 + 1 = m; simp [hqm]
      · change q * 3 + 2 = m + 1; simp [hqm1]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨5, by decide⟩).cap i)
      (![A m, A m, A m, A (m + 1)]) (q * 13 + 4)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 4 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> first | exact ws_m | exact ws_m1)
    convert h using 1
    · rw [← hn1, hedgeCounts, Fin.sum_univ_four]
      simp
      omega
    · simp only [← hm_def]
      rw [show Finset.univ.sum (![A m, A m, A m, A (m + 1)] : Fin 4 → ℕ) =
          A m + A m + A m + A (m + 1) from by rw [Fin.sum_univ_four]; rfl]
      simp [hbonus]
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨9, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨9, by decide⟩).supportList
    have hqm : q * 3 + 2 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hqm1 : q * 3 + 3 = m + 1 := by omega
    have hn1 : 4 * m + 1 = n := by
      simpa [hr] using four_mul_div_add_mod n m hm_def
    have hbonus : eBonus 1 m = q * 13 + 9 := eBonus1_mod2 m q hq_def hs
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨9, by decide⟩).cap i) =
          ![m, m, m, m + 1] := by
      funext i
      fin_cases i
      · change q * 3 + 2 = m; simp [hqm]
      · change q * 3 + 2 = m; simp [hqm]
      · change q * 3 + 2 = m; simp [hqm]
      · change q * 3 + 3 = m + 1; simp [hqm1]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨9, by decide⟩).cap i)
      (![A m, A m, A m, A (m + 1)]) (q * 13 + 9)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 9 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> first | exact ws_m | exact ws_m1)
    convert h using 1
    · rw [← hn1, hedgeCounts, Fin.sum_univ_four]
      simp
      omega
    · simp only [← hm_def]
      rw [show Finset.univ.sum (![A m, A m, A m, A (m + 1)] : Fin 4 → ℕ) =
          A m + A m + A m + A (m + 1) from by rw [Fin.sum_univ_four]; rfl]
      simp [hbonus]

private theorem A_witnessStrong_recursive_mod2
    (n : ℕ) (_hn : 1 ≤ n) (h60 : 60 ≤ n)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m))
    (hr : n % 4 = 2) :
    WitnessStrong n (A n) := by
  set m := n / 4 with hm_def
  have hm_pos : 1 ≤ m := by omega
  have hm1_pos : 1 ≤ m + 1 := by omega
  have hm_lt : m < n := Nat.div_lt_self (by omega) (by omega)
  have hm1_lt : m + 1 < n := by omega
  have ws_m := ih m hm_lt hm_pos
  have ws_m1 := ih (m + 1) hm1_lt hm1_pos
  have core_valid : SupportsValid core4Spec.supportList core4Spec.cap :=
    (SupportsValid.ofSpec core4Spec).mpr core4Spec_valid
  set q := m / 3 with hq_def
  have hA := A_mod2 n (by omega) hr
  rw [hA]
  have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases this with hs | hs | hs
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨2, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨2, by decide⟩).supportList
    have hqm : q * 3 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hqm1 : q * 3 + 1 = m + 1 := by omega
    have hn2 : 4 * m + 2 = n := by
      simpa [hr] using four_mul_div_add_mod n m hm_def
    have hbonus : eBonus 2 m = q * 13 + 1 := eBonus2_mod0 m q hq_def hs
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨2, by decide⟩).cap i) =
          ![m, m, m + 1, m + 1] := by
      funext i
      fin_cases i
      · change q * 3 + 0 = m; simp [hqm]
      · change q * 3 + 0 = m; simp [hqm]
      · change q * 3 + 1 = m + 1; simp [hqm1]
      · change q * 3 + 1 = m + 1; simp [hqm1]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨2, by decide⟩).cap i)
      (![A m, A m, A (m + 1), A (m + 1)]) (q * 13 + 1)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 1 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> first | exact ws_m | exact ws_m1)
    convert h using 1
    · rw [← hn2, hedgeCounts, Fin.sum_univ_four]
      simp
      omega
    · simp only [← hm_def]
      rw [show Finset.univ.sum (![A m, A m, A (m + 1), A (m + 1)] : Fin 4 → ℕ) =
          A m + A m + A (m + 1) + A (m + 1) from by rw [Fin.sum_univ_four]; rfl]
      simp [hbonus]
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨6, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨6, by decide⟩).supportList
    have hqm : q * 3 + 1 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hqm1 : q * 3 + 2 = m + 1 := by omega
    have hn2 : 4 * m + 2 = n := by
      simpa [hr] using four_mul_div_add_mod n m hm_def
    have hbonus : eBonus 2 m = q * 13 + 6 := eBonus2_mod1 m q hq_def hs
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨6, by decide⟩).cap i) =
          ![m, m, m + 1, m + 1] := by
      funext i
      fin_cases i
      · change q * 3 + 1 = m; simp [hqm]
      · change q * 3 + 1 = m; simp [hqm]
      · change q * 3 + 2 = m + 1; simp [hqm1]
      · change q * 3 + 2 = m + 1; simp [hqm1]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨6, by decide⟩).cap i)
      (![A m, A m, A (m + 1), A (m + 1)]) (q * 13 + 6)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 6 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> first | exact ws_m | exact ws_m1)
    convert h using 1
    · rw [← hn2, hedgeCounts, Fin.sum_univ_four]
      simp
      omega
    · simp only [← hm_def]
      rw [show Finset.univ.sum (![A m, A m, A (m + 1), A (m + 1)] : Fin 4 → ℕ) =
          A m + A m + A (m + 1) + A (m + 1) from by rw [Fin.sum_univ_four]; rfl]
      simp [hbonus]
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨10, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨10, by decide⟩).supportList
    have hqm : q * 3 + 2 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hqm1 : q * 3 + 3 = m + 1 := by omega
    have hn2 : 4 * m + 2 = n := by
      simpa [hr] using four_mul_div_add_mod n m hm_def
    have hbonus : eBonus 2 m = q * 13 + 10 := eBonus2_mod2 m q hq_def hs
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨10, by decide⟩).cap i) =
          ![m, m, m + 1, m + 1] := by
      funext i
      fin_cases i
      · change q * 3 + 2 = m; simp [hqm]
      · change q * 3 + 2 = m; simp [hqm]
      · change q * 3 + 3 = m + 1; simp [hqm1]
      · change q * 3 + 3 = m + 1; simp [hqm1]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨10, by decide⟩).cap i)
      (![A m, A m, A (m + 1), A (m + 1)]) (q * 13 + 10)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 10 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> first | exact ws_m | exact ws_m1)
    convert h using 1
    · rw [← hn2, hedgeCounts, Fin.sum_univ_four]
      simp
      omega
    · simp only [← hm_def]
      rw [show Finset.univ.sum (![A m, A m, A (m + 1), A (m + 1)] : Fin 4 → ℕ) =
          A m + A m + A (m + 1) + A (m + 1) from by rw [Fin.sum_univ_four]; rfl]
      simp [hbonus]

private theorem A_witnessStrong_recursive_mod3
    (n : ℕ) (_hn : 1 ≤ n) (h60 : 60 ≤ n)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m))
    (hr : n % 4 = 3) :
    WitnessStrong n (A n) := by
  set m := n / 4 with hm_def
  have hm_pos : 1 ≤ m := by omega
  have hm1_pos : 1 ≤ m + 1 := by omega
  have hm_lt : m < n := Nat.div_lt_self (by omega) (by omega)
  have hm1_lt : m + 1 < n := by omega
  have ws_m := ih m hm_lt hm_pos
  have ws_m1 := ih (m + 1) hm1_lt hm1_pos
  have core_valid : SupportsValid core4Spec.supportList core4Spec.cap :=
    (SupportsValid.ofSpec core4Spec).mpr core4Spec_valid
  set q := m / 3 with hq_def
  have hA := A_mod3 n (by omega) hr
  rw [hA]
  have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases this with hs | hs | hs
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨3, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨3, by decide⟩).supportList
    have hqm : q * 3 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hqm1 : q * 3 + 1 = m + 1 := by omega
    have hn3 : 4 * m + 3 = n := by
      simpa [hr] using four_mul_div_add_mod n m hm_def
    have hbonus : eBonus 3 m = q * 13 + 2 := eBonus3_mod0 m q hq_def hs
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨3, by decide⟩).cap i) =
          ![m, m + 1, m + 1, m + 1] := by
      funext i
      fin_cases i
      · change q * 3 + 0 = m; simp [hqm]
      · change q * 3 + 1 = m + 1; simp [hqm1]
      · change q * 3 + 1 = m + 1; simp [hqm1]
      · change q * 3 + 1 = m + 1; simp [hqm1]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨3, by decide⟩).cap i)
      (![A m, A (m + 1), A (m + 1), A (m + 1)]) (q * 13 + 2)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 2 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> first | exact ws_m | exact ws_m1)
    convert h using 1
    · rw [← hn3, hedgeCounts, Fin.sum_univ_four]
      simp
      omega
    · simp only [← hm_def]
      rw [Fin.sum_univ_four]
      simp [hbonus, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨7, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨7, by decide⟩).supportList
    have hqm : q * 3 + 1 = m := by
      simpa [hs] using q_mul_three_add_mod m q hq_def
    have hqm1 : q * 3 + 2 = m + 1 := by omega
    have hn3 : 4 * m + 3 = n := by
      simpa [hr] using four_mul_div_add_mod n m hm_def
    have hbonus : eBonus 3 m = q * 13 + 6 := eBonus3_mod1 m q hq_def hs
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨7, by decide⟩).cap i) =
          ![m, m + 1, m + 1, m + 1] := by
      funext i
      fin_cases i
      · change q * 3 + 1 = m; simp [hqm]
      · change q * 3 + 2 = m + 1; simp [hqm1]
      · change q * 3 + 2 = m + 1; simp [hqm1]
      · change q * 3 + 2 = m + 1; simp [hqm1]
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨7, by decide⟩).cap i)
      (![A m, A (m + 1), A (m + 1), A (m + 1)]) (q * 13 + 6)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 6 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> first | exact ws_m | exact ws_m1)
    convert h using 1
    · rw [← hn3, hedgeCounts, Fin.sum_univ_four]
      simp
      omega
    · simp only [← hm_def]
      rw [Fin.sum_univ_four]
      simp [hbonus, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · have rv := (SupportsValid.ofSpec (residueGadgets.get ⟨11, by decide⟩)).mpr
      (finite_bank_valid.2.2 _ (List.get_mem _ _))
    have hF := ((replicateList_valid core_valid q).append rv).toIsFrame
    let sc : List (SupportPattern 4) := core4Spec.supportList
    let sr : List (SupportPattern 4) := (residueGadgets.get ⟨11, by decide⟩).supportList
    have hqm : q * 3 + 2 = m := q_mul_three_add_two m q hq_def hs
    have hsum4 : m + (m + 1) + (m + 1) + (m + 1) = n :=
      four_way_sum_mod3 n m hm_def hr
    have hbonus : eBonus 3 m = q * 13 + 10 := eBonus3_mod2 m q hq_def hs
    have hedgeCounts :
        (fun i : Fin 4 =>
          q * core4Spec.cap i + (residueGadgets.get ⟨11, by decide⟩).cap i) =
          ![m, m + 1, m + 1, m + 1] := by
      funext i
      fin_cases i
      · change q * 3 + 2 = m; simp [hqm]
      · change q * 3 + 3 = m + 1; omega
      · change q * 3 + 3 = m + 1; omega
      · change q * 3 + 3 = m + 1; omega
    have h := apply_frameData
      ((replicateList sc q ++ sr : List _) : Multiset _)
      (fun i : Fin 4 =>
        q * core4Spec.cap i + (residueGadgets.get ⟨11, by decide⟩).cap i)
      (![A m, A (m + 1), A (m + 1), A (m + 1)]) (q * 13 + 10)
      (by simp only [Multiset.coe_card, List.length_append, replicateList_length,
            show sc.length = 13 from by decide, show sr.length = 10 from by decide])
      hF
      (fun i => by
        have hi := congrFun hedgeCounts i
        rw [hi]
        fin_cases i <;> first | exact ws_m | exact ws_m1)
    convert h using 1
    · rw [hedgeCounts, Fin.sum_univ_four]
      simp
      omega
    · simp only [← hm_def]
      rw [Fin.sum_univ_four]
      simp [hbonus, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem A_witnessStrong_recursive
    (n : ℕ) (hn : 1 ≤ n) (h60 : 60 ≤ n)
    (ih : ∀ m < n, 1 ≤ m → WitnessStrong m (A m)) :
    WitnessStrong n (A n) := by
  have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases this with hr | hr | hr | hr
  · exact A_witnessStrong_recursive_mod0 n hn h60 ih hr
  · exact A_witnessStrong_recursive_mod1 n hn h60 ih hr
  · exact A_witnessStrong_recursive_mod2 n hn h60 ih hr
  · exact A_witnessStrong_recursive_mod3 n hn h60 ih hr

private theorem A_witnessStrong (n : ℕ) (hn : 1 ≤ n) : WitnessStrong n (A n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h60 : n < 60
    · exact A_witnessStrong_bootstrap n hn h60 ih
    · push Not at h60
      exact A_witnessStrong_recursive n hn h60 ih

/-- A_witness for 2 ≤ n < 60: the bootstrap window. -/
private theorem A_witness_bootstrap (n : ℕ) (h1 : 2 ≤ n) (h2 : n < 60) :
    ∃ (edges : Finset (Finset ℕ)),
      edges.card = n ∧ (vertexSet edges).card = A n ∧ NoLargePartition edges n := by
  let w : Witness n (A n) := (A_witnessStrong n (by omega)).toWitnessData
  exact ⟨w.edges, w.edgeCard, w.vertexCard, w.noLargePartition⟩

/-- A_witness for n ≥ 60: the recursive four-way construction. -/
private theorem A_witness_recursive (n : ℕ) (hn : 60 ≤ n)
    (_ih : ∀ m, m < n → 1 ≤ m → ∃ (edges : Finset (Finset ℕ)),
      edges.card = m ∧ (vertexSet edges).card = A m ∧ NoLargePartition edges m) :
    ∃ (edges : Finset (Finset ℕ)),
      edges.card = n ∧ (vertexSet edges).card = A n ∧ NoLargePartition edges n := by
  let w : Witness n (A n) := (A_witnessStrong n (by omega)).toWitnessData
  exact ⟨w.edges, w.edgeCard, w.vertexCard, w.noLargePartition⟩

/-- A(n) is realized by a concrete hypergraph with n edges, A(n) vertices, and NoLargePartition. -/
theorem A_witness (n : ℕ) (hn : 1 ≤ n) :
    ∃ (edges : Finset (Finset ℕ)),
      edges.card = n ∧ (vertexSet edges).card = A n ∧ NoLargePartition edges n := by
  let w : Witness n (A n) := (A_witnessStrong n hn).toWitnessData
  exact ⟨w.edges, w.edgeCard, w.vertexCard, w.noLargePartition⟩

/-- For every `n ≥ 1` there exists a hypergraph with exactly `n` distinct edges,
    no partition of size greater than `n`, and exactly `A n` vertices.

    In this edge-set encoding, the "no isolated vertices" clause from the paper is
    implicit because `vertexSet` is defined as the union of the edges. -/
theorem constructive_An (n : ℕ) (hn : 1 ≤ n) :
    ∃ (edges : Finset (Finset ℕ)),
      edges.card = n ∧ (vertexSet edges).card = A n ∧ NoLargePartition edges n := by
  exact A_witness n hn

/-- A(n) ≤ H(n) for n ≥ 1: the constructive witness shows H(n) is at least A(n). -/
theorem A_le_H (n : ℕ) (hn : 1 ≤ n) : A n ≤ H n := by
  let w : Witness n (A n) := (A_witnessStrong n hn).toWitnessData
  unfold H
  apply le_csSup
  · exact H_set_bddAbove n
  · exact ⟨w.edges, w.vertexCard, w.noLargePartition⟩

/-- Pointwise witness form of Theorem `thm:main` from `frontier.tex`.

    For each `n ≥ 1`, the explicit construction gives a hypergraph with exactly `n`
    distinct edges, no partition of size greater than `n`, and exactly `A n`
    vertices. When `n ≥ 15`, this witness has at least `(26/25) k n` vertices.
    As above, "no isolated vertices" is implicit in the edge-set encoding. -/
theorem thm_main_pointwise (n : ℕ) (hn : 1 ≤ n) :
    ∃ edges : Finset (Finset ℕ),
      edges.card = n ∧
        (vertexSet edges).card = A n ∧
        NoLargePartition edges n ∧
        (15 ≤ n → 25 * (vertexSet edges).card ≥ 26 * k n) := by
  let w : MainPointwiseWitness n :=
    { witness := (A_witnessStrong n hn).toWitnessData
      lowerBound := by
        intro hn15
        have hV := ((A_witnessStrong n hn).toWitnessData).vertexCard
        have hU := uniform_26_25 n hn15
        omega }
  exact ⟨w.witness.edges, w.witness.edgeCard, w.witness.vertexCard,
    w.witness.noLargePartition, w.lowerBound⟩

/-- Formalization of Theorem `thm:main` from `frontier.tex`, packaged as a
    witness family.

    The sequence is obtained by choosing, for each `n ≥ 1`, one witness from
    `mainPointwiseWitness`. As above, "no isolated vertices" is implicit in the
    edge-set encoding. -/
theorem thm_main :
    ∃ G : ℕ → Hypergraph ℕ, WitnessFamily G := by
  let G : ℕ → Hypergraph ℕ := fun n =>
    if hn : 1 ≤ n then ((A_witnessStrong n hn).toWitnessData).edges else ∅
  refine ⟨G, ?_⟩
  refine
    { edgeCard := ?_
      noLargePartition := ?_
      lowerBoundWitness := ?_
      lowerBoundH := ?_ }
  · intro n hn
    simpa [G, dif_pos hn] using ((A_witnessStrong n hn).toWitnessData).edgeCard
  · intro n hn
    simpa [G, dif_pos hn] using ((A_witnessStrong n hn).toWitnessData).noLargePartition
  · intro n hn
    have h1 : 1 ≤ n := by omega
    have hV := ((A_witnessStrong n h1).toWitnessData).vertexCard
    have hU := uniform_26_25 n hn
    have hBound :
        25 * (vertexSet (((A_witnessStrong n h1).toWitnessData).edges)).card ≥
          26 * k n := by
      omega
    simpa [G, dif_pos h1] using hBound
  · intro n hn
    have h1 : 1 ≤ n := by omega
    have hA := A_le_H n h1
    have hU := uniform_26_25 n hn
    omega

/-- The `H(n)` lower bound stated as the consequence of Theorem `thm:main`. -/
theorem thm_main_H_lower_bound (n : ℕ) (hn : 15 ≤ n) :
    25 * H n ≥ 26 * k n := by
  rcases thm_main with ⟨_, hG⟩
  exact hG.lowerBoundH n hn


end HypergraphLowerBound
