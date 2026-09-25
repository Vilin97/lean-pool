/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.Separation

/-!
# The Bellenbaum--Diestel induction

The forward half of the tree-width duality theorem: **if no bramble of `H` has
order `> k`, then `treewidth H < k`**, proved exactly as in Bellenbaum--Diestel,
*Two short proofs concerning tree-decompositions*, Theorem 5, except that the
appeal to Menger's theorem is replaced by the explicit separator `rerootSep`
below.

## The induction

A decomposition is **`𝔅`-admissible** when every bag of order `> k` fails to
cover `𝔅`.  The statement proved by induction is

> for every bramble `𝔅` there is a `𝔅`-admissible decomposition of `H`,

by induction on `2 ^ |V| − |𝔅.members|`, i.e. downward on the number of members:
the induction hypothesis is applied to `𝔅 ∪ {C}` for a component `C` of `H − X`,
`X` a minimum cover of `𝔅`.  Applying the result to the *empty* bramble — every
set covers it — forces every bag to have at most `k` vertices, hence
`treewidth H ≤ k − 1`.

## The Menger-free step

Where the paper produces `ℓ = |X|` disjoint `X`–`V_s` paths from Menger's
theorem and reads `|W_t| ≤ |V_t|` off them, this development exhibits the single
set

> `rerootSep t = (bag t \ (C ∪ X)) ∪ (X \ (Z t \ bag t))`

directly, proves that it separates `X` from `bag s` (`rerootSep_separates`,
using only Lemma 1), and concludes `|rerootSep t| ≥ |X|` from Lemma 4 plus
minimality of `X` — the same two facts the paper already uses.  The counting
then falls out (`rerootBag_card_le`).  Mathlib has no Menger's theorem, no
vertex separators, and no treewidth, so this is what makes the campaign finite.
-/

@[expose] public section

namespace Utilities.Treewidth

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {H : SimpleGraph V}

/-! ### Admissibility -/

namespace Bramble

/-- A partial decomposition is **`𝔅`-admissible** when every bag with more than
`k` vertices fails to cover `𝔅`. -/
def Admissible (k : ℕ) (𝔅 : Bramble H) {U : Finset V}
    (D : PartialDecomposition H U) : Prop :=
  ∀ t : D.Node, k < (D.bag t).card → ¬ 𝔅.IsHittingSet (D.bag t)

omit [Fintype V] in
/-- The one-bag decomposition is admissible as soon as its bag is small. -/
theorem admissible_single (𝔅 : Bramble H) {k : ℕ} {X : Finset V} (h : X.card ≤ k) :
    𝔅.Admissible k (PartialDecomposition.single H X) := by
  intro t ht
  rw [PartialDecomposition.single_bag] at ht
  exact absurd ht (Nat.not_lt.mpr h)

omit [Fintype V] in
/-- The two-bag decomposition is admissible when one bag is small and the other
fails to cover. -/
theorem admissible_pairDecomp (𝔅 : Bramble H) {k : ℕ} {X Y : Finset V} (hedge)
    (hX : X.card ≤ k) (hY : ¬ 𝔅.IsHittingSet Y) :
    𝔅.Admissible k (PartialDecomposition.pairDecomp H X Y hedge) := by
  intro t ht
  rcases PartialDecomposition.pairDecomp_bag_cases H X Y hedge t with hb | hb
  · rw [hb] at ht ⊢
    exact absurd ht (Nat.not_lt.mpr hX)
  · rw [hb]
    exact hY

omit [Fintype V] in
/-- A join of admissible decompositions is admissible: its bags are exactly the
bags of the two pieces. -/
theorem admissible_join (𝔅 : Bramble H) {k : ℕ} {U₁ U₂ X : Finset V}
    {D₁ : PartialDecomposition H U₁} {r₁ : D₁.Node} {h₁ : D₁.bag r₁ = X}
    {D₂ : PartialDecomposition H U₂} {r₂ : D₂.Node} {h₂ : D₂.bag r₂ = X}
    {hcap hsep} (a₁ : 𝔅.Admissible k D₁) (a₂ : 𝔅.Admissible k D₂) :
    𝔅.Admissible k (PartialDecomposition.join D₁ r₁ h₁ D₂ r₂ h₂ hcap hsep) := by
  intro t ht
  rcases PartialDecomposition.join_bag_cases D₁ r₁ h₁ D₂ r₂ h₂ hcap hsep t with
    ⟨x, hb⟩ | ⟨x, hb⟩
  · rw [hb] at ht ⊢
    exact a₁ x ht
  · rw [hb] at ht ⊢
    exact a₂ x ht

/-! ### Two small brambles -/

/-- The empty bramble.  Every set covers it, which is what makes the base case
of the induction say something. -/
def empty (H : SimpleGraph V) : Bramble H where
  members := ∅
  connected_mem := by simp
  touching := by simp

omit [Fintype V] in
@[simp] theorem empty_members (H : SimpleGraph V) : (Bramble.empty H).members = ∅ := rfl

omit [Fintype V] in
theorem isHittingSet_empty (S : Finset V) : (Bramble.empty H).IsHittingSet S :=
  fun B hB => absurd hB (Finset.notMem_empty B)

omit [Fintype V] [DecidableEq V] in
/-- A one-element vertex set induces a connected subgraph. -/
theorem connected_induce_singleton (H : SimpleGraph V) (v : V) :
    (H.induce (↑({v} : Finset V) : Set V)).Connected := by
  have : Nonempty ↥((↑({v} : Finset V)) : Set V) := ⟨⟨v, by simp⟩⟩
  have : Subsingleton ↥((↑({v} : Finset V)) : Set V) := by
    constructor
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    subst ha; subst hb; rfl
  exact SimpleGraph.Connected.of_subsingleton

/-- The one-member bramble `{{v}}`, of order `1`.  It is what rules out `k = 0`
when `V` is nonempty. -/
def singletonBramble (H : SimpleGraph V) (v : V) : Bramble H where
  members := {{v}}
  connected_mem := by
    intro B hB
    rw [Finset.mem_singleton] at hB
    subst hB
    exact connected_induce_singleton H v
  touching := by
    intro B hB B' hB'
    rw [Finset.mem_singleton] at hB hB'
    subst hB; subst hB'
    rw [Finset.union_self]
    exact connected_induce_singleton H v

theorem one_le_order_singletonBramble (H : SimpleGraph V) (v : V) :
    1 ≤ (Bramble.singletonBramble H v).order :=
  Bramble.one_le_order _ ⟨{v}, Finset.mem_singleton_self _⟩

/-! ### Adding one member -/

/-- Adjoin a connected set touching every member. -/
def insertMember (𝔅 : Bramble H) (C : Finset V)
    (hC : (H.induce (↑C : Set V)).Connected)
    (htouch : ∀ B ∈ 𝔅.members, (H.induce (↑(C ∪ B) : Set V)).Connected) : Bramble H where
  members := insert C 𝔅.members
  connected_mem := by
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB'
    · exact hC
    · exact 𝔅.connected_mem B hB'
  touching := by
    intro B hB B' hB'
    rcases Finset.mem_insert.mp hB with rfl | hB1
    · rcases Finset.mem_insert.mp hB' with rfl | hB2
      · rw [Finset.union_self]; exact hC
      · exact htouch B' hB2
    · rcases Finset.mem_insert.mp hB' with rfl | hB2
      · rw [Finset.union_comm]; exact htouch B hB1
      · exact 𝔅.touching B hB1 B' hB2

omit [Fintype V] in
@[simp] theorem insertMember_members (𝔅 : Bramble H) (C : Finset V) (hC) (htouch) :
    (𝔅.insertMember C hC htouch).members = insert C 𝔅.members := rfl

omit [Fintype V] in
theorem card_lt_card_insertMember (𝔅 : Bramble H) (C : Finset V) (hC) (htouch)
    (hCnot : C ∉ 𝔅.members) :
    𝔅.members.card < (𝔅.insertMember C hC htouch).members.card := by
  rw [insertMember_members, Finset.card_insert_of_notMem hCnot]
  omega

end Bramble

/-! ### The rerooted decomposition `𝒟_s(H)` -/

section Reroot

variable (D : PartialDecomposition H Finset.univ) (s : D.Node) (X C : Finset V)
  (home : V → D.Node)

/-- The paper's `{x ∈ X | t ∈ t_x T s}`. -/
noncomputable def rerootZ (t : D.Node) : Finset V :=
  @Finset.filter _ (fun x => t ∈ Anc D.isTree s (home x)) (Classical.decPred _) X

omit [DecidableEq V] in
theorem mem_rerootZ_iff (t : D.Node) (x : V) :
    x ∈ rerootZ D s X home t ↔ x ∈ X ∧ t ∈ Anc D.isTree s (home x) :=
  @Finset.mem_filter _ (fun x => t ∈ Anc D.isTree s (home x)) (Classical.decPred _) X x

/-- The paper's `W_t := (V_t ∩ V(H)) ∪ {x ∈ X | t ∈ t_x T s}`, with
`V(H) = C ∪ X`. -/
noncomputable def rerootBag (t : D.Node) : Finset V :=
  (D.bag t ∩ (C ∪ X)) ∪ rerootZ D s X home t

/-- **The separator that replaces Menger's theorem**:
`S t = (V_t \ (C ∪ X)) ∪ (X \ Y_t)` with `Y_t = Z_t \ V_t`. -/
noncomputable def rerootSep (t : D.Node) : Finset V :=
  (D.bag t \ (C ∪ X)) ∪ (X \ (rerootZ D s X home t \ D.bag t))

variable {D s X C home}

/-- **The Menger-free separation lemma** (blueprint §4, Lemma ST-Sep).  Screened
exhaustively over all configurations with `|V| ≤ 4` and `|T| ≤ 3` (680496 of
them) and randomly to `|V| = 7` before being written down.

Discharge plan.  Suppose a walk from `a ∈ X` to `b ∈ bag s` avoids
`rerootSep t`.  Pass to a path `P` meeting `X` only in its first vertex `x` and
`bag s` only in its last vertex `v` (`Walk.dropUntil` at the last `X`-vertex,
then `Walk.takeUntil` at the first `bag s`-vertex; both preserve avoidance).
Then `x ∉ rerootSep t` forces `x ∈ Z t` and `x ∉ bag t`.
* If `t = s`: `v ∈ bag s = bag t`, and avoidance puts `v ∈ C ∪ X`; `v ∈ C`
  contradicts `hsC`, and `v ∈ X` forces `v = x`, contradicting `x ∉ bag t`.
* Otherwise `separates_of_mem_anc` (with `na := home x`, `nb := s`, using
  `anc_root` for `t ∉ Anc s s`) puts a vertex `y ∈ bag t` on `P`; avoidance
  gives `y ∈ C ∪ X`; `y ∈ X` forces `y = x`, again impossible, so `y ∈ C`.  But
  `P` starts outside `C` and ends outside `C`, so the successor of the last
  `C`-vertex of `P` is an `H`-neighbour of `C` outside `C`, hence in `X` by
  `hC.closed`, hence equal to `x` — impossible, since `P` is a path and `x` is
  its first vertex. -/
theorem rerootSep_separates (hhome : ∀ x ∈ X, x ∈ D.bag (home x))
    (hC : IsComponent H X C) (hsC : ∀ v ∈ D.bag s, v ∉ C) (t : D.Node) :
    ∀ a ∈ X, ∀ b ∈ D.bag s, ∀ p : H.Walk a b,
      ∃ x ∈ p.support, x ∈ rerootSep D s X C home t := by
  classical
  -- Three membership facts about the separator, used throughout.
  have S1 : ∀ z : V, z ∈ D.bag t → z ∉ C → z ∉ X → z ∈ rerootSep D s X C home t := by
    intro z hzt hzC hzX
    show z ∈ (D.bag t \ (C ∪ X)) ∪ (X \ (rerootZ D s X home t \ D.bag t))
    refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hzt, ?_⟩)
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hzC h
    · exact hzX h
  have S2 : ∀ z : V, z ∈ X → z ∉ rerootSep D s X C home t →
      t ∈ Anc D.isTree s (home z) ∧ z ∉ D.bag t := by
    intro z hzX hzS
    have h : z ∉ (D.bag t \ (C ∪ X)) ∪ (X \ (rerootZ D s X home t \ D.bag t)) := hzS
    have h3 : z ∈ rerootZ D s X home t \ D.bag t := by
      by_contra hc
      exact h (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzX, hc⟩))
    exact ⟨((mem_rerootZ_iff D s X home t z).mp (Finset.mem_sdiff.mp h3).1).2,
      (Finset.mem_sdiff.mp h3).2⟩
  have S4 : ∀ z : V, z ∈ X → z ∈ D.bag s → z ∈ rerootSep D s X C home s := by
    intro z hzX hzs
    show z ∈ (D.bag s \ (C ∪ X)) ∪ (X \ (rerootZ D s X home s \ D.bag s))
    refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzX, ?_⟩)
    intro hh
    exact (Finset.mem_sdiff.mp hh).2 hzs
  -- The induction on walk length; `a ∈ C` is carried so that a walk leaving `C`
  -- can be resumed at the vertex of `X` where it crosses out.
  have body : ∀ n : ℕ,
      (∀ (a b : V) (q : H.Walk a b), q.length < n → (a ∈ X ∨ a ∈ C) → b ∈ D.bag s →
        ∃ z ∈ q.support, z ∈ rerootSep D s X C home t) →
      ∀ (a b : V) (p : H.Walk a b), p.length ≤ n → (a ∈ X ∨ a ∈ C) → b ∈ D.bag s →
        ∃ z ∈ p.support, z ∈ rerootSep D s X C home t := by
    intro n ih a b p hlen hstart hb
    by_cases haS : a ∈ rerootSep D s X C home t
    · exact ⟨a, p.start_mem_support, haS⟩
    rcases hstart with haX | haC
    · -- The walk starts in `X`.
      obtain ⟨hanc, hat⟩ := S2 a haX haS
      by_cases hts : t = s
      · -- `t = s`: the endpoint itself is in the separator.
        refine ⟨b, p.end_mem_support, ?_⟩
        by_cases hbC : b ∈ C
        · exact absurd hbC (hsC b hb)
        by_cases hbX : b ∈ X
        · rw [hts]
          exact S4 b hbX hb
        · exact S1 b (by rw [hts]; exact hb) hbC hbX
      · -- `t ≠ s`: Lemma 1 puts a vertex of `bag t` on the walk.
        obtain ⟨y, hyp, hyt⟩ := separates_of_mem_anc D s t (Finset.mem_univ a)
          (Finset.mem_univ b) (hhome a haX) hb hanc
          (by rw [anc_root D.isTree s]; exact hts) p (fun z _ => Finset.mem_univ z)
        by_cases hyS : y ∈ rerootSep D s X C home t
        · exact ⟨y, hyp, hyS⟩
        · have hyC : y ∈ C := by
            by_cases hyCmem : y ∈ C
            · exact hyCmem
            by_cases hyXmem : y ∈ X
            · exact absurd hyt (S2 y hyXmem hyS).2
            · exact absurd (S1 y hyt hyCmem hyXmem) hyS
          have hay : a ≠ y := fun h => hC.notMem y hyC (h ▸ haX)
          have hlen2 : (p.takeUntil y hyp).length + (p.dropUntil y hyp).length = p.length := by
            rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec p hyp]
          have hpos : 0 < (p.takeUntil y hyp).length := by
            rcases Nat.eq_zero_or_pos (p.takeUntil y hyp).length with h | h
            · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h) hay
            · exact h
          obtain ⟨z, hz, hzS⟩ := ih y b (p.dropUntil y hyp) (by omega) (Or.inr hyC) hb
          exact ⟨z, SimpleGraph.Walk.support_dropUntil_subset_support p hyp hz, hzS⟩
    · -- The walk starts in `C`; it must leave `C`, and it leaves through `X`.
      have hbC : b ∉ C := hsC b hb
      obtain ⟨d, hd, hd1, hd2⟩ := p.exists_boundary_dart (↑C : Set V)
        (Finset.mem_coe.mpr haC) (fun h => hbC (Finset.mem_coe.mp h))
      have hsndX : d.snd ∈ X := by
        by_contra hn
        exact hd2 (Finset.mem_coe.mpr
          (hC.closed d.fst (Finset.mem_coe.mp hd1) d.snd d.adj hn))
      have hsupp : d.snd ∈ p.support := SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts p hd
      have hne : a ≠ d.snd := fun h => hd2 (h ▸ Finset.mem_coe.mpr haC)
      have hlen2 : (p.takeUntil d.snd hsupp).length + (p.dropUntil d.snd hsupp).length
          = p.length := by
        rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec p hsupp]
      have hpos : 0 < (p.takeUntil d.snd hsupp).length := by
        rcases Nat.eq_zero_or_pos (p.takeUntil d.snd hsupp).length with h | h
        · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h) hne
        · exact h
      obtain ⟨z, hz, hzS⟩ :=
        ih d.snd b (p.dropUntil d.snd hsupp) (by omega) (Or.inl hsndX) hb
      exact ⟨z, SimpleGraph.Walk.support_dropUntil_subset_support p hsupp hz, hzS⟩
  have main : ∀ n : ℕ, ∀ (a b : V) (p : H.Walk a b), p.length ≤ n → (a ∈ X ∨ a ∈ C) →
      b ∈ D.bag s → ∃ z ∈ p.support, z ∈ rerootSep D s X C home t := by
    intro n
    induction n with
    | zero => exact body 0 (fun _ _ _ hq => absurd hq (Nat.not_lt_zero _))
    | succ n ih => exact body (n + 1) (fun a b q hq => ih a b q (by omega))
  exact fun a ha b hbs p => main p.length a b p le_rfl (Or.inl ha) hbs

/-- **Lemma 2, Menger-free** (blueprint §4, Lemma ST-Card).

Discharge plan: `rerootSep_separates` + `Bramble.isHittingSet_of_separates`
(Lemma 4) make `rerootSep t` a cover of `𝔅`, so `hXmin` gives
`X.card ≤ (rerootSep t).card`.  The two pieces of `rerootSep t` are disjoint, so
this reads `|Z t \ bag t| ≤ |bag t \ (C ∪ X)|`; add
`|bag t ∩ (C ∪ X)|` to both sides. -/
theorem rerootBag_card_le (𝔅 : Bramble H)
    (hXcov : 𝔅.IsHittingSet X)
    (hXmin : ∀ S : Finset V, 𝔅.IsHittingSet S → X.card ≤ S.card)
    (hscov : 𝔅.IsHittingSet (D.bag s))
    (hhome : ∀ x ∈ X, x ∈ D.bag (home x))
    (hC : IsComponent H X C) (hsC : ∀ v ∈ D.bag s, v ∉ C) (t : D.Node) :
    (rerootBag D s X C home t).card ≤ (D.bag t).card := by
  classical
  have hZX : rerootZ D s X home t ⊆ X :=
    fun x hx => ((mem_rerootZ_iff D s X home t x).mp hx).1
  have hSep : 𝔅.IsHittingSet (rerootSep D s X C home t) :=
    Bramble.isHittingSet_of_separates 𝔅 hXcov hscov (rerootSep_separates hhome hC hsC t)
  have hcard : X.card ≤ (rerootSep D s X C home t).card := hXmin _ hSep
  have hdisj : Disjoint (D.bag t \ (C ∪ X)) (X \ (rerootZ D s X home t \ D.bag t)) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp hxA).2
      (Finset.mem_union_right _ (Finset.mem_sdiff.mp hxB).1)
  have hsepcard : (rerootSep D s X C home t).card
      = (D.bag t \ (C ∪ X)).card + (X \ (rerootZ D s X home t \ D.bag t)).card := by
    rw [rerootSep, Finset.card_union_of_disjoint hdisj]
  have hsub : (rerootZ D s X home t \ D.bag t) ⊆ X :=
    fun x hx => hZX (Finset.mem_sdiff.mp hx).1
  have hBs : (rerootZ D s X home t \ D.bag t).card
      + (X \ (rerootZ D s X home t \ D.bag t)).card = X.card := by
    have h := Finset.card_inter_add_card_sdiff X (rerootZ D s X home t \ D.bag t)
    rwa [Finset.inter_eq_right.mpr hsub] at h
  have hZsdiff : rerootZ D s X home t \ (D.bag t ∩ (C ∪ X))
      = rerootZ D s X home t \ D.bag t := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter, not_and]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun hb => h hb (Finset.mem_union_right _ (hZX hx))⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun hb _ => h hb⟩
  have hbagcard : (rerootBag D s X C home t).card
      = (D.bag t ∩ (C ∪ X)).card + (rerootZ D s X home t \ D.bag t).card := by
    have h1 : rerootBag D s X C home t
        = (D.bag t ∩ (C ∪ X)) ∪ (rerootZ D s X home t \ (D.bag t ∩ (C ∪ X))) := by
      rw [rerootBag, Finset.union_sdiff_self_eq_union]
    rw [h1, Finset.card_union_of_disjoint Finset.disjoint_sdiff, hZsdiff]
  have hpart : (D.bag t ∩ (C ∪ X)).card + (D.bag t \ (C ∪ X)).card = (D.bag t).card :=
    Finset.card_inter_add_card_sdiff _ _
  omega

/-- **`𝒟_s(H)`**: the same tree, the same `isTree`, only the bags change.  This
is why the campaign never needs to re-root a tree. -/
noncomputable def rerootDecomp (hhome : ∀ x ∈ X, x ∈ D.bag (home x))
    (_hsC : ∀ v ∈ D.bag s, v ∉ C) (_hC : IsComponent H X C) :
    PartialDecomposition H (C ∪ X) where
  Node := D.Node
  tree := D.tree
  isTree := D.isTree
  bag := rerootBag D s X C home
  bag_subset := by
    intro t x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact (Finset.mem_inter.mp h).2
    · exact Finset.mem_union_right _ ((mem_rerootZ_iff D s X home t x).mp h).1
  cover_vertex := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨t, ht⟩ := D.cover_vertex v (Finset.mem_univ v)
      exact ⟨t, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ht, hv⟩)⟩
    · exact ⟨home v, Finset.mem_union_right _
        ((mem_rerootZ_iff D s X home (home v) v).mpr
          ⟨h, self_mem_anc D.isTree s (home v)⟩)⟩
  cover_edge := by
    intro v hv w hw hadj
    obtain ⟨t, htv, htw⟩ := D.cover_edge v (Finset.mem_univ v) w (Finset.mem_univ w) hadj
    exact ⟨t, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨htv, hv⟩),
      Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨htw, hw⟩)⟩
  coherent := by
    intro v hv
    by_cases hvX : v ∈ X
    · have hset : {t : D.Node | v ∈ rerootBag D s X C home t}
          = {t : D.Node | v ∈ D.bag t} ∪ Anc D.isTree s (home v) := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_union, rerootBag, Finset.mem_union,
          Finset.mem_inter, mem_rerootZ_iff]
        constructor
        · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
          · exact Or.inl h1
          · exact Or.inr h2
        · rintro (h | h)
          · exact Or.inl ⟨h, Finset.mem_union.mp hv⟩
          · exact Or.inr ⟨hvX, h⟩
      rw [hset]
      exact SimpleGraph.induce_union_connected
        (D.coherent v (Finset.mem_univ v)).preconnected
        (anc_connected D.isTree s (home v)).preconnected
        ⟨home v, hhome v hvX, self_mem_anc D.isTree s (home v)⟩
    · have hset : {t : D.Node | v ∈ rerootBag D s X C home t}
          = {t : D.Node | v ∈ D.bag t} := by
        ext t
        simp only [Set.mem_ofPred_eq, rerootBag, Finset.mem_union,
          Finset.mem_inter, mem_rerootZ_iff]
        constructor
        · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
          · exact h1
          · exact absurd h1 hvX
        · exact fun h => Or.inl ⟨h, Finset.mem_union.mp hv⟩
      rw [hset]
      exact D.coherent v (Finset.mem_univ v)

@[simp] theorem rerootDecomp_bag (hhome : ∀ x ∈ X, x ∈ D.bag (home x))
    (hsC : ∀ v ∈ D.bag s, v ∉ C) (hC : IsComponent H X C) (t : D.Node) :
    (rerootDecomp hhome hsC hC).bag t = rerootBag D s X C home t := rfl

/-- `W_s = X`. -/
theorem rerootBag_root (_hhome : ∀ x ∈ X, x ∈ D.bag (home x))
    (hsC : ∀ v ∈ D.bag s, v ∉ C) :
    rerootBag D s X C home s = X := by
  ext x
  simp only [rerootBag, Finset.mem_union, Finset.mem_inter, mem_rerootZ_iff]
  constructor
  · rintro (⟨hx1, hx2⟩ | ⟨hx, _⟩)
    · exact hx2.resolve_left (hsC x hx1)
    · exact hx
  · exact fun hx => Or.inr ⟨hx, root_mem_anc D.isTree s (home x)⟩

end Reroot

/-! ### The per-component step -/

/-- **The paper's (∗)**, with the "there is nothing more to show" escape already
discharged by the ambient `hno`.

Discharge plan.  Put `𝔅' := 𝔅 ∪ {C}`.
* If some `B ∈ 𝔅.members` fails to touch `C`, then `Y := C ∪ N(C)` misses `B`,
  so `PartialDecomposition.pairDecomp H X Y` is admissible
  (`Bramble.admissible_pairDecomp`), and `N(C) ⊆ X` makes `X ∪ Y = C ∪ X`.
* Otherwise `𝔅'` is a bramble with strictly more members (`C ∉ 𝔅.members`
  because `X` covers `𝔅` and `C ∩ X = ∅`), so `IH` gives a `𝔅'`-admissible
  `𝒟`.  By `hno`, `𝒟` is not `𝔅`-admissible: some `bag s` with `k < |bag s|`
  covers `𝔅`.  Since `𝒟` is `𝔅'`-admissible, `bag s` misses `C`.  Then
  `rerootDecomp` is the required decomposition: `rerootBag_root` gives the `X`
  part, and admissibility is the paper's last paragraph — a bag `W t` with
  `k < |W t|` meets `C`, so `V t` meets `C`, so `V t` misses some `B ∈ 𝔅`
  (`𝔅'`-admissibility of `𝒟` and `k < |W t| ≤ |V t|` by `rerootBag_card_le`);
  and `W t` misses that same `B`, since a vertex of `W t ∩ B` outside `V t`
  lies in `X`, making `B` a connected set meeting `bag s` and `bag (home x)`
  but not `bag t`, contradicting `separates_of_mem_anc`. -/
theorem component_step (k : ℕ) (𝔅 : Bramble H)
    (IH : ∀ 𝔅' : Bramble H, 𝔅.members.card < 𝔅'.members.card →
      ∃ D : PartialDecomposition H Finset.univ, 𝔅'.Admissible k D)
    (hno : ¬ ∃ D : PartialDecomposition H Finset.univ, 𝔅.Admissible k D)
    (X : Finset V) (hXcov : 𝔅.IsHittingSet X)
    (hXmin : ∀ S : Finset V, 𝔅.IsHittingSet S → X.card ≤ S.card)
    (hXk : X.card ≤ k)
    (C : Finset V) (hC : IsComponent H X C) :
    ∃ D : PartialDecomposition H (C ∪ X), 𝔅.Admissible k D ∧ ∃ r, D.bag r = X := by
  classical
  by_cases htouch : ∀ B ∈ 𝔅.members, (H.induce (↑(C ∪ B) : Set V)).Connected
  · -- `𝔅 ∪ {C}` is a bramble: recurse.
    set 𝔅' := 𝔅.insertMember C hC.connected htouch with h𝔅'
    have hCnot : C ∉ 𝔅.members := by
      intro hmem
      obtain ⟨y, hy⟩ := hXcov C hmem
      exact hC.notMem y (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
    obtain ⟨D, hDadm⟩ := IH 𝔅' (Bramble.card_lt_card_insertMember 𝔅 C _ _ hCnot)
    have hnotadm : ¬ 𝔅.Admissible k D := fun h => hno ⟨D, h⟩
    have hex : ∃ s : D.Node, k < (D.bag s).card ∧ 𝔅.IsHittingSet (D.bag s) := by
      by_contra hcon
      push Not at hcon
      exact hnotadm fun t ht => hcon t ht
    obtain ⟨s, hks, hscov⟩ := hex
    have hsC : ∀ v ∈ D.bag s, v ∉ C := by
      intro v hv hvC
      refine hDadm s hks ?_
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB'
      · exact ⟨v, Finset.mem_inter.mpr ⟨hvC, hv⟩⟩
      · exact hscov B hB'
    choose home hhome0 using fun x : V => D.cover_vertex x (Finset.mem_univ x)
    have hhome : ∀ x ∈ X, x ∈ D.bag (home x) := fun x _ => hhome0 x
    refine ⟨rerootDecomp hhome hsC hC, ?_, s, rerootBag_root hhome hsC⟩
    intro t ht hcov
    replace ht : k < (rerootBag D s X C home t).card := ht
    replace hcov : 𝔅.IsHittingSet (rerootBag D s X C home t) := hcov
    -- `t ≠ s`, since `W s = X` is small
    have hts : t ≠ s := by
      intro h
      have hWX : (rerootBag D s X C home t).card = X.card := by
        rw [h, rerootBag_root hhome hsC]
      omega
    -- `W t` meets `C`, hence so does `bag t`
    have hWsub : rerootBag D s X C home t ⊆ C ∪ X :=
      (rerootDecomp hhome hsC hC).bag_subset t
    have hmeetC : ∃ y, y ∈ C ∧ y ∈ D.bag t := by
      by_contra hcon
      push Not at hcon
      have hsubX : rerootBag D s X C home t ⊆ X := by
        intro y hy
        rcases Finset.mem_union.mp hy with h | h
        · have h1 := Finset.mem_inter.mp h
          exact (Finset.mem_union.mp h1.2).resolve_left (fun hyC => hcon y hyC h1.1)
        · exact ((mem_rerootZ_iff D s X home t y).mp h).1
      have := Finset.card_le_card hsubX
      omega
    obtain ⟨y, hyC, hyt⟩ := hmeetC
    -- `k < |bag t|`
    have hkt : k < (D.bag t).card :=
      lt_of_lt_of_le ht (rerootBag_card_le 𝔅 hXcov hXmin hscov hhome hC hsC t)
    -- `bag t` fails to cover `𝔅'`, and it does meet `C`, so it misses some `B ∈ 𝔅`
    have hmiss : ∃ B ∈ 𝔅.members, ¬ (B ∩ D.bag t).Nonempty := by
      by_contra hcon
      push Not at hcon
      refine hDadm t hkt ?_
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB'
      · exact ⟨y, Finset.mem_inter.mpr ⟨hyC, hyt⟩⟩
      · exact hcon B hB'
    obtain ⟨B, hBmem, hBt⟩ := hmiss
    have hBdisj : ∀ z, z ∈ B → z ∉ D.bag t := by
      intro z hz hzt
      exact hBt ⟨z, Finset.mem_inter.mpr ⟨hz, hzt⟩⟩
    -- `W t` meets `B`, necessarily in `X` and along the path from `home x` to `s`
    obtain ⟨x, hx⟩ := hcov B hBmem
    have hxB : x ∈ B := (Finset.mem_inter.mp hx).1
    have hxW : x ∈ rerootBag D s X C home t := (Finset.mem_inter.mp hx).2
    have hxZ : x ∈ rerootZ D s X home t := by
      rcases Finset.mem_union.mp hxW with h | h
      · exact absurd (Finset.mem_inter.mp h).1 (hBdisj x hxB)
      · exact h
    have hxanc : t ∈ Anc D.isTree s (home x) := ((mem_rerootZ_iff D s X home t x).mp hxZ).2
    -- `B` also meets `bag s`, so Lemma 1 forces `B` to meet `bag t`
    obtain ⟨b, hb⟩ := hscov B hBmem
    have hbB : b ∈ B := (Finset.mem_inter.mp hb).1
    have hbs : b ∈ D.bag s := (Finset.mem_inter.mp hb).2
    obtain ⟨q⟩ := (𝔅.connected_mem B hBmem).preconnected
      ⟨x, Finset.mem_coe.mpr hxB⟩ ⟨b, Finset.mem_coe.mpr hbB⟩
    have key : ∀ (u v : ↥(↑B : Set V)) (r : (H.induce (↑B : Set V)).Walk u v),
        ∀ z ∈ (r.map (SimpleGraph.Embedding.induce (↑B : Set V)).toHom).support, z ∈ B := by
      intro u v r z hz
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨w, _, rfl⟩ := hz
      exact Finset.mem_coe.mp w.2
    have htnotanc : t ∉ Anc D.isTree s s := by
      rw [anc_root D.isTree s]
      exact hts
    obtain ⟨z, hzp, hzt⟩ := separates_of_mem_anc D s t (Finset.mem_univ x)
      (Finset.mem_univ b) (hhome0 x) hbs hxanc htnotanc
      (q.map (SimpleGraph.Embedding.induce (↑B : Set V)).toHom)
      (fun z _ => Finset.mem_univ z)
    exact hBdisj z (key _ _ q z hzp) hzt
  · -- `𝔅 ∪ {C}` is not a bramble: the two-bag decomposition works.
    push Not at htouch
    obtain ⟨B, hBmem, hBnot⟩ := htouch
    set Y : Finset V :=
      C ∪ @Finset.filter _ (fun x => ∃ a ∈ C, H.Adj a x) (Classical.decPred _) X with hY
    have hmemY : ∀ x, x ∈ Y ↔ x ∈ C ∨ (x ∈ X ∧ ∃ a ∈ C, H.Adj a x) := by
      intro x
      rw [hY, Finset.mem_union]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (@Finset.mem_filter _ (fun x => ∃ a ∈ C, H.Adj a x)
            (Classical.decPred _) X x |>.mp h)
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (@Finset.mem_filter _ (fun x => ∃ a ∈ C, H.Adj a x)
            (Classical.decPred _) X x |>.mpr h)
    have hYsub : Y ⊆ C ∪ X := by
      intro x hx
      rcases (hmemY x).mp hx with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ h.1
    have hXY : X ∪ Y = C ∪ X := by
      ext x
      simp only [Finset.mem_union]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Finset.mem_union.mp (hYsub h)
      · rintro (h | h)
        · exact Or.inr ((hmemY x).mpr (Or.inl h))
        · exact Or.inl h
    have hedge : ∀ v ∈ X ∪ Y, ∀ w ∈ X ∪ Y, H.Adj v w →
        (v ∈ X ∧ w ∈ X) ∨ (v ∈ Y ∧ w ∈ Y) := by
      intro v hv w hw hadj
      rw [hXY] at hv hw
      rcases Finset.mem_union.mp hv with hvC | hvX
      · refine Or.inr ⟨(hmemY v).mpr (Or.inl hvC), ?_⟩
        rcases Finset.mem_union.mp hw with hwC | hwX
        · exact (hmemY w).mpr (Or.inl hwC)
        · exact (hmemY w).mpr (Or.inr ⟨hwX, v, hvC, hadj⟩)
      · rcases Finset.mem_union.mp hw with hwC | hwX
        · refine Or.inr ⟨(hmemY v).mpr (Or.inr ⟨hvX, w, hwC, hadj.symm⟩), ?_⟩
          exact (hmemY w).mpr (Or.inl hwC)
        · exact Or.inl ⟨hvX, hwX⟩
    have hYnot : ¬ 𝔅.IsHittingSet Y := by
      intro hcon
      obtain ⟨y, hy⟩ := hcon B hBmem
      have hyB : y ∈ B := (Finset.mem_inter.mp hy).1
      have hyY : y ∈ Y := (Finset.mem_inter.mp hy).2
      refine hBnot ?_
      rw [Finset.coe_union]
      rcases (hmemY y).mp hyY with h | h
      · exact SimpleGraph.induce_union_connected hC.connected.preconnected
          (𝔅.connected_mem B hBmem).preconnected
          ⟨y, Finset.mem_coe.mpr h, Finset.mem_coe.mpr hyB⟩
      · obtain ⟨a, haC, hadj⟩ := h.2
        exact SimpleGraph.connected_induce_union hC.connected.preconnected
          (𝔅.connected_mem B hBmem).preconnected
          (Finset.mem_coe.mpr haC) (Finset.mem_coe.mpr hyB) hadj
    rw [← hXY]
    exact ⟨PartialDecomposition.pairDecomp H X Y hedge,
      𝔅.admissible_pairDecomp hedge hXk hYnot, Sum.inl (), rfl⟩

/-! ### Gluing over the components -/

omit [Fintype V] in
/-- Fold `PartialDecomposition.join` over a closed set of vertices, one
component at a time.

Discharge plan: strong induction on `R.card`.  `R = ∅` is
`PartialDecomposition.single H X` (`Bramble.admissible_single`).  Otherwise pick
`v ∈ R`, put `C := compOf H X R v` (a component by `isComponent_compOf`, inside
`R` by `compOf_subset`), apply `hstep` to `C` and the induction hypothesis to
`R \ C` (closed by `isClosedAway_sdiff`, smaller by `card_sdiff_compOf_lt`), and
`join` them along `X`.  `hcap` holds because `C` and `R \ C` are disjoint and
both miss `X`; `hsep` holds because `hC.closed` forbids `H`-edges from `C` to
`R \ C`. -/
theorem exists_admissible_of_closed (k : ℕ) (𝔅 : Bramble H) (X : Finset V)
    (hXk : X.card ≤ k)
    (hstep : ∀ C : Finset V, IsComponent H X C →
      ∃ D : PartialDecomposition H (C ∪ X), 𝔅.Admissible k D ∧ ∃ r, D.bag r = X) :
    ∀ n : ℕ, ∀ R : Finset V, R.card ≤ n → IsClosedAway H X R →
      ∃ D : PartialDecomposition H (R ∪ X), 𝔅.Admissible k D ∧ ∃ r, D.bag r = X := by
  intro n
  induction n with
  | zero =>
      intro R hRcard _
      have hR : R = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hRcard)
      subst hR
      rw [Finset.empty_union]
      exact ⟨PartialDecomposition.single H X, 𝔅.admissible_single hXk, (), rfl⟩
  | succ n ih =>
      intro R hRcard hclosed
      rcases Finset.eq_empty_or_nonempty R with rfl | ⟨v, hv⟩
      · rw [Finset.empty_union]
        exact ⟨PartialDecomposition.single H X, 𝔅.admissible_single hXk, (), rfl⟩
      · have hCcomp : IsComponent H X (compOf H X R v) := isComponent_compOf hclosed hv
        have hCR : compOf H X R v ⊆ R := compOf_subset H X R v
        obtain ⟨D₂, hD₂adm, r₂, hr₂⟩ := hstep (compOf H X R v) hCcomp
        have hlt : (R \ compOf H X R v).card < R.card := card_sdiff_compOf_lt hv
        obtain ⟨D₁, hD₁adm, r₁, hr₁⟩ :=
          ih (R \ compOf H X R v) (by omega) (isClosedAway_sdiff hclosed v)
        have hcap : ∀ w, w ∈ (R \ compOf H X R v) ∪ X → w ∈ compOf H X R v ∪ X → w ∈ X := by
          intro w h1 h2
          rcases Finset.mem_union.mp h2 with hw | hw
          · exact ((Finset.mem_union.mp h1).resolve_left
              (fun h => (Finset.mem_sdiff.mp h).2 hw))
          · exact hw
        have hsep : ∀ w ∈ (R \ compOf H X R v) ∪ X, ∀ y ∈ compOf H X R v ∪ X,
            w ∉ X → y ∉ X → ¬ H.Adj w y := by
          intro w hw y hy hwX hyX hadj
          have hwR : w ∈ R \ compOf H X R v := (Finset.mem_union.mp hw).resolve_right hwX
          have hyC : y ∈ compOf H X R v := (Finset.mem_union.mp hy).resolve_right hyX
          exact (Finset.mem_sdiff.mp hwR).2 (hCcomp.closed y hyC w hadj.symm hwX)
        have hUeq : ((R \ compOf H X R v) ∪ X) ∪ (compOf H X R v ∪ X) = R ∪ X := by
          ext w
          simp only [Finset.mem_union, Finset.mem_sdiff]
          constructor
          · rintro ((⟨h, _⟩ | h) | (h | h))
            · exact Or.inl h
            · exact Or.inr h
            · exact Or.inl (hCR h)
            · exact Or.inr h
          · rintro (h | h)
            · by_cases hc : w ∈ compOf H X R v
              · exact Or.inr (Or.inl hc)
              · exact Or.inl (Or.inl ⟨h, hc⟩)
            · exact Or.inl (Or.inr h)
        rw [← hUeq]
        exact ⟨PartialDecomposition.join D₁ r₁ hr₁ D₂ r₂ hr₂ hcap hsep,
          𝔅.admissible_join hD₁adm hD₂adm, Sum.inl r₁, hr₁⟩

/-! ### The induction, and its consequence for the treewidth -/

/-- **Theorem 5, forward direction.**  If no bramble of `H` has order `> k`,
then every bramble has an admissible decomposition.

Discharge plan: induction on `n` bounding `Fintype.card (Finset V) −
𝔅.members.card`.  `by_contra hno`; take `X` a minimum cover of `𝔅`
(`Bramble.exists_isHittingSet_card_eq_order` plus
`Bramble.order_le_card_of_isHittingSet`), note `X.card = 𝔅.order ≤ k` by `hk`;
feed `component_step` into `exists_admissible_of_closed` with
`R := Finset.univ \ X`, and rewrite `(Finset.univ \ X) ∪ X = Finset.univ`. -/
theorem exists_admissible (k : ℕ) (hk : ∀ 𝔅 : Bramble H, 𝔅.order ≤ k) :
    ∀ 𝔅 : Bramble H, ∃ D : PartialDecomposition H Finset.univ, 𝔅.Admissible k D := by
  have core : ∀ 𝔅 : Bramble H,
      (∀ 𝔅' : Bramble H, 𝔅.members.card < 𝔅'.members.card →
        ∃ D : PartialDecomposition H Finset.univ, 𝔅'.Admissible k D) →
      ∃ D : PartialDecomposition H Finset.univ, 𝔅.Admissible k D := by
    intro 𝔅 IH
    by_contra hno
    obtain ⟨X, hXcov, hXcard⟩ := 𝔅.exists_isHittingSet_card_eq_order
    have hXmin : ∀ S : Finset V, 𝔅.IsHittingSet S → X.card ≤ S.card := by
      intro S hS
      rw [hXcard]
      exact 𝔅.order_le_card_of_isHittingSet hS
    have hXk : X.card ≤ k := by rw [hXcard]; exact hk 𝔅
    have hclosed : IsClosedAway H X (Finset.univ \ X) := by
      refine ⟨fun w hw => (Finset.mem_sdiff.mp hw).2, ?_⟩
      intro a _ b hab
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hab.2.2⟩
    have huniv : (Finset.univ \ X) ∪ X = Finset.univ := by
      ext w
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
        iff_true]
      exact (em (w ∈ X)).symm.imp id id
    have hget := exists_admissible_of_closed k 𝔅 X hXk
      (fun C hC => component_step k 𝔅 IH hno X hXcov hXmin hXk C hC)
      (Finset.univ \ X).card (Finset.univ \ X) le_rfl hclosed
    rw [huniv] at hget
    obtain ⟨D, hDadm, -⟩ := hget
    exact hno ⟨D, hDadm⟩
  have key : ∀ n : ℕ, ∀ 𝔅 : Bramble H,
      Fintype.card (Finset V) - 𝔅.members.card ≤ n →
      ∃ D : PartialDecomposition H Finset.univ, 𝔅.Admissible k D := by
    intro n
    induction n with
    | zero =>
        intro 𝔅 hn
        refine core 𝔅 (fun 𝔅' hlt => absurd hlt ?_)
        have h1 : 𝔅'.members.card ≤ Fintype.card (Finset V) := by
          simpa [Finset.card_univ] using Finset.card_le_univ 𝔅'.members
        omega
    | succ n ih =>
        intro 𝔅 hn
        exact core 𝔅 (fun 𝔅' hlt => ih 𝔅' (by omega))
  exact fun 𝔅 => key _ 𝔅 le_rfl

/-- Applying `exists_admissible` to the empty bramble bounds the treewidth.

Discharge plan: admissibility for `Bramble.empty` says no bag has more than `k`
vertices (every set covers the empty bramble, `Bramble.isHittingSet_empty`), so
`width ≤ k − 1`; then `treewidth_le_width` on `toTreeDecomposition`. -/
theorem treewidth_le_of_forall_order_le (k : ℕ) (hk : ∀ 𝔅 : Bramble H, 𝔅.order ≤ k) :
    treewidth H ≤ k - 1 := by
  obtain ⟨D, hD⟩ := exists_admissible k hk (Bramble.empty H)
  have hbag : ∀ t : D.Node, (D.bag t).card ≤ k := by
    intro t
    by_contra h
    exact hD t (not_le.mp h) (Bramble.isHittingSet_empty _)
  have hsup : (Finset.univ.sup fun t : D.Node => (D.bag t).card) ≤ k :=
    Finset.sup_le fun t _ => hbag t
  have hw : D.width ≤ k - 1 := by
    unfold PartialDecomposition.width
    omega
  exact le_trans (treewidth_le_width D.toTreeDecomposition) hw

/-- **The hard half of Seymour--Thomas duality**: some bramble has order at
least `treewidth H + 1`.

Discharge plan: apply `treewidth_le_of_forall_order_le` with `k := treewidth H`.
If every bramble had order `≤ treewidth H` we would get
`treewidth H ≤ treewidth H − 1`, impossible unless `treewidth H = 0`; and
`treewidth H = 0` is excluded because `Bramble.singletonBramble H v` has order
`≥ 1` (this is where `Nonempty V` is used). -/
theorem exists_bramble_treewidth_succ_le [Nonempty V] (H : SimpleGraph V) :
    ∃ 𝔅 : Bramble H, treewidth H + 1 ≤ 𝔅.order := by
  by_contra hcon
  push Not at hcon
  have hk : ∀ 𝔅 : Bramble H, 𝔅.order ≤ treewidth H :=
    fun 𝔅 => Nat.lt_succ_iff.mp (hcon 𝔅)
  have h1 := treewidth_le_of_forall_order_le (treewidth H) hk
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  have h2 := Bramble.one_le_order_singletonBramble H v
  have h3 := hk (Bramble.singletonBramble H v)
  omega

end Utilities.Treewidth
