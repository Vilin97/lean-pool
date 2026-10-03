/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.Basic

/-!
# Perfect elimination orders and the clique-bag decomposition

A **perfect elimination order** (PEO) of a graph is a linear ordering of its vertices — here given
by an injective ranking `ord : V → ℕ` — such that the neighbours of each vertex occurring later in
the order form a clique.  Dirac's theorem (available in `Chordal.lean`) yields a PEO for every
finite chordal graph.

Out of a PEO we build the **clique-bag decomposition**: the bag of `v` is `{v} ∪ N⁺(v)`, where
`N⁺(v)` are the neighbours of `v` occurring later in the order.  These bags are cliques, they cover
all vertices and all edges, and *maximality is never required*: the bags form a genuine clique tree
in the sense of `SimpleGraph.CliqueTree`, with parent of `v` the earliest later neighbour of `v`.

## Main definitions

* `SimpleGraph.IsPEO`
* `SimpleGraph.laterNbrs`, `SimpleGraph.peoBag`, `SimpleGraph.peoParent`, `SimpleGraph.peoRank`
* `SimpleGraph.IsPEO.cliqueTree` — the clique tree carried by the bag decomposition

## Main results

* `SimpleGraph.IsChordal.exists_isPEO` — a finite chordal graph admits a perfect elimination order
* `SimpleGraph.IsPEO.peoBag_isClique`, `SimpleGraph.IsPEO.exists_peoBag_of_adj`
* `SimpleGraph.IsPEO.card_edgeFinset_eq_sum_card_laterNbrs` — edge accounting: each edge is charged
  exactly once, to its earlier endpoint
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A **perfect elimination order** of `G`, given by an injective ranking `ord : V → ℕ`: the
neighbours of a vertex that come later in the order form a clique. -/
structure IsPEO (G : SimpleGraph V) (ord : V → ℕ) : Prop where
  /-- The ranking is injective, i.e. it is a linear order on the vertices. -/
  injective : Function.Injective ord
  /-- The later neighbourhood of every vertex is a clique. -/
  isClique_later : ∀ v : V, G.IsClique {u | ord v < ord u ∧ G.Adj v u}

/-! ### Existence of a perfect elimination order -/

/-- Every nonempty finite vertex set in a chordal graph contains a vertex whose neighbours
within that set form a clique. -/
theorem IsChordal.exists_simplicial_in_finset (hG : G.IsChordal) (S : Finset V)
    (hSne : S.Nonempty) :
    ∃ z ∈ S, ∀ a ∈ S, ∀ b ∈ S, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b := by
  classical
  obtain ⟨w, hw⟩ := hSne
  let _ : Nonempty ((S : Set V)) := ⟨⟨w, by simpa using hw⟩⟩
  obtain ⟨z, hz⟩ := (hG.induce (S : Set V)).exists_isSimplicial
  refine ⟨z, by simp, ?_⟩
  intro a ha b hb hva hvb hab
  have ha' : (⟨a, by simpa using ha⟩ : (S : Set V)) ∈
      (G.induce (S : Set V)).neighborSet z := hva
  have hb' : (⟨b, by simpa using hb⟩ : (S : Set V)) ∈
      (G.induce (S : Set V)).neighborSet z := hvb
  exact hz ha' hb' (by simp [Subtype.ext_iff, hab])

/-- Relative simplicial elimination produces an injective ranking on every finite set. -/
theorem exists_rank_of_simplicial_elimination
    (helim : ∀ (S : Finset V), S.Nonempty → ∃ z ∈ S,
      ∀ a ∈ S, ∀ b ∈ S, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → ∃ f : V → ℕ, Set.InjOn f S ∧
      ∀ v ∈ S, G.IsClique {u | u ∈ S ∧ f v < f u ∧ G.Adj v u} := by
  classical
  intro n
  induction n with
  | zero =>
      intro S hS
      rw [Finset.card_eq_zero] at hS
      subst hS
      exact ⟨fun _ => 0, by simp, by simp⟩
  | succ n ih =>
      intro S hS
      have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨z, hvS, hsimp⟩ := helim S hSne
      obtain ⟨f', hinj', hcl'⟩ := ih (S.erase (z : V))
        (by rw [Finset.card_erase_of_mem hvS, hS]; omega)
      refine ⟨fun u => if u = (z : V) then 0 else f' u + 1, ?_, ?_⟩
      · intro a ha b hb hab
        simp only at hab
        by_cases hav : a = (z : V)
        · by_cases hbv : b = (z : V)
          · rw [hav, hbv]
          · rw [ite_eq_left hav, ite_eq_right hbv] at hab
            exact absurd hab.symm (Nat.succ_ne_zero _)
        · by_cases hbv : b = (z : V)
          · rw [ite_eq_right hav, ite_eq_left hbv] at hab
            exact absurd hab (Nat.succ_ne_zero _)
          · rw [ite_eq_right hav, ite_eq_right hbv] at hab
            exact hinj' (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hav, Finset.mem_coe.1 ha⟩))
              (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hbv, Finset.mem_coe.1 hb⟩)) (by omega)
      · intro u hu
        by_cases huv : u = (z : V)
        · subst huv
          intro a ha b hb hab
          exact hsimp a ha.1 b hb.1 ha.2.2 hb.2.2 hab
        · have hmem : u ∈ S.erase (z : V) := Finset.mem_erase.2 ⟨huv, hu⟩
          refine (hcl' u hmem).subset ?_
          intro x hx
          obtain ⟨hxS, hlt, hadj⟩ := hx
          simp only [huv, ite_false] at hlt
          have hxv : x ≠ (z : V) := by
            rintro rfl
            simp at hlt
          refine ⟨Finset.mem_erase.2 ⟨hxv, hxS⟩, ?_, hadj⟩
          simp only [hxv, ite_false] at hlt
          omega

/-- Relative simpliciality in every nonempty finite vertex set yields an elimination order. -/
theorem exists_isPEO_of_simplicial_in_finset [Finite V]
    (hsimp : ∀ (S : Finset V), S.Nonempty →
      ∃ z ∈ S, ∀ a ∈ S, ∀ b ∈ S, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b) :
    ∃ ord : V → ℕ, G.IsPEO ord := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  obtain ⟨f, hinj, hclique⟩ := exists_rank_of_simplicial_elimination
    hsimp (Finset.univ.card) Finset.univ rfl
  refine ⟨f, ⟨fun a b hab => hinj (Finset.mem_coe.2 (Finset.mem_univ a))
      (Finset.mem_coe.2 (Finset.mem_univ b)) hab, fun v => ?_⟩⟩
  have := hclique v (Finset.mem_univ v)
  refine this.subset ?_
  intro u hu
  exact ⟨Finset.mem_univ u, hu.1, hu.2⟩

/-- **Every finite chordal graph has a perfect elimination order.** -/
theorem IsChordal.exists_isPEO [Finite V] (hG : G.IsChordal) :
    ∃ ord : V → ℕ, G.IsPEO ord :=
  exists_isPEO_of_simplicial_in_finset hG.exists_simplicial_in_finset

/-! ### The clique-bag decomposition of a perfect elimination order -/

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The neighbours of `v` occurring later than `v` in the order `ord`. -/
def laterNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (ord : V → ℕ) (v : V) : Finset V :=
  Finset.univ.filter fun u => ord v < ord u ∧ G.Adj v u

/-- The **clique bag** of `v`: the vertex together with its later neighbours. -/
def peoBag (G : SimpleGraph V) [DecidableRel G.Adj] (ord : V → ℕ) (v : V) : Finset V :=
  insert v (laterNbrs G ord v)

/-- The parent of `v`: its earliest later neighbour, if any. -/
noncomputable def peoParent (G : SimpleGraph V) [DecidableRel G.Adj] (ord : V → ℕ) (v : V) :
    Option V :=
  if h : (laterNbrs G ord v).Nonempty then
    some (Finset.exists_min_image (laterNbrs G ord v) ord h).choose
  else none

/-- The rank of `v`: the number of vertices occurring after `v`. -/
def peoRank (ord : V → ℕ) (v : V) : ℕ := (Finset.univ.filter fun u => ord v < ord u).card

omit [DecidableEq V] in
@[simp] theorem mem_laterNbrs {ord : V → ℕ} {v u : V} :
    u ∈ laterNbrs G ord v ↔ ord v < ord u ∧ G.Adj v u := by
  simp [laterNbrs]

@[simp] theorem mem_peoBag {ord : V → ℕ} {v u : V} :
    u ∈ peoBag G ord v ↔ u = v ∨ (ord v < ord u ∧ G.Adj v u) := by
  simp [peoBag]

theorem self_mem_peoBag {ord : V → ℕ} (v : V) : v ∈ peoBag G ord v := by simp

omit [DecidableEq V] in
theorem notMem_laterNbrs_self {ord : V → ℕ} (v : V) : v ∉ laterNbrs G ord v := by simp

theorem card_peoBag {ord : V → ℕ} (v : V) :
    (peoBag G ord v).card = (laterNbrs G ord v).card + 1 := by
  rw [peoBag, Finset.card_insert_of_notMem (notMem_laterNbrs_self v)]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem peoRank_lt_of_ord_lt {ord : V → ℕ} {u v : V} (h : ord u < ord v) :
    peoRank ord v < peoRank ord u := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    omega
  · intro hsub
    have : v ∈ Finset.univ.filter fun u => ord v < ord u := by
      exact hsub (by simp [h])
    simp at this

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem peoRank_injective {ord : V → ℕ} (h : Function.Injective ord) :
    Function.Injective (peoRank ord) := by
  intro u v huv
  rcases lt_trichotomy (ord u) (ord v) with hlt | heq | hgt
  · exact absurd huv (by simpa using (peoRank_lt_of_ord_lt hlt).ne')
  · exact h heq
  · exact absurd huv (by simpa using (peoRank_lt_of_ord_lt hgt).ne)

omit [DecidableEq V] in
theorem peoParent_spec {ord : V → ℕ} {v p : V} (hp : peoParent G ord v = some p) :
    p ∈ laterNbrs G ord v ∧ ∀ u ∈ laterNbrs G ord v, ord p ≤ ord u := by
  unfold peoParent at hp
  split at hp
  · rename_i hne
    obtain ⟨hmem, hmin⟩ := (Finset.exists_min_image (laterNbrs G ord v) ord hne).choose_spec
    rw [Option.some_inj] at hp
    subst hp
    exact ⟨hmem, hmin⟩
  · exact absurd hp (by simp)

omit [DecidableEq V] in
theorem peoParent_eq_some {ord : V → ℕ} {v : V} (hne : (laterNbrs G ord v).Nonempty) :
    ∃ p, peoParent G ord v = some p := by
  unfold peoParent
  rw [dite_eq_left hne]
  exact ⟨_, rfl⟩

namespace IsPEO

variable {ord : V → ℕ} (h : G.IsPEO ord)
include h

theorem peoBag_isClique (v : V) : G.IsClique (peoBag G ord v : Set V) := by
  have hcl : G.IsClique ((laterNbrs G ord v : Finset V) : Set V) := by
    refine (h.isClique_later v).subset ?_
    intro u hu
    simpa using hu
  have : ((peoBag G ord v : Finset V) : Set V) = insert v ((laterNbrs G ord v : Finset V) : Set V)
      := by simp [peoBag]
  rw [this]
  refine hcl.insert ?_
  intro b hb _
  have : b ∈ laterNbrs G ord v := by simpa using hb
  exact (mem_laterNbrs.1 this).2

theorem exists_peoBag_of_adj {u v : V} (hadj : G.Adj u v) :
    ∃ w, u ∈ peoBag G ord w ∧ v ∈ peoBag G ord w := by
  rcases lt_trichotomy (ord u) (ord v) with hlt | heq | hgt
  · exact ⟨u, self_mem_peoBag u, by simp [hlt, hadj]⟩
  · exact absurd (h.injective heq) hadj.ne
  · exact ⟨v, by simp [hgt, hadj.symm], self_mem_peoBag v⟩

theorem mem_peoBag_peoParent {v w : V} (hw : w ∈ peoBag G ord v) (hne : w ≠ v) :
    ∃ p, peoParent G ord v = some p ∧ w ∈ peoBag G ord p := by
  have hwlater : w ∈ laterNbrs G ord v := by
    rcases mem_peoBag.1 hw with rfl | hx
    · exact absurd rfl hne
    · exact mem_laterNbrs.2 hx
  obtain ⟨p, hp⟩ := peoParent_eq_some ⟨w, hwlater⟩
  refine ⟨p, hp, ?_⟩
  obtain ⟨hpmem, hpmin⟩ := peoParent_spec hp
  by_cases hpw : p = w
  · exact hpw ▸ self_mem_peoBag p
  · have hlt : ord p < ord w :=
      lt_of_le_of_ne (hpmin w hwlater) (fun hEq => hpw (h.injective hEq))
    have hadj : G.Adj p w := by
      refine h.isClique_later v ?_ ?_ hpw
      · exact ⟨(mem_laterNbrs.1 hpmem).1, (mem_laterNbrs.1 hpmem).2⟩
      · exact ⟨(mem_laterNbrs.1 hwlater).1, (mem_laterNbrs.1 hwlater).2⟩
    exact mem_peoBag.2 (Or.inr ⟨hlt, hadj⟩)

/-- **The clique-bag decomposition of a perfect elimination order is a clique tree.**
No maximality of the bags is required. -/
@[expose]
noncomputable def cliqueTree : CliqueTree G V where
  bag := peoBag G ord
  parent := peoParent G ord
  rank := peoRank ord
  top := id
  rank_injective := peoRank_injective h.injective
  rank_parent_lt := by
    intro i j hij
    exact peoRank_lt_of_ord_lt (mem_laterNbrs.1 (peoParent_spec hij).1).1
  bag_isClique := h.peoBag_isClique
  mem_bag_top := fun v => self_mem_peoBag v
  exists_bag_of_adj := h.exists_peoBag_of_adj
  mem_bag_parent := fun hv hi => mem_peoBag_peoParent h hv (Ne.symm hi)

@[simp] theorem cliqueTree_bag (v : V) : (h.cliqueTree).bag v = peoBag G ord v := rfl

@[simp] theorem cliqueTree_top (v : V) : (h.cliqueTree).top v = v := rfl

/-! ### Edge accounting -/

omit [DecidableEq V] in
/-- **Unique edge assignment along a PEO.** Every edge is charged to its earlier endpoint, and the
total count of edges is the total number of later neighbours. -/
theorem card_edgeFinset_eq_sum_card_laterNbrs :
    G.edgeFinset.card = ∑ v : V, (laterNbrs G ord v).card := by
  classical
  set D : Finset (V × V) := Finset.univ.filter (fun p => ord p.1 < ord p.2 ∧ G.Adj p.1 p.2)
    with hD
  have h1 : D.card = ∑ v : V, (laterNbrs G ord v).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hset : D.filter (fun p => p.1 = v) = (laterNbrs G ord v).image (fun u => (v, u)) := by
      ext p
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        mem_laterNbrs, Prod.ext_iff]
      constructor
      · rintro ⟨⟨hlt, hadj⟩, rfl⟩
        exact ⟨p.2, ⟨hlt, hadj⟩, rfl, rfl⟩
      · rintro ⟨u, ⟨hlt, hadj⟩, rfl, rfl⟩
        exact ⟨⟨hlt, hadj⟩, rfl⟩
    rw [hset, Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.injEq _ _ _ _ ▸ hab).2)]
  rw [← h1]
  refine (Finset.card_bij (fun (p : V × V) _ => s(p.1, p.2)) ?_ ?_ ?_).symm
  · intro p hp
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simpa using hp.2
  · intro a ha b hb hab
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases Sym2.eq_iff.1 hab with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact Prod.ext h1' h2'
    · exfalso
      rw [h1', h2'] at ha
      omega
  · intro e he
    induction e with
    | _ x y =>
      have hadj : G.Adj x y := by simpa using he
      rcases lt_trichotomy (ord x) (ord y) with hlt | heq | hgt
      · exact ⟨(x, y), by simp [hD, hlt, hadj], rfl⟩
      · exact absurd (h.injective heq) hadj.ne
      · exact ⟨(y, x), by simp [hD, hgt, hadj.symm], Sym2.eq_swap⟩

/-- The bag form of the edge accounting: each bag contributes its size minus one. -/
theorem card_edgeFinset_add_card_eq_sum_card_peoBag :
    G.edgeFinset.card + Fintype.card V = ∑ v : V, (peoBag G ord v).card := by
  rw [card_edgeFinset_eq_sum_card_laterNbrs h]
  simp [card_peoBag, Finset.sum_add_distrib, Finset.card_univ]

end IsPEO

/-- **Every finite chordal graph has a clique tree**, namely the clique-bag decomposition of any
perfect elimination order. -/
theorem IsChordal.nonempty_cliqueTree {V : Type*} [Finite V]
    {G : SimpleGraph V} (hG : G.IsChordal) : Nonempty (CliqueTree G V) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨ord, h⟩ := hG.exists_isPEO
  exact ⟨h.cliqueTree⟩

end SimpleGraph
