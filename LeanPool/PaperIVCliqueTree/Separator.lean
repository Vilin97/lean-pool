/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.Helly
public import LeanPool.PaperIVCliqueTree.Maximal
import Mathlib.Order.BourbakiWitt

/-!
# Clique trees and minimal separators

`SimpleGraph.CliqueTree.branch_separator` shows that the intersection `bag i ∩ bag j` of two bags
joined by a tree edge separates the branch below `i` from the rest of the graph.  This file proves
that these intersections are exactly the *minimal* separators of the graph.

## Main results

* `SimpleGraph.CliqueTree.separates_bag_inter` — the separation statement in the form used below
* `SimpleGraph.CliqueTree.isMinimalSeparator_bag_inter` — for a clique tree whose bags are the
  maximal cliques (pairwise distinct), the intersection along a tree edge is a minimal separator
* `SimpleGraph.CliqueTree.exists_parent_eq_of_isMinimalSeparator` — conversely, every minimal
  separator of two vertices joined by a walk is such an intersection

Both hypotheses are shown to be necessary:
`SimpleGraph.CliqueTree.not_exists_isMinimalSeparator_dupBagTree` refutes the direct statement for
a clique tree with repeated maximal bags, and
`SimpleGraph.CliqueTree.not_exists_parent_eq_isolatedTree` refutes the converse for a disconnected
graph.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {ι : Type*}

/-- Reachability avoiding a set of vertices: the relation whose non-existence is the content of
`SimpleGraph.Separates`. -/
private def Avoid (G : SimpleGraph V) (S : Set V) (x y : V) : Prop :=
  Relation.ReflTransGen (fun p q => p ∉ S ∧ q ∉ S ∧ G.Adj p q) x y

private theorem avoid_refl {S : Set V} (x : V) : Avoid G S x x := Relation.ReflTransGen.refl

private theorem avoid_trans {S : Set V} {x y z : V} (h₁ : Avoid G S x y) (h₂ : Avoid G S y z) :
    Avoid G S x z := Relation.ReflTransGen.trans h₁ h₂

private theorem avoid_step {S : Set V} {x y : V} (hx : x ∉ S) (hy : y ∉ S) (hadj : G.Adj x y) :
    Avoid G S x y := Relation.ReflTransGen.single ⟨hx, hy, hadj⟩

private theorem avoid_symm {S : Set V} {x y : V} (h : Avoid G S x y) : Avoid G S y x := by
  induction h with
  | refl => exact avoid_refl _
  | tail _ hstep ih =>
      exact avoid_trans (avoid_step hstep.2.1 hstep.1 hstep.2.2.symm) ih

private theorem avoid_notMem {S : Set V} {x y : V} (hx : x ∉ S) (h : Avoid G S x y) : y ∉ S := by
  induction h with
  | refl => exact hx
  | tail _ hstep _ => exact hstep.2.1

private theorem separates_iff {S : Set V} {a b : V} :
    G.Separates S a b ↔ a ∉ S ∧ b ∉ S ∧ ¬ Avoid G S a b := Iff.rfl

namespace CliqueTree

variable {T : CliqueTree G ι}

/-- **Separation by a tree edge.** If `a` lies in the branch below `i` and `b` does not, and
neither lies in the separator `bag i ∩ bag j` of the tree edge `i → j`, then that separator
separates `a` from `b`. -/
theorem separates_bag_inter [DecidableEq V] {i j : ι} (hp : T.parent i = some j) {a b : V}
    (ha : a ∈ T.branch i) (hb : b ∉ T.branch i) (haS : a ∉ T.bag i ∩ T.bag j)
    (hbS : b ∉ T.bag i ∩ T.bag j) :
    G.Separates ((T.bag i ∩ T.bag j : Finset V) : Set V) a b := by
  refine ⟨by simpa using haS, by simpa using hbS, fun hreach => ?_⟩
  have key : ∀ x, Avoid G ((T.bag i ∩ T.bag j : Finset V) : Set V) a x → x ∈ T.branch i := by
    intro x hx
    induction hx with
    | refl => exact ha
    | tail _ hstep ih =>
        by_contra hy
        exact not_adj_of_branch_separator hp ih (by simpa using hstep.1) hy hstep.2.2
  exact hb (key b hreach)

/-- **The separator of a tree edge is a minimal separator**, for a clique tree whose bags are the
maximal cliques of `G`, each occurring once. -/
theorem isMinimalSeparator_bag_inter [Fintype V] [DecidableEq V] (T : CliqueTree G ι)
    (hmax : ∀ i, G.IsMaximalCliqueOn Finset.univ (T.bag i)) (hinj : Function.Injective T.bag)
    {i j : ι} (hp : T.parent i = some j) :
    ∃ a b, G.IsMinimalSeparator ((T.bag i ∩ T.bag j : Finset V) : Set V) a b := by
  classical
  have hne : i ≠ j := fun h => absurd (T.rank_parent_lt hp) (by rw [h]; exact lt_irrefl _)
  -- the two bags are incomparable, because they are distinct maximal cliques
  have hnotsub : ∀ k l : ι, k ≠ l → ¬ T.bag k ⊆ T.bag l := by
    intro k l hkl hsub
    exact hkl (hinj ((hmax k).eq_of_subset (Finset.subset_univ _) (hmax l).isClique hsub).symm)
  obtain ⟨a, haI, haJ⟩ : ∃ a, a ∈ T.bag i ∧ a ∉ T.bag j := by
    by_contra hcon
    push Not at hcon
    exact hnotsub i j hne hcon
  obtain ⟨b, hbJ, hbI⟩ : ∃ b, b ∈ T.bag j ∧ b ∉ T.bag i := by
    by_contra hcon
    push Not at hcon
    exact hnotsub j i (Ne.symm hne) hcon
  have hbranch : b ∉ T.branch i := by
    rintro ⟨m, hmi, hbm⟩
    rcases (hmi.comparable (isAncestor_top_of_mem_bag hbm)) with h | h
    · exact hbI (mem_bag_of_isAncestor hbm hmi h)
    · have hji : T.IsAncestor j i := (isAncestor_top_of_mem_bag hbJ).trans h
      exact hne ((isAncestor_parent hp).antisymm hji)
  have haS : a ∉ T.bag i ∩ T.bag j := fun h => haJ (Finset.mem_inter.1 h).2
  have hbS : b ∉ T.bag i ∩ T.bag j := fun h => hbI (Finset.mem_inter.1 h).1
  refine ⟨a, b, separates_bag_inter hp (mem_branch_self haI) hbranch haS hbS, ?_⟩
  -- minimality: every separator vertex is adjacent to both `a` and `b`
  intro W hW hsep
  obtain ⟨s, hsS, hsW⟩ : ∃ s, s ∈ ((T.bag i ∩ T.bag j : Finset V) : Set V) ∧ s ∉ W := by
    by_contra hcon
    push Not at hcon
    exact absurd (Set.Subset.antisymm hW.1 hcon) (ne_of_lt hW)
  obtain ⟨hsI, hsJ⟩ := Finset.mem_inter.1 (by simpa using hsS)
  have hsa : G.Adj a s := T.bag_isClique i (by simpa using haI) (by simpa using hsI)
    (by rintro rfl; exact haJ hsJ)
  have hsb : G.Adj s b := T.bag_isClique j (by simpa using hsJ) (by simpa using hbJ)
    (by rintro rfl; exact hbI hsI)
  exact hsep.2.2 (avoid_trans (avoid_step hsep.1 hsW hsa) (avoid_step hsW hsep.2.1 hsb))

/-! ### The converse: every minimal separator is the intersection of two adjacent bags -/

section Converse

/-- Among the vertices reachable from `c` while avoiding `S`, one has a top node of minimal rank:
the top node of the subtree spanned by that part of the graph. -/
private theorem exists_min_top [Finite V] (T : CliqueTree G ι) (S : Set V) (c : V) :
    ∃ v, Avoid G S c v ∧ ∀ x, Avoid G S c x → T.rank (T.top v) ≤ T.rank (T.top x) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  have hne : (Finset.univ.filter fun x => Avoid G S c x).Nonempty :=
    ⟨c, by simp [avoid_refl]⟩
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image _ (fun x => T.rank (T.top x)) hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact ⟨v, hv, fun x hx => hmin x (by simp [hx])⟩

private theorem avoid_iff_of_avoid {S : Set V} {c v x : V} (hcv : Avoid G S c v) :
    Avoid G S c x ↔ Avoid G S v x :=
  ⟨fun h => avoid_trans (avoid_symm hcv) h, fun h => avoid_trans hcv h⟩

/-- All the top nodes of a connected part of the graph lie below the one of minimal rank. -/
private theorem isAncestor_top_root (T : CliqueTree G ι) {S : Set V} {v : V}
    (hmin : ∀ x, Avoid G S v x → T.rank (T.top v) ≤ T.rank (T.top x)) :
    ∀ x, Avoid G S v x → T.IsAncestor (T.top x) (T.top v) := by
  intro x hx
  induction hx with
  | refl => exact isAncestor_refl _
  | @tail y z hvy hstep ih =>
      obtain ⟨k, hyk, hzk⟩ := T.exists_bag_of_adj hstep.2.2
      rcases top_comparable_of_mem_bag hzk hyk with h | h
      · exact h.trans ih
      · rcases ih.comparable h with h' | h'
        · have hrank := hmin z (Relation.ReflTransGen.tail hvy hstep)
          have heq : T.top v = T.top z := T.rank_injective (le_antisymm hrank h'.rank_le)
          rw [heq]
        · exact h'

/-- The nodes met by a connected part of the graph form a subtree: every node between the top node
of one of its vertices and the top node of the whole part meets it again. -/
private theorem exists_mem_bag_between (T : CliqueTree G ι) {S : Set V} {v : V} :
    ∀ x, Avoid G S v x → ∀ m, T.IsAncestor (T.top x) m → T.IsAncestor m (T.top v) →
      ∃ w, Avoid G S v w ∧ w ∈ T.bag m := by
  intro x hx
  induction hx with
  | refl =>
      intro m h1 h2
      exact ⟨v, avoid_refl v, (h1.antisymm h2) ▸ T.mem_bag_top v⟩
  | @tail y z hvy hstep ih =>
      intro m h1 h2
      obtain ⟨k, hyk, hzk⟩ := T.exists_bag_of_adj hstep.2.2
      rcases top_comparable_of_mem_bag hyk hzk with h | h
      · exact ih m (h.trans h1) h2
      · rcases h1.comparable h with h' | h'
        · exact ⟨y, hvy, mem_bag_of_isAncestor hyk ((isAncestor_top_of_mem_bag hzk).trans h1) h'⟩
        · exact ih m h' h2

/-- Two vertices joined by a walk have top nodes in the same tree of the clique forest. -/
private theorem exists_common_ancestor_of_reachable (T : CliqueTree G ι) {a b : V}
    (h : G.Reachable a b) : ∃ w, T.IsAncestor (T.top a) w ∧ T.IsAncestor (T.top b) w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨T.top _, isAncestor_refl _, isAncestor_refl _⟩
  | @cons u v w hadj q ih =>
      obtain ⟨w', h1, h2⟩ := ih
      obtain ⟨k, hu, hv⟩ := T.exists_bag_of_adj hadj
      rcases top_comparable_of_mem_bag hu hv with h | h
      · exact ⟨w', h.trans h1, h2⟩
      · rcases h.comparable h1 with h' | h'
        · exact ⟨w', h', h2⟩
        · exact ⟨T.top u, isAncestor_refl _, h2.trans h'⟩

/-- The heart of the converse: one of the two sides of the separation produces a tree edge whose
separator is contained in `S` and which separates `a` from `b`. -/
private theorem exists_sep_edge [DecidableEq V] (T : CliqueTree G ι) {S : Set V} {a b : V}
    (hbags : ∀ (k : ι) (u w : V), u ∈ T.bag k → w ∈ T.bag k → Avoid G S a u → Avoid G S b w →
      False)
    (haS : a ∉ S) {vA vB : V} (hvA : Avoid G S a vA) (hvB : Avoid G S b vB)
    (htopA : ∀ x, Avoid G S a x → T.IsAncestor (T.top x) (T.top vA))
    (htopB : ∀ x, Avoid G S b x → T.IsAncestor (T.top x) (T.top vB))
    (hbetB : ∀ x, Avoid G S b x → ∀ m, T.IsAncestor (T.top x) m → T.IsAncestor m (T.top vB) →
      ∃ w, Avoid G S b w ∧ w ∈ T.bag m)
    (hcase : ¬ (T.IsAncestor (T.top vB) (T.top vA) ∧ T.top vB ≠ T.top vA))
    (hcommon : ∃ w, T.IsAncestor (T.top vA) w ∧ T.IsAncestor (T.top vB) w) :
    ∃ i j, T.parent i = some j ∧ ((T.bag i ∩ T.bag j : Finset V) : Set V) ⊆ S ∧
      a ∈ T.branch i ∧ b ∉ T.branch i := by
  have hrne : T.top vA ≠ T.top vB := fun h =>
    hbags (T.top vA) vA vB (T.mem_bag_top vA) (h ▸ T.mem_bag_top vB) hvA hvB
  obtain ⟨w, hAw, hBw⟩ := hcommon
  obtain ⟨j, hj⟩ : ∃ j, T.parent (T.top vA) = some j := by
    rcases Relation.ReflTransGen.cases_head hAw with hrfl | ⟨c, hc, -⟩
    · exact absurd ⟨hrfl ▸ hBw, Ne.symm hrne⟩ hcase
    · exact ⟨c, hc⟩
  refine ⟨T.top vA, j, hj, ?_, ⟨T.top a, htopA a (avoid_refl a), T.mem_bag_top a⟩, ?_⟩
  · intro x hx
    obtain ⟨hxA, hxJ⟩ := Finset.mem_inter.1 (by simpa using hx)
    by_contra hxS
    have hxAv : Avoid G S a x := by
      rcases eq_or_ne x vA with rfl | hne
      · exact hvA
      · exact avoid_trans hvA (avoid_step (avoid_notMem haS hvA) hxS
          (T.bag_isClique (T.top vA) (by simpa using T.mem_bag_top vA) (by simpa using hxA)
            (Ne.symm hne)))
    have hjA : T.IsAncestor j (T.top vA) := (isAncestor_top_of_mem_bag hxJ).trans (htopA x hxAv)
    have heq : T.top vA = j := (isAncestor_parent hj).antisymm hjA
    exact absurd (T.rank_parent_lt hj) (by rw [heq]; exact lt_irrefl _)
  · rintro ⟨m, hmA, hbm⟩
    rcases hmA.comparable (isAncestor_top_of_mem_bag hbm) with h | h
    · exact hbags (T.top vA) vA b (T.mem_bag_top vA) (mem_bag_of_isAncestor hbm hmA h) hvA
        (avoid_refl b)
    · rcases h.comparable (htopB b (avoid_refl b)) with h1 | h1
      · obtain ⟨w', hw', hw'mem⟩ := hbetB b (avoid_refl b) (T.top vA) h h1
        exact hbags (T.top vA) vA w' (T.mem_bag_top vA) hw'mem hvA hw'
      · exact hcase ⟨h1, Ne.symm hrne⟩

private theorem separates_symm' {S : Set V} {a b : V} (h : G.Separates S a b) :
    G.Separates S b a :=
  ⟨h.2.1, h.1, fun hr => h.2.2 (avoid_symm hr)⟩

private theorem eq_of_subset_of_separates {S W : Set V} {a b : V}
    (hmin : ∀ W' ⊂ S, ¬ G.Separates W' a b) (hsub : W ⊆ S) (hsep : G.Separates W a b) : S = W := by
  by_contra hne
  exact hmin W (LE.le.ssubset_of_ne hsub fun h => hne h.symm) hsep

/-- **Every minimal separator of a clique tree is the intersection of two adjacent bags.**

No maximality of the bags is needed here.  The hypothesis that `a` and `b` are joined by a walk
cannot be dropped: in a disconnected graph the empty set is a minimal separator of two vertices of
different components, while the clique forest may have no tree edge at all. -/
theorem exists_parent_eq_of_isMinimalSeparator [Finite V] [DecidableEq V] (T : CliqueTree G ι)
    {S : Set V} {a b : V}
    (hS : G.IsMinimalSeparator S a b) (hreach : G.Reachable a b) :
    ∃ i j, T.parent i = some j ∧ S = ((T.bag i ∩ T.bag j : Finset V) : Set V) := by
  classical
  obtain ⟨⟨haS, hbS, hnr⟩, hmin⟩ := hS
  obtain ⟨vA, hvA, hminA⟩ := exists_min_top T S a
  obtain ⟨vB, hvB, hminB⟩ := exists_min_top T S b
  have htopA : ∀ x, Avoid G S a x → T.IsAncestor (T.top x) (T.top vA) := fun x hx =>
    isAncestor_top_root T (fun y hy => hminA y ((avoid_iff_of_avoid hvA).2 hy)) x
      ((avoid_iff_of_avoid hvA).1 hx)
  have htopB : ∀ x, Avoid G S b x → T.IsAncestor (T.top x) (T.top vB) := fun x hx =>
    isAncestor_top_root T (fun y hy => hminB y ((avoid_iff_of_avoid hvB).2 hy)) x
      ((avoid_iff_of_avoid hvB).1 hx)
  have hbetA : ∀ x, Avoid G S a x → ∀ m, T.IsAncestor (T.top x) m → T.IsAncestor m (T.top vA) →
      ∃ w, Avoid G S a w ∧ w ∈ T.bag m := by
    intro x hx m h1 h2
    obtain ⟨w, hw, hwm⟩ := exists_mem_bag_between T x ((avoid_iff_of_avoid hvA).1 hx) m h1 h2
    exact ⟨w, (avoid_iff_of_avoid hvA).2 hw, hwm⟩
  have hbetB : ∀ x, Avoid G S b x → ∀ m, T.IsAncestor (T.top x) m → T.IsAncestor m (T.top vB) →
      ∃ w, Avoid G S b w ∧ w ∈ T.bag m := by
    intro x hx m h1 h2
    obtain ⟨w, hw, hwm⟩ := exists_mem_bag_between T x ((avoid_iff_of_avoid hvB).1 hx) m h1 h2
    exact ⟨w, (avoid_iff_of_avoid hvB).2 hw, hwm⟩
  have hbags : ∀ (k : ι) (u w : V), u ∈ T.bag k → w ∈ T.bag k → Avoid G S a u → Avoid G S b w →
      False := by
    intro k u w hu hw hau hbw
    have hne : u ≠ w := by
      rintro rfl
      exact hnr (avoid_trans hau (avoid_symm hbw))
    have hadj : G.Adj u w := T.bag_isClique k (by simpa using hu) (by simpa using hw) hne
    exact hnr (avoid_trans (avoid_trans hau
      (avoid_step (avoid_notMem haS hau) (avoid_notMem hbS hbw) hadj)) (avoid_symm hbw))
  -- the top nodes of the two sides lie in the same tree of the forest
  have hcommon : ∃ w, T.IsAncestor (T.top vA) w ∧ T.IsAncestor (T.top vB) w := by
    obtain ⟨w, hAw, hBw⟩ := exists_common_ancestor_of_reachable T hreach
    rcases (htopA a (avoid_refl a)).comparable hAw with hc1 | hc1 <;>
      rcases (htopB b (avoid_refl b)).comparable hBw with hc2 | hc2
    · exact ⟨w, hc1, hc2⟩
    · exact ⟨T.top vB, hc1.trans hc2, isAncestor_refl _⟩
    · exact ⟨T.top vA, isAncestor_refl _, hc2.trans hc1⟩
    · rcases hc1.comparable hc2 with h | h
      · exact ⟨T.top vB, h, isAncestor_refl _⟩
      · exact ⟨T.top vA, isAncestor_refl _, h⟩
  by_cases hcase : T.IsAncestor (T.top vB) (T.top vA) ∧ T.top vB ≠ T.top vA
  · -- the `b` side carries the tree edge
    obtain ⟨i, j, hp, hsub, hbbr, habr⟩ :=
      exists_sep_edge T (fun k u w hu hw h1 h2 => hbags k w u hw hu h2 h1) hbS hvB hvA htopB htopA
        hbetA (fun hcon => hcase.2 (hcase.1.antisymm hcon.1))
        (by obtain ⟨w, h1, h2⟩ := hcommon; exact ⟨w, h2, h1⟩)
    refine ⟨i, j, hp, eq_of_subset_of_separates hmin hsub (separates_symm' ?_)⟩
    exact separates_bag_inter hp hbbr habr (fun h => hbS (hsub (by simpa using h)))
      (fun h => haS (hsub (by simpa using h)))
  · -- the `a` side carries the tree edge
    obtain ⟨i, j, hp, hsub, habr, hbbr⟩ :=
      exists_sep_edge T hbags haS hvA hvB htopA htopB hbetB hcase hcommon
    refine ⟨i, j, hp, eq_of_subset_of_separates hmin hsub ?_⟩
    exact separates_bag_inter hp habr hbbr (fun h => haS (hsub (by simpa using h)))
      (fun h => hbS (hsub (by simpa using h)))

end Converse

/-! ### The maximality and injectivity hypotheses are needed

The direct statement fails for a clique tree whose bags are maximal cliques but are allowed to
repeat: below, a one-vertex graph is given a two-node clique tree with the same bag twice, so the
separator of its unique tree edge is the whole vertex set and separates nothing. -/

/-- A clique tree of the one-vertex graph with two nodes carrying the same (maximal) bag. -/
def dupBagTree : CliqueTree (⊥ : SimpleGraph Unit) Bool where
  bag := fun _ => {()}
  parent := fun i => if i then some false else none
  rank := fun i => if i then 1 else 0
  top := fun _ => false
  rank_injective := by decide
  rank_parent_lt := by decide
  bag_isClique := by
    intro i
    simp
  mem_bag_top := by simp
  exists_bag_of_adj := by
    intro u v h
    simp at h
  mem_bag_parent := by
    intro i v hv hne
    refine ⟨false, ?_, by simp⟩
    cases i
    · simp at hne
    · simp

/-- **Injectivity of the bags cannot be dropped from `isMinimalSeparator_bag_inter`.** All the bags
of `dupBagTree` are maximal cliques, but the separator of its tree edge is the whole vertex set,
hence separates no pair of vertices. -/
theorem not_exists_isMinimalSeparator_dupBagTree :
    (∀ i, (⊥ : SimpleGraph Unit).IsMaximalCliqueOn Finset.univ (dupBagTree.bag i)) ∧
      dupBagTree.parent true = some false ∧
      ¬ ∃ a b, (⊥ : SimpleGraph Unit).IsMinimalSeparator
        ((dupBagTree.bag true ∩ dupBagTree.bag false : Finset Unit) : Set Unit) a b := by
  refine ⟨fun i => ⟨Finset.subset_univ _, by simp [dupBagTree],
    ?_⟩, by simp [dupBagTree], ?_⟩
  · intro K' hK' _ hsub
    refine Finset.Subset.antisymm ?_ hsub
    intro x hx
    cases x
    simp [dupBagTree]
  · rintro ⟨a, b, ⟨ha, -, -⟩, -⟩
    exact ha (by cases a; simp [dupBagTree])

/-! ### Connectivity is needed in the converse

In a disconnected graph the empty set is a minimal separator of two vertices of distinct
components, while a clique *forest* need not have any tree edge at all. -/

/-- Two isolated vertices, each in its own bag, with no tree edge. -/
def isolatedTree : CliqueTree (⊥ : SimpleGraph Bool) Bool where
  bag := fun i => {i}
  parent := fun _ => none
  rank := fun i => if i then 1 else 0
  top := id
  rank_injective := by decide
  rank_parent_lt := by decide
  bag_isClique := by
    intro i
    simp
  mem_bag_top := by simp
  exists_bag_of_adj := by
    intro u v h
    simp at h
  mem_bag_parent := by
    intro i v hv hne
    simp only [Finset.mem_singleton] at hv
    exact absurd (by simp [hv] : i = id v) hne

/-- **The walk hypothesis cannot be dropped from `exists_parent_eq_of_isMinimalSeparator`.** All
the bags of `isolatedTree` are maximal cliques and `∅` is a minimal separator of its two vertices,
but the forest has no tree edge. -/
theorem not_exists_parent_eq_isolatedTree :
    (∀ i, (⊥ : SimpleGraph Bool).IsMaximalCliqueOn Finset.univ (isolatedTree.bag i)) ∧
      (⊥ : SimpleGraph Bool).IsMinimalSeparator (∅ : Set Bool) true false ∧
      ¬ ∃ i j, isolatedTree.parent i = some j ∧
        (∅ : Set Bool) = ((isolatedTree.bag i ∩ isolatedTree.bag j : Finset Bool) : Set Bool) := by
  refine ⟨fun i => ⟨Finset.subset_univ _, by simp [isolatedTree],
      ?_⟩,
    ⟨⟨by simp, by simp, ?_⟩, fun W hW => absurd (Set.empty_subset W) hW.2⟩,
    by rintro ⟨i, j, h, -⟩; simp [isolatedTree] at h⟩
  · intro K' _ hclique hsub
    refine Finset.Subset.antisymm ?_ hsub
    intro x hx
    simp only [isolatedTree, Finset.mem_singleton]
    by_contra hne
    have hadj : (⊥ : SimpleGraph Bool).Adj x i := hclique (by simpa using hx)
      (by simpa using hsub (by simp [isolatedTree])) hne
    simp at hadj
  · intro h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hc, -⟩
    · simp at heq
    · simp at hc

end CliqueTree

end SimpleGraph
